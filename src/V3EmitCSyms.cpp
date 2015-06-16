// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2015 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <cmath>
#include <map>
#include <set>
#include <vector>
#include <algorithm>

#include "V3Global.h"
#include "V3EmitC.h"
#include "V3EmitCBase.h"
#include "V3LanguageWords.h"

//######################################################################
// Symbol table emitting

class EmitCSyms : EmitCBaseVisitor {
    // NODE STATE
    // Cleared on Netlist
    //  AstNodeModule::user1()	-> bool.  Set true __Vconfigure called
    AstUser1InUse	m_inuser1;

    // TYPES
    struct ScopeNameData { string m_symName; string m_prettyName;
	ScopeNameData(const string& symName, const string& prettyName)
	    : m_symName(symName), m_prettyName(prettyName) {}
    };
    struct ScopeFuncData { AstScopeName* m_scopep; AstCFunc* m_funcp; AstNodeModule* m_modp;
	ScopeFuncData(AstScopeName* scopep, AstCFunc* funcp, AstNodeModule* modp)
	    : m_scopep(scopep), m_funcp(funcp), m_modp(modp) {}
    };
    struct ScopeVarData { string m_scopeName; string m_varBasePretty; AstVar* m_varp;
	AstNodeModule* m_modp;  AstScope* m_scopep;
	ScopeVarData(const string& scopeName, const string& varBasePretty, AstVar* varp, AstNodeModule* modp, AstScope* scopep)
	    : m_scopeName(scopeName), m_varBasePretty(varBasePretty), m_varp(varp), m_modp(modp), m_scopep(scopep) {}
    };
    typedef map<string,ScopeFuncData> ScopeFuncs;
    typedef map<string,ScopeVarData> ScopeVars;
    typedef map<string,ScopeNameData> ScopeNames;
    typedef pair<AstScope*,AstNodeModule*> ScopeModPair;
    typedef pair<AstNodeModule*,AstVar*> ModVarPair;
    struct CmpName {
	inline bool operator () (const ScopeModPair& lhsp, const ScopeModPair& rhsp) const {
	    return lhsp.first->name() < rhsp.first->name();
	}
    };
    struct CmpDpi {
	inline bool operator () (const AstCFunc* lhsp, const AstCFunc* rhsp) const {
	    if (lhsp->dpiImport() != rhsp->dpiImport()) {
		// cppcheck-suppress comparisonOfFuncReturningBoolError
		return lhsp->dpiImport() < rhsp->dpiImport();
	    }
	    return lhsp->name() < rhsp->name();
	}
    };

    // STATE
    AstCFunc*		m_funcp;	// Current function
    AstNodeModule*	m_modp;		// Current module
    vector<ScopeModPair>  m_scopes;	// Every scope by module
    vector<AstCFunc*>	m_dpis;		// DPI functions
    vector<ModVarPair>	m_modVars;	// Each public {mod,var}
    ScopeNames		m_scopeNames;	// Each unique AstScopeName
    ScopeFuncs		m_scopeFuncs;	// Each {scope,dpi-export-func}
    ScopeVars		m_scopeVars;	// Each {scope,public-var}
    V3LanguageWords 	m_words;	// Reserved word detector
    int		m_coverBins;		// Coverage bin number
    int		m_labelNum;		// Next label number

    // METHODS
    void emitSymHdr();
    void emitSymImp();
    void emitDpiHdr();
    void emitDpiImp();

    void nameCheck(AstNode* nodep) {
	// Prevent GCC compile time error; name check all things that reach C++ code
	if (nodep->name() != "") {
	    string rsvd = m_words.isKeyword(nodep->name());
	    if (rsvd != "") {
		// Generally V3Name should find all of these and throw SYMRSVDWORD.
		// We'll still check here because the compiler errors resulting if we miss this warning are SO nasty
		nodep->v3error("Symbol matching "+rsvd+" reserved word reached emitter, should have hit SYMRSVDWORD: '"<<nodep->prettyName()<<"'");
	    }
	}
    }

    void varsExpand() {
	// We didn'e have all m_scopes loaded when we encountered variables, so expand them now
	// It would be less code if each module inserted its own variables.
	// Someday.  For now public isn't common.
	for (vector<ScopeModPair>::iterator it = m_scopes.begin(); it != m_scopes.end(); ++it) {
	    AstScope* scopep = it->first;  AstNodeModule* smodp = it->second;
	    for (vector<ModVarPair>::iterator it = m_modVars.begin(); it != m_modVars.end(); ++it) {
		AstNodeModule* modp = it->first;
		AstVar* varp = it->second;
		if (modp == smodp) {
		    // Need to split the module + var name into the original-ish full scope and variable name under that scope.
		    // The module instance name is included later, when we know the scopes this module is under
		    string whole = scopep->name()+"__DOT__"+varp->name();
		    string scpName;
		    string varBase;
		    if (whole.substr(0,10) == "__DOT__TOP") whole.replace(0,10,"");
		    string::size_type pos = whole.rfind("__DOT__");
		    if (pos != string::npos) {
			scpName = whole.substr(0,pos);
			varBase = whole.substr(pos+strlen("__DOT__"));
		    } else {
			varBase = whole;
		    }
		    //UINFO(9,"For "<<scopep->name()<<" - "<<varp->name()<<"  Scp "<<scpName<<"  Var "<<varBase<<endl);
		    string varBasePretty = AstNode::prettyName(varBase);
		    string scpPretty = AstNode::prettyName(scpName);
		    string scpSym;
		    {
			string out = scpName;
			string::size_type pos;
			while ((pos=out.find("__PVT__")) != string::npos) {
			    out.replace(pos, 7, "");
			}
			if (out.substr(0,10) == "TOP__DOT__") out.replace(0,10,"");
			if (out.substr(0,4) == "TOP.") out.replace(0,4,"");
			while ((pos=out.find(".")) != string::npos) {
			    out.replace(pos, 1, "__");
			}
			while ((pos=out.find("__DOT__")) != string::npos) {
			    out.replace(pos, 7, "__");
			}
			scpSym = out;
		    }
		    //UINFO(9," scnameins sp "<<scpName<<" sp "<<scpPretty<<" ss "<<scpSym<<endl);
		    if (m_scopeNames.find(scpSym) == m_scopeNames.end()) {
			m_scopeNames.insert(make_pair(scpSym, ScopeNameData(scpSym, scpPretty)));
		    }
		    m_scopeVars.insert(make_pair(scpSym + " " + varp->name(),
						 ScopeVarData(scpSym, varBasePretty, varp, modp, scopep)));
		}
	    }
	}
    }

    // VISITORS
    virtual void visit(AstNetlist* nodep, AstNUser*) {
	// Collect list of scopes
	nodep->iterateChildren(*this);
	varsExpand();

	// Sort by names, so line/process order matters less
	stable_sort(m_scopes.begin(), m_scopes.end(), CmpName());
	stable_sort(m_dpis.begin(), m_dpis.end(), CmpDpi());

	// Output
	emitSymHdr();
	emitSymImp();
	if (v3Global.dpi()) {
	    emitDpiHdr();
	    emitDpiImp();
	}
    }
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	nameCheck(nodep);
	m_modp = nodep;
	m_labelNum = 0;
	nodep->iterateChildren(*this);
	m_modp = NULL;
    }
    virtual void visit(AstScope* nodep, AstNUser*) {
	nameCheck(nodep);
	m_scopes.push_back(make_pair(nodep, m_modp));
    }
    virtual void visit(AstScopeName* nodep, AstNUser*) {
	string name = nodep->scopeSymName();
	//UINFO(9,"scnameins sp "<<nodep->name()<<" sp "<<nodep->scopePrettySymName()<<" ss "<<name<<endl);
	if (m_scopeNames.find(name) == m_scopeNames.end()) {
	    m_scopeNames.insert(make_pair(name, ScopeNameData(name, nodep->scopePrettySymName())));
	}
	if (nodep->dpiExport()) {
	    if (!m_funcp) nodep->v3fatalSrc("ScopeName not under DPI function");
	    m_scopeFuncs.insert(make_pair(name + " " + m_funcp->name(),
					  ScopeFuncData(nodep, m_funcp, m_modp)));
	} else {
	    if (m_scopeNames.find(nodep->scopeDpiName()) == m_scopeNames.end()) {
		m_scopeNames.insert(make_pair(nodep->scopeDpiName(), ScopeNameData(nodep->scopeDpiName(), nodep->scopePrettyDpiName())));
	    }
	}
    }
    virtual void visit(AstVar* nodep, AstNUser*) {
	nameCheck(nodep);
	nodep->iterateChildren(*this);
	if (nodep->isSigUserRdPublic()
	    && !nodep->isParam()) {  // The VPI functions require a pointer to allow modification, but parameters are constants
	    m_modVars.push_back(make_pair(m_modp, nodep));
	}
    }
    virtual void visit(AstCoverDecl* nodep, AstNUser*) {
	// Assign numbers to all bins, so we know how big of an array to use
	if (!nodep->dataDeclNullp()) {  // else duplicate we don't need code for
	    nodep->binNum(m_coverBins++);
	}
    }
    virtual void visit(AstJumpLabel* nodep, AstNUser*) {
	nodep->labelNum(++m_labelNum);
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstCFunc* nodep, AstNUser*) {
	nameCheck(nodep);
	if (nodep->dpiImport() || nodep->dpiExportWrapper()) {
	    m_dpis.push_back(nodep);
	}
	m_funcp = nodep;
	nodep->iterateChildren(*this);
	m_funcp = NULL;
    }
    // NOPs
    virtual void visit(AstConst*, AstNUser*) {}
    // Default
    virtual void visit(AstNode* nodep, AstNUser*) {
	nameCheck(nodep);
	nodep->iterateChildren(*this);
    }
    //---------------------------------------
    // ACCESSORS
public:
    EmitCSyms(AstNetlist* nodep) {
	m_funcp = NULL;
	m_modp = NULL;
	m_coverBins = 0;
	m_labelNum = 0;
	nodep->accept(*this);
    }
};

void EmitCSyms::emitSymHdr() {
    UINFO(6,__FUNCTION__<<": "<<endl);
    string filename = v3Global.opt.makeDir()+"/"+symClassName()+".h";
    newCFile(filename, true/*slow*/, false/*source*/);
    V3OutCFile hf (filename);
    m_ofp = &hf;

    ofp()->putsHeader();
    puts("// DESCR" "IPTION: Verilator output: Symbol table internal header\n");
    puts("//\n");
    puts("// Internal details; most calling programs do not need this header\n");
    puts("\n");

    puts("#ifndef _"+symClassName()+"_H_\n");
    puts("#define _"+symClassName()+"_H_\n");
    puts("\n");

    if (optSystemPerl()) puts("#include \"systemperl.h\"\n");
    else if (optSystemC()) puts("#include \"systemc.h\"\n");

    if (optSystemPerl() || optSystemC()) {
	puts("#include \"verilated_sc.h\"\n");
    }
    if (v3Global.needHeavy()) {
	puts("#include \"verilated_heavy.h\"\n");
    } else {
	puts("#include \"verilated.h\"\n");
    }

    // for
    puts("\n// INCLUDE MODULE CLASSES\n");
    for (AstNodeModule* nodep = v3Global.rootp()->modulesp(); nodep; nodep=nodep->nextp()->castNodeModule()) {
	puts("#include \""+modClassName(nodep)+".h\"\n");
    }

    if (v3Global.dpi()) {
	puts ("\n// DPI TYPES for DPI Export callbacks (Internal use)\n");
	map<string,int> types;  // Remove duplicates and sort
	for (ScopeFuncs::iterator it = m_scopeFuncs.begin(); it != m_scopeFuncs.end(); ++it) {
	    AstCFunc* funcp = it->second.m_funcp;
	    if (funcp->dpiExport()) {
		string cbtype = v3Global.opt.prefix()+"__Vcb_"+funcp->cname()+"_t";
		types["typedef void (*"+cbtype+") ("+cFuncArgs(funcp)+");\n"] = 1;
	    }
	}
	for (map<string,int>::iterator it = types.begin(); it != types.end(); ++it) {
	    puts(it->first);
	}
    }

    puts("\n// SYMS CLASS\n");
    puts((string)"class "+symClassName()+" : public VerilatedSyms {\n");
    ofp()->putsPrivate(false);  // public:

    puts("\n// LOCAL STATE\n");
    ofp()->putAlign(V3OutFile::AL_AUTO, sizeof(vluint64_t));
    puts("const char* __Vm_namep;\n");	// Must be before subcells, as constructor order needed before _vlCoverInsert.
    ofp()->putAlign(V3OutFile::AL_AUTO, sizeof(bool));
    puts("bool\t__Vm_activity;\t\t///< Used by trace routines to determine change occurred\n");
    ofp()->putAlign(V3OutFile::AL_AUTO, sizeof(bool));
    puts("bool\t__Vm_didInit;\n");

    ofp()->putAlign(V3OutFile::AL_AUTO, sizeof(vluint64_t));
    puts("\n// SUBCELL STATE\n");
    for (vector<ScopeModPair>::iterator it = m_scopes.begin(); it != m_scopes.end(); ++it) {
	AstScope* scopep = it->first;  AstNodeModule* modp = it->second;
	if (modp->isTop()) {
	    ofp()->printf("%-30s ", (modClassName(modp)+"*").c_str());
	    puts(scopep->nameDotless()+"p;\n");
	}
	else {
	    ofp()->printf("%-30s ", (modClassName(modp)+"").c_str());
	    puts(scopep->nameDotless()+";\n");
	}
    }

    puts("\n// COVERAGE\n");
    if (m_coverBins) {
	ofp()->putAlign(V3OutFile::AL_AUTO, sizeof(uint32_t));
	puts("uint32_t\t__Vcoverage["); puts(cvtToStr(m_coverBins)); puts("];\n");
    }

    puts("\n// SCOPE NAMES\n");
    for (ScopeNames::iterator it = m_scopeNames.begin(); it != m_scopeNames.end(); ++it) {
	puts("VerilatedScope __Vscope_"+it->second.m_symName+";\n");
    }

    puts("\n// CREATORS\n");
    puts(symClassName()+"("+topClassName()+"* topp, const char* namep);\n");
    puts((string)"~"+symClassName()+"() {};\n");

    puts("\n// METHODS\n");
    puts("inline const char* name() { return __Vm_namep; }\n");
    puts("inline bool getClearActivity() { bool r=__Vm_activity; __Vm_activity=false; return r;}\n");
    if (v3Global.opt.savable() ) {
	puts("void __Vserialize(VerilatedSerialize& os);\n");
	puts("void __Vdeserialize(VerilatedDeserialize& os);\n");
    }
    puts("\n");
    puts("} VL_ATTR_ALIGNED(64);\n");
    puts("\n");
    puts("#endif  /*guard*/\n");
}

void EmitCSyms::emitSymImp() {
    UINFO(6,__FUNCTION__<<": "<<endl);
    string filename = v3Global.opt.makeDir()+"/"+symClassName()+".cpp";
    AstCFile* cfilep = newCFile(filename, true/*slow*/, true/*source*/);
    cfilep->support(true);
    V3OutCFile cf (filename);
    m_ofp = &cf;
    ofp()->putsHeader();
    puts("// DESCR" "IPTION: Verilator output: Symbol table implementation internals\n");
    puts("\n");

    // Includes
    puts("#include \""+symClassName()+".h\"\n");
    for (AstNodeModule* nodep = v3Global.rootp()->modulesp(); nodep; nodep=nodep->nextp()->castNodeModule()) {
	puts("#include \""+modClassName(nodep)+".h\"\n");
    }

    //puts("\n// GLOBALS\n");

    puts("\n// FUNCTIONS\n");
    puts(symClassName()+"::"+symClassName()+"("+topClassName()+"* topp, const char* namep)\n");
    puts("\t// Setup locals\n");
    puts("\t: __Vm_namep(namep)\n");	// No leak, as we get destroyed when the top is destroyed
    puts("\t, __Vm_activity(false)\n");
    puts("\t, __Vm_didInit(false)\n");
    puts("\t// Setup submodule names\n");
    char comma=',';
    for (vector<ScopeModPair>::iterator it = m_scopes.begin(); it != m_scopes.end(); ++it) {
	AstScope* scopep = it->first;  AstNodeModule* modp = it->second;
	if (modp->isTop()) {
	} else {
	    string nameDl = scopep->nameDotless();
	    ofp()->printf("\t%c %-30s ", comma, nameDl.c_str());
	    puts("(Verilated::catName(topp->name(),");
	    // The "." is added by catName
	    putsQuoted(scopep->prettyName());
	    puts("))\n");
	    comma=',';
	}
    }
    puts("{\n");

    puts("// Pointer to top level\n");
    puts("TOPp = topp;\n");
    puts("// Setup each module's pointers to their submodules\n");
    for (vector<ScopeModPair>::iterator it = m_scopes.begin(); it != m_scopes.end(); ++it) {
	AstScope* scopep = it->first;  AstNodeModule* modp = it->second;
	if (!modp->isTop()) {
	    string arrow = scopep->name();
	    string::size_type pos;
	    while ((pos=arrow.find(".")) != string::npos) {
		arrow.replace(pos, 1, "->");
	    }
	    if (arrow.substr(0,5) == "TOP->") arrow.replace(0,5,"TOPp->");
	    ofp()->printf("%-30s ", arrow.c_str());
	    puts(" = &");
	    puts(scopep->nameDotless()+";\n");
	}
    }

    puts("// Setup each module's pointer back to symbol table (for public functions)\n");
    puts("TOPp->__Vconfigure(this, true);\n");
    for (vector<ScopeModPair>::iterator it = m_scopes.begin(); it != m_scopes.end(); ++it) {
	AstScope* scopep = it->first;  AstNodeModule* modp = it->second;
	if (!modp->isTop()) {
	    // first is used by AstCoverDecl's call to __vlCoverInsert
	    bool first = !modp->user1();
	    modp->user1(true);
	    puts(scopep->nameDotless()+".__Vconfigure(this, "
		 +(first?"true":"false")
		 +");\n");
	}
    }

    puts("// Setup scope names\n");
    for (ScopeNames::iterator it = m_scopeNames.begin(); it != m_scopeNames.end(); ++it) {
	puts("__Vscope_"+it->second.m_symName+".configure(this,name(),");
	putsQuoted(it->second.m_prettyName);
	puts(");\n");
    }

    if (v3Global.dpi()) {
	puts("// Setup export functions\n");
	puts("for (int __Vfinal=0; __Vfinal<2; __Vfinal++) {\n");
	for (ScopeFuncs::iterator it = m_scopeFuncs.begin(); it != m_scopeFuncs.end(); ++it) {
	    AstScopeName* scopep = it->second.m_scopep;
	    AstCFunc* funcp = it->second.m_funcp;
	    AstNodeModule* modp = it->second.m_modp;
	    if (funcp->dpiExport()) {
		puts("__Vscope_"+scopep->scopeSymName()+".exportInsert(__Vfinal,");
		putsQuoted(funcp->cname());
		puts(", (void*)(&");
		puts(modClassName(modp));
		puts("::");
		puts(funcp->name());
		puts("));\n");
	    }
	}
	// It would be less code if each module inserted its own variables.
	// Someday.  For now public isn't common.
	for (ScopeVars::iterator it = m_scopeVars.begin(); it != m_scopeVars.end(); ++it) {
	    AstNodeModule* modp = it->second.m_modp;
	    AstScope* scopep = it->second.m_scopep;
	    AstVar* varp = it->second.m_varp;
	    //
	    int pdim=0;
	    int udim=0;
	    string bounds;
	    if (AstBasicDType* basicp = varp->basicp()) {
		// Range is always first, it's not in "C" order
		if (basicp->isRanged()) {
		    bounds += " ,"; bounds += cvtToStr(basicp->msb());
		    bounds += ","; bounds += cvtToStr(basicp->lsb());
		    pdim++;
		}
		for (AstNodeDType* dtypep=varp->dtypep(); dtypep; ) {
		    dtypep = dtypep->skipRefp();  // Skip AstRefDType/AstTypedef, or return same node
		    if (AstNodeArrayDType* adtypep = dtypep->castNodeArrayDType()) {
			bounds += " ,"; bounds += cvtToStr(adtypep->msb());
			bounds += ","; bounds += cvtToStr(adtypep->lsb());
			if (dtypep->castPackArrayDType()) pdim++; else udim++;
			dtypep = adtypep->subDTypep();
		    }
		    else break; // AstBasicDType - nothing below, 1
		}
	    }
	    //
	    if (pdim>1 || udim>1) {
		puts("//UNSUP ");  // VerilatedImp can't deal with >2d or packed arrays
	    }
	    puts("__Vscope_"+it->second.m_scopeName+".varInsert(__Vfinal,");
	    putsQuoted(it->second.m_varBasePretty);
	    puts(", &(");
	    if (modp->isTop()) {
		puts(scopep->nameDotless());
		puts("p->");
	    } else {
		puts(scopep->nameDotless());
		puts(".");
	    }
	    puts(varp->name());
	    puts("), ");
	    puts(varp->vlEnumType());  // VLVT_UINT32 etc
	    puts(",");
	    puts(varp->vlEnumDir());  // VLVD_IN etc
	    if (varp->isSigUserRWPublic()) puts("|VLVF_PUB_RW");
	    else if (varp->isSigUserRdPublic()) puts("|VLVF_PUB_RD");
	    puts(",");
	    puts(cvtToStr(pdim+udim));
	    puts(bounds);
	    puts(");\n");
	}
	puts("}\n");
    }

    puts("}\n");

    if (v3Global.opt.savable() ) {
	puts("\n");
	for (int de=0; de<2; ++de) {
	    string classname = de ? "VerilatedDeserialize" : "VerilatedSerialize";
	    string funcname = de ? "__Vdeserialize" : "__Vserialize";
	    string op = de ? ">>" : "<<";
	    puts("void "+symClassName()+"::"+funcname+"("+classname+"& os) {\n");
	    puts(   "// LOCAL STATE\n");
	    // __Vm_namep presumably already correct
	    puts(   "os"+op+"__Vm_activity;\n");
	    puts(   "os"+op+"__Vm_didInit;\n");
	    puts(   "// SUBCELL STATE\n");
	    for (vector<ScopeModPair>::iterator it = m_scopes.begin(); it != m_scopes.end(); ++it) {
		AstScope* scopep = it->first;  AstNodeModule* modp = it->second;
		if (!modp->isTop()) {
		    puts(   scopep->nameDotless()+"."+funcname+"(os);\n");
		}
	    }
	    puts("}\n");
	}
    }
}

//######################################################################

void EmitCSyms::emitDpiHdr() {
    UINFO(6,__FUNCTION__<<": "<<endl);
    string filename = v3Global.opt.makeDir()+"/"+topClassName()+"__Dpi.h";
    AstCFile* cfilep = newCFile(filename, false/*slow*/, false/*source*/);
    cfilep->support(true);
    V3OutCFile hf (filename);
    m_ofp = &hf;

    m_ofp->putsHeader();
    puts("// DESCR" "IPTION: Verilator output: Prototypes for DPI import and export functions.\n");
    puts("//\n");
    puts("// Verilator includes this file in all generated .cpp files that use DPI functions.\n");
    puts("// Manually include this file where DPI .c import functions are declared to insure\n");
    puts("// the C functions match the expectations of the DPI imports.\n");
    puts("\n");
    puts("#include \"svdpi.h\"\n");
    puts("\n");
    puts("#ifdef __cplusplus\n");
    puts("extern \"C\" {\n");
    puts("#endif\n");
    puts("\n");

    int firstExp = 0;
    int firstImp = 0;
    for (vector<AstCFunc*>::iterator it = m_dpis.begin(); it != m_dpis.end(); ++it) {
	AstCFunc* nodep = *it;
	if (nodep->dpiExportWrapper()) {
	    if (!firstExp++) puts("\n// DPI EXPORTS\n");
	    puts("// DPI Export at "+nodep->fileline()->ascii()+"\n");
	    puts("extern "+nodep->rtnTypeVoid()+" "+nodep->name()+" ("+cFuncArgs(nodep)+");\n");
	}
	else if (nodep->dpiImport()) {
	    if (!firstImp++) puts("\n// DPI IMPORTS\n");
	    puts("// DPI Import at "+nodep->fileline()->ascii()+"\n");
	    puts("extern "+nodep->rtnTypeVoid()+" "+nodep->name()+" ("+cFuncArgs(nodep)+");\n");
	}
    }

    puts("\n");
    puts("#ifdef __cplusplus\n");
    puts("}\n");
    puts("#endif\n");
}

//######################################################################

void EmitCSyms::emitDpiImp() {
    UINFO(6,__FUNCTION__<<": "<<endl);
    string filename = v3Global.opt.makeDir()+"/"+topClassName()+"__Dpi.cpp";
    AstCFile* cfilep = newCFile(filename, false/*slow*/, true/*source*/);
    cfilep->support(true);
    V3OutCFile hf (filename);
    m_ofp = &hf;

    m_ofp->putsHeader();
    puts("// DESCR" "IPTION: Verilator output: Implementation of DPI export functions.\n");
    puts("//\n");
    puts("// Verilator compiles this file in when DPI functions are used.\n");
    puts("// If you have multiple Verilated designs with the same DPI exported\n");
    puts("// function names, you will get multiple definition link errors from here.\n");
    puts("// This is an unfortunate result of the DPI specification.\n");
    puts("// To solve this, either\n");
    puts("//    1. Call "+topClassName()+"::{export_function} instead,\n");
    puts("//       and do not even bother to compile this file\n");
    puts("// or 2. Compile all __Dpi.cpp files in the same compiler run,\n");
    puts("//       and #ifdefs already inserted here will sort everything out.\n");
    puts("\n");

    puts("#include \""+topClassName()+"__Dpi.h\"\n");
    puts("#include \""+topClassName()+".h\"\n");
    puts("\n");

    for (vector<AstCFunc*>::iterator it = m_dpis.begin(); it != m_dpis.end(); ++it) {
	AstCFunc* nodep = *it;
	if (nodep->dpiExportWrapper()) {
	    puts("#ifndef _VL_DPIDECL_"+nodep->name()+"\n");
	    puts("#define _VL_DPIDECL_"+nodep->name()+"\n");
	    puts(nodep->rtnTypeVoid()+" "+nodep->name()+" ("+cFuncArgs(nodep)+") {\n");
	    puts("// DPI Export at "+nodep->fileline()->ascii()+"\n");
	    puts("return "+topClassName()+"::"+nodep->name()+"(");
	    string args;
	    for (AstNode* stmtp = nodep->argsp(); stmtp; stmtp=stmtp->nextp()) {
		if (AstVar* portp = stmtp->castVar()) {
		    if (portp->isIO() && !portp->isFuncReturn()) {
			if (args != "") args+= ", ";
			args += portp->name();
		    }
		}
	    }
	    puts(args+");\n");
	    puts("}\n");
	    puts("#endif\n");
	    puts("\n");
	}
    }
}

//######################################################################
// EmitC class functions

void V3EmitC::emitcSyms() {
    UINFO(2,__FUNCTION__<<": "<<endl);
    EmitCSyms syms (v3Global.rootp());
}
