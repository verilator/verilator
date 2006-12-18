// $Id$
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
//
// Code available from: http://www.veripool.com/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2006 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <stdio.h>
#include <stdarg.h>
#include <unistd.h>
#include <math.h>
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
    // STATE
    AstModule*	m_modp;		// Current module
    typedef pair<AstScope*,AstModule*> ScopeModPair;
    vector<ScopeModPair>  m_scopes;	// Every scope by module
    V3LanguageWords 	m_words;	// Reserved word detector

    // METHODS
    void emitInt();
    void emitImp();
    struct CmpName {
	inline bool operator () (const ScopeModPair& lhsp, const ScopeModPair& rhsp) const {
	    return lhsp.first->name() < rhsp.first->name();
	}
    };

    void nameCheck(AstNode* nodep) {
	// Prevent GCC compile time error; name check all things that reach C++ code
	if (nodep->name() != "") {
	    string rsvd = m_words.isKeyword(nodep->name());
	    if (rsvd != "") {
		nodep->v3error("Unsupported: "+rsvd+": "<<nodep->name());
	    }
	}
    }

    // VISITORS
    virtual void visit(AstNetlist* nodep, AstNUser*) {
	// Collect list of scopes
	nodep->iterateChildren(*this);
	
	// Sort m_scopes by scope name
	sort(m_scopes.begin(), m_scopes.end(), CmpName());
	// Output
	emitInt();
	emitImp();
    }
    virtual void visit(AstModule* nodep, AstNUser*) {
	nameCheck(nodep);
	m_modp = nodep;
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstScope* nodep, AstNUser*) {
	nameCheck(nodep);
	m_scopes.push_back(make_pair(nodep, m_modp));
    }
    // NOPs
    virtual void visit(AstNodeStmt*, AstNUser*) {}
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
	m_modp = NULL;
	nodep->accept(*this);
    }
};

void EmitCSyms::emitInt() {
    string filename = v3Global.opt.makeDir()+"/"+symClassName()+".h";
    newCFile(filename, true/*slow*/, false/*source*/);
    V3OutCFile hf (filename);
    m_ofp = &hf;

    ofp()->putsHeader();
    puts("#ifndef _"+symClassName()+"_H_\n");
    puts("#define _"+symClassName()+"_H_\n");
    puts("\n");

    // for
    puts("\n// INCLUDE MODULE CLASSES\n");
    for (AstModule* nodep = v3Global.rootp()->modulesp(); nodep; nodep=nodep->nextp()->castModule()) {
	puts("#include \""+modClassName(nodep)+".h\"\n");
    }

    puts("\n// SYMS CLASS\n");
    puts((string)"class "+symClassName()+" {\n");
    ofp()->putsPrivate(false);  // public:

    //puts("\n// STATIC STATE\n");

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
	AstScope* scopep = it->first;  AstModule* modp = it->second;
	if (modp->isTop()) {
	    ofp()->printf("%-30s ", (modClassName(modp)+"*").c_str());
	    puts(scopep->nameDotless()+"p;\n");
	}
	else {
	    ofp()->printf("%-30s ", (modClassName(modp)+"").c_str());
	    puts(scopep->nameDotless()+";\n");
	}
    }

    puts("\n// CREATORS\n");
    puts(symClassName()+"("+topClassName()+"* topp, const char* namep);\n");
    puts((string)"~"+symClassName()+"() {};\n");

    puts("\n// METHODS\n");
    puts("inline const char* name() { return __Vm_namep; }\n");
    puts("inline bool getClearActivity() { bool r=__Vm_activity; __Vm_activity=false; return r;}\n");
    puts("\n");
    puts("} VL_ATTR_ALIGNED(64);\n");
    puts("#endif  /*guard*/\n");
}

void EmitCSyms::emitImp() {
    string filename = v3Global.opt.makeDir()+"/"+symClassName()+".cpp";
    AstCFile* cfilep = newCFile(filename, true/*slow*/, true/*source*/);
    cfilep->support(true);
    V3OutCFile cf (filename);
    m_ofp = &cf;
    ofp()->putsHeader();
    puts("\n");

    // Includes
    puts("#include \""+symClassName()+".h\"\n");
    for (AstModule* nodep = v3Global.rootp()->modulesp(); nodep; nodep=nodep->nextp()->castModule()) {
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
	AstScope* scopep = it->first;  AstModule* modp = it->second;
	if (modp->isTop()) {
	} else {
	    string arrow = scopep->name();
	    if (arrow.substr(0,4) == "TOP.") arrow.replace(0,4,".");
	    ofp()->printf("\t%c %-30s ", comma, scopep->nameDotless().c_str());
	    puts("(Verilated::catName(topp->name(),\"");
	    puts(arrow);
	    puts("\"))\n");
	    comma=',';
	}
    }
    puts("{\n");

    puts("// Pointer to top level\n");
    puts("TOPp = topp;\n");
    puts("// Setup each module's pointers to their submodules\n");
    for (vector<ScopeModPair>::iterator it = m_scopes.begin(); it != m_scopes.end(); ++it) {
	AstScope* scopep = it->first;  AstModule* modp = it->second;
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
    puts("TOPp->__Vconfigure(this);\n");
    for (vector<ScopeModPair>::iterator it = m_scopes.begin(); it != m_scopes.end(); ++it) {
	AstScope* scopep = it->first;  AstModule* modp = it->second;
	if (!modp->isTop()) {
	    puts(scopep->nameDotless()+".__Vconfigure(this);\n");
	}
    }

    puts("}\n");
    puts("\n");
}

//######################################################################
// EmitC class functions

void V3EmitC::emitcSyms() {
    UINFO(2,__FUNCTION__<<": "<<endl);
    EmitCSyms syms (v3Global.rootp());
}
