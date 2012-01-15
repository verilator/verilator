//*************************************************************************
// DESCRIPTION: Verilator: Check for unused/undriven signals
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2004-2012 by Wilson Snyder.  This program is free software; you can
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
// V3Undriven's Transformations:
//
// Each module:
//      Make vector for all variables
//	SEL(VARREF(...))) mark only some bits as used/driven
//	else VARREF(...) mark all bits as used/driven
//	Report unused/undriven nets
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <algorithm>
#include <vector>

#include "V3Global.h"
#include "V3Undriven.h"
#include "V3Ast.h"

//######################################################################
// Class for every variable we may process

class UndrivenVarEntry {
    // MEMBERS
    AstVar*		m_varp;		// Variable this tracks
    bool		m_usedWhole;	// True if whole vector used
    bool		m_drivenWhole;	// True if whole vector driven
    vector<bool>	m_flags;	// Used/Driven on each subbit

    enum { FLAG_USED = 0, FLAG_DRIVEN = 1, FLAGS_PER_BIT = 2 };

    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

public:
    // CONSTRUCTORS
    UndrivenVarEntry (AstVar* varp) {	// Construction for when a var is used
	UINFO(9, "create "<<varp<<endl);
	m_varp = varp;
	m_usedWhole = false;
	m_drivenWhole = false;

	m_flags.resize(varp->width()*FLAGS_PER_BIT);
	for (int i=0; i<varp->width()*FLAGS_PER_BIT; i++) {
	    m_flags[i] = false;
	}
    }
    ~UndrivenVarEntry() {}

private:
    // METHODS
    inline bool bitNumOk(int bit) const { return (bit*FLAGS_PER_BIT < (int)m_flags.size()); }
    inline bool usedFlag(int bit) const { return m_usedWhole || m_flags[bit*FLAGS_PER_BIT + FLAG_USED]; }
    inline bool drivenFlag(int bit) const { return m_drivenWhole || m_flags[bit*FLAGS_PER_BIT + FLAG_DRIVEN]; }
    enum BitNamesWhich { BN_UNUSED, BN_UNDRIVEN, BN_BOTH };
    string bitNames(BitNamesWhich which) {
	string bits="";
	bool prev = false;
	int msb = 0;
	// bit==-1 loops below; we do one extra iteration so end with prev=false
	for (int bit=(m_flags.size()/FLAGS_PER_BIT)-1; bit >= -1; --bit) {
	    if (bit>=0
		&& ((which == BN_UNUSED && !usedFlag(bit) && drivenFlag(bit))
		    || (which == BN_UNDRIVEN && usedFlag(bit) && !drivenFlag(bit))
		    || (which == BN_BOTH && !usedFlag(bit) && !drivenFlag(bit)))) {
		if (!prev) { prev=true; msb = bit; }
	    } else if (prev) {
		AstBasicDType* bdtypep = m_varp->basicp();
		int lsb = bit+1;
		if (bits != "") bits += ",";
		if (lsb==msb) {
		    bits += cvtToStr(lsb+bdtypep->lsb());
		} else {
		    if (bdtypep->littleEndian()) {
			bits += cvtToStr(lsb+bdtypep->lsb())+":"+cvtToStr(msb+bdtypep->lsb());
		    } else {
			bits += cvtToStr(msb+bdtypep->lsb())+":"+cvtToStr(lsb+bdtypep->lsb());
		    }
		}
		prev = false;
	    }
	}
	return "["+bits+"]";
    }
public:
    void usedWhole() {
	UINFO(9, "set u[*] "<<m_varp->name()<<endl);
	m_usedWhole = true;
    }
    void drivenWhole() {
	UINFO(9, "set d[*] "<<m_varp->name()<<endl);
	m_drivenWhole = true;
    }
    void usedBit (int bit, int width) {
	UINFO(9, "set u["<<(bit+width-1)<<":"<<bit<<"] "<<m_varp->name()<<endl);
	for (int i=0; i<width; i++) {
	    if (bitNumOk(bit+i)) {
		m_flags[(bit+i)*FLAGS_PER_BIT + FLAG_USED] = true;
	    }
	}
    }
    void drivenBit (int bit, int width) {
	UINFO(9, "set d["<<(bit+width-1)<<":"<<bit<<"] "<<m_varp->name()<<endl);
	for (int i=0; i<width; i++) {
	    if (bitNumOk(bit+i)) {
		m_flags[(bit+i)*FLAGS_PER_BIT + FLAG_DRIVEN] = true;
	    }
	}
    }
    bool unusedMatch(AstVar* nodep) {
	const char* regexpp = v3Global.opt.unusedRegexp().c_str();
	if (!regexpp || !*regexpp) return false;
	return V3Options::wildmatch(nodep->prettyName().c_str(), regexpp);
    }
    void reportViolations() {
	// Combine bits into overall state
	AstVar* nodep = m_varp;
	if (!nodep->isParam() && !nodep->isGenVar()) {
	    bool allU=true;
	    bool allD=true;
	    bool anyU=m_usedWhole;
	    bool anyD=m_drivenWhole;
	    bool anyUnotD=false;
	    bool anyDnotU=false;
	    bool anynotDU=false;
	    for (unsigned bit=0; bit<m_flags.size()/FLAGS_PER_BIT; bit++) {
		bool used = usedFlag(bit);
		bool driv = drivenFlag(bit);
		allU &= used;
		anyU |= used;
		allD &= driv;
		anyD |= driv;
		anyUnotD |= used && !driv;
		anyDnotU |= !used && driv;
		anynotDU |= !used && !driv;
	    }
	    if (allU) m_usedWhole = true;
	    if (allD) m_drivenWhole = true;
	    // Test results
	    if (allU && allD) {
		// It's fine
	    } else if (!anyD && !anyU) {
		// UNDRIVEN is considered more serious - as is more likely a bug,
		// thus undriven+unused bits get UNUSED warnings, as they're not as buggy.
		if (!unusedMatch(nodep)) {
		    nodep->v3warn(UNUSED, "Signal is not driven, nor used: "<<nodep->prettyName());
		    nodep->fileline()->modifyWarnOff(V3ErrorCode::UNUSED, true);  // Warn only once
		}
	    } else if (allD && !anyU) {
		if (!unusedMatch(nodep)) {
		    nodep->v3warn(UNUSED, "Signal is not used: "<<nodep->prettyName());
		    nodep->fileline()->modifyWarnOff(V3ErrorCode::UNUSED, true);  // Warn only once
		}
	    } else if (!anyD && allU) {
		nodep->v3warn(UNDRIVEN, "Signal is not driven: "<<nodep->prettyName());
		nodep->fileline()->modifyWarnOff(V3ErrorCode::UNDRIVEN, true);  // Warn only once
	    } else {
		// Bits have different dispositions
		bool setU=false; bool setD=false;
		if (anynotDU && !unusedMatch(nodep)) {
		    nodep->v3warn(UNUSED, "Bits of signal are not driven, nor used: "<<nodep->prettyName()
				  <<bitNames(BN_BOTH));
		    setU=true;
		}
		if (anyDnotU && !unusedMatch(nodep)) {
		    nodep->v3warn(UNUSED, "Bits of signal are not used: "<<nodep->prettyName()
				  <<bitNames(BN_UNUSED));
		    setU=true;
		}
		if (anyUnotD) {
		    nodep->v3warn(UNDRIVEN, "Bits of signal are not driven: "<<nodep->prettyName()
				  <<bitNames(BN_UNDRIVEN));
		    setD=true;
		}
		if (setU) nodep->fileline()->modifyWarnOff(V3ErrorCode::UNUSED, true);  // Warn only once
		if (setD) nodep->fileline()->modifyWarnOff(V3ErrorCode::UNDRIVEN, true);  // Warn only once
	    }
	}
    }
};

//######################################################################
// Undriven state, as a visitor of each AstNode

class UndrivenVisitor : public AstNVisitor {
private:
    // NODE STATE
    // AstVar::user1p		-> UndrivenVar* for usage var, 0=not set yet
    AstUser1InUse	m_inuser1;

    // STATE
    vector<UndrivenVarEntry*>	m_entryps;	// Nodes to delete when we are finished
    bool		m_markBoth;	// Mark as driven+used
    AstNodeFTask*	m_taskp;	// Current task

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    UndrivenVarEntry* getEntryp(AstVar* nodep) {
	if (!nodep->user1p()) {
	    UndrivenVarEntry* entryp = new UndrivenVarEntry (nodep);
	    m_entryps.push_back(entryp);
	    nodep->user1p(entryp);
	    return entryp;
	} else {
	    UndrivenVarEntry* entryp = (UndrivenVarEntry*)(nodep->user1p());
	    return entryp;
	}
    }

    // VISITORS
    virtual void visit(AstVar* nodep, AstNUser*) {
	UndrivenVarEntry* entryp = getEntryp (nodep);
	if (nodep->isInput()
	    || nodep->isSigPublic() || nodep->isSigUserRWPublic()
	    || (m_taskp && (m_taskp->dpiImport() || m_taskp->dpiExport()))) {
	    entryp->drivenWhole();
	}
	if (nodep->isOutput()
	    || nodep->isSigPublic() || nodep->isSigUserRWPublic()
	    || nodep->isSigUserRdPublic()
	    || (m_taskp && (m_taskp->dpiImport() || m_taskp->dpiExport()))) {
	    entryp->usedWhole();
	}
	// Discover variables used in bit definitions, etc
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstArraySel* nodep, AstNUser*) {
	// Arrays are rarely constant assigned, so for now we punt and do all entries
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstSel* nodep, AstNUser*) {
	AstVarRef* varrefp = nodep->fromp()->castVarRef();
	AstConst* constp = nodep->lsbp()->castConst();
	if (varrefp && constp && !constp->num().isFourState()) {
	    UndrivenVarEntry* entryp = getEntryp (varrefp->varp());
	    int lsb = constp->toUInt();
	    if (m_markBoth || varrefp->lvalue()) entryp->drivenBit(lsb, nodep->width());
	    if (m_markBoth || !varrefp->lvalue()) entryp->usedBit(lsb, nodep->width());
	} else {
	    // else other varrefs handled as unknown mess in AstVarRef
	    nodep->iterateChildren(*this);
	}
    }
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	// Any variable
	UndrivenVarEntry* entryp = getEntryp (nodep->varp());
	if (m_markBoth || nodep->lvalue()) entryp->drivenWhole();
	if (m_markBoth || !nodep->lvalue()) entryp->usedWhole();
    }

    // Don't know what black boxed calls do, assume in+out
    virtual void visit(AstSysIgnore* nodep, AstNUser*) {
	bool prevMark = m_markBoth;
	m_markBoth = true;
	nodep->iterateChildren(*this);
	m_markBoth = prevMark;
    }

    virtual void visit(AstNodeFTask* nodep, AstNUser*) {
	AstNodeFTask* prevTaskp = m_taskp;
	m_taskp = nodep;
	nodep->iterateChildren(*this);
	m_taskp = prevTaskp;
    }

    // Until we support tables, primitives will have undriven and unused I/Os
    virtual void visit(AstPrimitive* nodep, AstNUser*) {}

    // Coverage artifacts etc shouldn't count as a sink
    virtual void visit(AstCoverDecl* nodep, AstNUser*) {}
    virtual void visit(AstCoverInc* nodep, AstNUser*) {}
    virtual void visit(AstCoverToggle* nodep, AstNUser*) {}
    virtual void visit(AstTraceDecl* nodep, AstNUser*) {}
    virtual void visit(AstTraceInc* nodep, AstNUser*) {}

    // iterate
    virtual void visit(AstConst* nodep, AstNUser*) {}
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    UndrivenVisitor(AstNetlist* nodep) {
	m_markBoth = false;
	m_taskp = NULL;
	nodep->accept(*this);
    }
    virtual ~UndrivenVisitor() {
	for (vector<UndrivenVarEntry*>::iterator it = m_entryps.begin(); it != m_entryps.end(); ++it) {
	    (*it)->reportViolations();
	    delete (*it);
	}
    }
};

//######################################################################
// Undriven class functions

void V3Undriven::undrivenAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    UndrivenVisitor visitor (nodep);
}
