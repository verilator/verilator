// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Check for unused/undriven signals
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2004-2019 by Wilson Snyder.  This program is free software; you can
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
// Netlist:
//      Make vector for all variables
//	SEL(VARREF(...))) mark only some bits as used/driven
//	else VARREF(...) mark all bits as used/driven
//	Report unused/undriven nets
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3String.h"
#include "V3Undriven.h"
#include "V3Ast.h"

#include <algorithm>
#include <cstdarg>
#include <vector>

//######################################################################
// Class for every variable we may process

class UndrivenVarEntry {
    // MEMBERS
    AstVar*		m_varp;		// Variable this tracks
    bool		m_usedWhole;	// True if whole vector used
    bool		m_drivenWhole;	// True if whole vector driven
    std::vector<bool>   m_flags;        // Used/Driven on each subbit

    enum { FLAG_USED = 0, FLAG_DRIVEN = 1, FLAGS_PER_BIT = 2 };

    VL_DEBUG_FUNC;  // Declare debug()

public:
    // CONSTRUCTORS
    explicit UndrivenVarEntry(AstVar* varp) {  // Construction for when a var is used
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
    inline bool bitNumOk(int bit) const { return bit>=0
            && (bit*FLAGS_PER_BIT < static_cast<int>(m_flags.size())); }
    inline bool usedFlag(int bit) const { return m_usedWhole || m_flags[bit*FLAGS_PER_BIT + FLAG_USED]; }
    inline bool drivenFlag(int bit) const { return m_drivenWhole || m_flags[bit*FLAGS_PER_BIT + FLAG_DRIVEN]; }
    enum BitNamesWhich { BN_UNUSED, BN_UNDRIVEN, BN_BOTH };
    string bitNames(BitNamesWhich which) {
        string bits;
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
    void usedBit(int bit, int width) {
	UINFO(9, "set u["<<(bit+width-1)<<":"<<bit<<"] "<<m_varp->name()<<endl);
	for (int i=0; i<width; i++) {
	    if (bitNumOk(bit+i)) {
		m_flags[(bit+i)*FLAGS_PER_BIT + FLAG_USED] = true;
	    }
	}
    }
    void drivenBit(int bit, int width) {
	UINFO(9, "set d["<<(bit+width-1)<<":"<<bit<<"] "<<m_varp->name()<<endl);
	for (int i=0; i<width; i++) {
	    if (bitNumOk(bit+i)) {
		m_flags[(bit+i)*FLAGS_PER_BIT + FLAG_DRIVEN] = true;
	    }
	}
    }
    bool isUsedNotDrivenBit(int bit, int width) const {
	for (int i=0; i<width; i++) {
	    if (bitNumOk(bit+i)
		&& (m_usedWhole || m_flags[(bit+i)*FLAGS_PER_BIT + FLAG_USED])
		&& !(m_drivenWhole || m_flags[(bit+i)*FLAGS_PER_BIT + FLAG_DRIVEN])) return true;
	}
	return false;
    }
    bool isUsedNotDrivenAny() const {
	return isUsedNotDrivenBit(0, m_flags.size()/FLAGS_PER_BIT);
    }
    bool unusedMatch(AstVar* nodep) {
	string regexp = v3Global.opt.unusedRegexp();
	if (regexp == "") return false;
	string prettyName = nodep->prettyName();
	return VString::wildmatch(prettyName.c_str(), regexp.c_str());
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
	    if (nodep->isIfaceRef()) {
		// For interface top level we don't do any tracking
		// Ideally we'd report unused instance cells, but presumably a signal inside one
		// would get reported as unused
	    } else if (allU && allD) {
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
    // Netlist:
    //  AstVar::user1p		-> UndrivenVar* for usage var, 0=not set yet
    AstUser1InUse	m_inuser1;
    // Each always:
    //  AstNode::user2p		-> UndrivenVar* for usage var, 0=not set yet
    AstUser2InUse	m_inuser2;

    // STATE
    std::vector<UndrivenVarEntry*> m_entryps[3];  // Nodes to delete when we are finished
    bool                m_inBBox;       // In black box; mark as driven+used
    bool                m_inContAssign;  // In continuous assignment
    bool                m_inProcAssign;  // In procedual assignment
    AstNodeFTask*       m_taskp;        // Current task
    AstAlways*          m_alwaysCombp;  // Current always if combo, otherwise NULL

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    UndrivenVarEntry* getEntryp(AstVar* nodep, int which_user) {
	if (!(which_user==1 ? nodep->user1p() : nodep->user2p())) {
            UndrivenVarEntry* entryp = new UndrivenVarEntry(nodep);
            //UINFO(9," Associate u="<<which_user<<" "<<cvtToHex(this)<<" "<<nodep->name()<<endl);
	    m_entryps[which_user].push_back(entryp);
	    if (which_user==1) nodep->user1p(entryp);
	    else if (which_user==2) nodep->user2p(entryp);
	    else nodep->v3fatalSrc("Bad case");
	    return entryp;
	} else {
            UndrivenVarEntry* entryp = reinterpret_cast<UndrivenVarEntry*>
                (which_user==1 ? nodep->user1p() : nodep->user2p());
	    return entryp;
	}
    }

    void warnAlwCombOrder(AstNodeVarRef* nodep) {
	AstVar* varp = nodep->varp();
	if (!varp->isParam() && !varp->isGenVar() && !varp->isUsedLoopIdx()
	    && !m_inBBox   // We may have falsely considered a SysIgnore as a driver
            && !VN_IS(nodep, VarXRef)  // Xrefs might point at two different instances
	    && !varp->fileline()->warnIsOff(V3ErrorCode::ALWCOMBORDER)) {  // Warn only once per variable
	    nodep->v3warn(ALWCOMBORDER, "Always_comb variable driven after use: "<<nodep->prettyName());
	    varp->fileline()->modifyWarnOff(V3ErrorCode::ALWCOMBORDER, true);  // Complain just once for any usage
	}
    }

    // VISITORS
    virtual void visit(AstVar* nodep) {
        for (int usr=1; usr<(m_alwaysCombp?3:2); ++usr) {
            // For assigns and non-combo always, do just usr==1, to look for module-wide undriven etc
            // For non-combo always, run both usr==1 for above, and also usr==2 for always-only checks
            UndrivenVarEntry* entryp = getEntryp(nodep, usr);
            if (nodep->isNonOutput()
                || nodep->isSigPublic() || nodep->isSigUserRWPublic()
                || (m_taskp && (m_taskp->dpiImport() || m_taskp->dpiExport()))) {
                entryp->drivenWhole();
            }
            if (nodep->isWritable()
		|| nodep->isSigPublic() || nodep->isSigUserRWPublic()
		|| nodep->isSigUserRdPublic()
		|| (m_taskp && (m_taskp->dpiImport() || m_taskp->dpiExport()))) {
		entryp->usedWhole();
	    }
	}
	// Discover variables used in bit definitions, etc
        iterateChildren(nodep);
    }
    virtual void visit(AstArraySel* nodep) {
	// Arrays are rarely constant assigned, so for now we punt and do all entries
        iterateChildren(nodep);
    }
    virtual void visit(AstSliceSel* nodep) {
        // Arrays are rarely constant assigned, so for now we punt and do all entries
        iterateChildren(nodep);
    }
    virtual void visit(AstSel* nodep) {
        AstNodeVarRef* varrefp = VN_CAST(nodep->fromp(), NodeVarRef);
        AstConst* constp = VN_CAST(nodep->lsbp(), Const);
	if (varrefp && constp && !constp->num().isFourState()) {
            for (int usr=1; usr<(m_alwaysCombp?3:2); ++usr) {
                UndrivenVarEntry* entryp = getEntryp(varrefp->varp(), usr);
                int lsb = constp->toUInt();
                if (m_inBBox || varrefp->lvalue()) {
                    // Don't warn if already driven earlier as "a=0; if(a) a=1;" is fine.
                    if (usr==2 && m_alwaysCombp && entryp->isUsedNotDrivenBit(lsb, nodep->width())) {
                        UINFO(9," Select.  Entryp="<<cvtToHex(entryp)<<endl);
			warnAlwCombOrder(varrefp);
		    }
		    entryp->drivenBit(lsb, nodep->width());
		}
		if (m_inBBox || !varrefp->lvalue()) entryp->usedBit(lsb, nodep->width());
	    }
	} else {
	    // else other varrefs handled as unknown mess in AstVarRef
            iterateChildren(nodep);
	}
    }
    virtual void visit(AstNodeVarRef* nodep) {
	// Any variable
        if (nodep->lvalue()
            && !VN_IS(nodep, VarXRef)) {  // Ignore interface variables and similar ugly items
            if (m_inProcAssign && !nodep->varp()->varType().isProcAssignable()) {
                nodep->v3warn(PROCASSWIRE, "Procedural assignment to wire, perhaps intended var"
                              " (IEEE 2017 6.5): "
                              +nodep->prettyName());
            }
            if (m_inContAssign && !nodep->varp()->varType().isContAssignable()
                && !nodep->fileline()->language().systemVerilog()) {
                nodep->v3warn(CONTASSREG, "Continuous assignment to reg, perhaps intended wire"
                              " (IEEE 2005 6.1; Verilog only, legal in SV): "
                              +nodep->prettyName());
            }
        }
        for (int usr=1; usr<(m_alwaysCombp?3:2); ++usr) {
            UndrivenVarEntry* entryp = getEntryp(nodep->varp(), usr);
            bool fdrv = nodep->lvalue() && nodep->varp()->attrFileDescr();  // FD's are also being read from
            if (m_inBBox || nodep->lvalue()) {
                if (usr==2 && m_alwaysCombp && entryp->isUsedNotDrivenAny()) {
                    UINFO(9," Full bus.  Entryp="<<cvtToHex(entryp)<<endl);
		    warnAlwCombOrder(nodep);
		}
		entryp->drivenWhole();
	    }
	    if (m_inBBox || !nodep->lvalue() || fdrv) entryp->usedWhole();
	}
    }

    // Don't know what black boxed calls do, assume in+out
    virtual void visit(AstSysIgnore* nodep) {
	bool prevMark = m_inBBox;
	m_inBBox = true;
        iterateChildren(nodep);
	m_inBBox = prevMark;
    }

    virtual void visit(AstAssign* nodep) {
        bool prevProc = m_inProcAssign;
        {
            m_inProcAssign = true;
            iterateChildren(nodep);
            m_inProcAssign = false;
        }
        m_inProcAssign = prevProc;
    }
    virtual void visit(AstAssignDly* nodep) {
        bool prevProc = m_inProcAssign;
        {
            m_inProcAssign = true;
            iterateChildren(nodep);
            m_inProcAssign = false;
        }
        m_inProcAssign = prevProc;
    }
    virtual void visit(AstAssignW* nodep) {
        bool prevCont = m_inProcAssign;
        {
            m_inContAssign = true;
            iterateChildren(nodep);
            m_inContAssign = false;
        }
        m_inProcAssign = prevCont;
    }
    virtual void visit(AstAlways* nodep) {
        AstAlways* prevAlwp = m_alwaysCombp;
        {
            AstNode::user2ClearTree();
            if (nodep->keyword() == VAlwaysKwd::ALWAYS_COMB) UINFO(9,"   "<<nodep<<endl);
            if (nodep->keyword() == VAlwaysKwd::ALWAYS_COMB) m_alwaysCombp = nodep;
            else m_alwaysCombp = NULL;
            iterateChildren(nodep);
            if (nodep->keyword() == VAlwaysKwd::ALWAYS_COMB) UINFO(9,"   Done "<<nodep<<endl);
        }
        m_alwaysCombp = prevAlwp;
    }

    virtual void visit(AstNodeFTask* nodep) {
	AstNodeFTask* prevTaskp = m_taskp;
	m_taskp = nodep;
        iterateChildren(nodep);
	m_taskp = prevTaskp;
    }

    // Until we support tables, primitives will have undriven and unused I/Os
    virtual void visit(AstPrimitive* nodep) {}

    // Coverage artifacts etc shouldn't count as a sink
    virtual void visit(AstCoverDecl* nodep) {}
    virtual void visit(AstCoverInc* nodep) {}
    virtual void visit(AstCoverToggle* nodep) {}
    virtual void visit(AstTraceDecl* nodep) {}
    virtual void visit(AstTraceInc* nodep) {}

    // iterate
    virtual void visit(AstConst* nodep) {}
    virtual void visit(AstNode* nodep) {
        iterateChildren(nodep);
    }
public:
    // CONSTUCTORS
    explicit UndrivenVisitor(AstNetlist* nodep) {
        m_inBBox = false;
        m_inContAssign = false;
        m_inProcAssign = false;
        m_taskp = NULL;
        m_alwaysCombp = NULL;
        iterate(nodep);
    }
    virtual ~UndrivenVisitor() {
        for (std::vector<UndrivenVarEntry*>::iterator it = m_entryps[1].begin(); it != m_entryps[1].end(); ++it) {
	    (*it)->reportViolations();
	}
	for (int usr=1; usr<3; ++usr) {
            for (std::vector<UndrivenVarEntry*>::iterator it = m_entryps[usr].begin(); it != m_entryps[usr].end(); ++it) {
		delete (*it);
	    }
	}
    }
};

//######################################################################
// Undriven class functions

void V3Undriven::undrivenAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    UndrivenVisitor visitor (nodep);
}
