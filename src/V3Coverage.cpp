// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Netlist (top level) functions
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// COVERAGE TRANSFORMATIONS:
//      At each IF/(IF else)/CASEITEM,
//         If there's no coverage off on the block below it,
//         or a $stop
//              Insert a COVERDECL node in the module.
//              (V3Emit reencodes into per-module numbers for emitting.)
//              Insert a COVERINC node at the end of the statement list
//              for that if/else/case.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Coverage.h"
#include "V3Ast.h"

#include <cstdarg>
#include <map>

//######################################################################
// Coverage state, as a visitor of each AstNode

class CoverageVisitor : public AstNVisitor {
private:
    // TYPES
    typedef std::map<string,int> FileMap;

    struct ToggleEnt {
        string          m_comment;      // Comment for coverage dump
        AstNode*        m_varRefp;      // How to get to this element
        AstNode*        m_chgRefp;      // How to get to this element
        ToggleEnt(const string& comment, AstNode* vp, AstNode* cp)
            : m_comment(comment), m_varRefp(vp), m_chgRefp(cp) {}
        ~ToggleEnt() {}
        void cleanup() {
            VL_DO_CLEAR(m_varRefp->deleteTree(), m_varRefp = NULL);
            VL_DO_CLEAR(m_chgRefp->deleteTree(), m_chgRefp = NULL);
        }
    };

    // NODE STATE
    // Entire netlist:
    //  AstIf::user1()                  -> bool.  True indicates ifelse processed
    AstUser1InUse       m_inuser1;

    // STATE
    bool                m_checkBlock;   // Should this block get covered?
    AstNodeModule*      m_modp;         // Current module to add statement to
    bool        m_inToggleOff;  // In function/task etc
    bool        m_inModOff;     // In module with no coverage
    FileMap     m_fileps;       // Column counts for each fileline
    string      m_beginHier;    // AstBegin hier name for user coverage points

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    const char* varIgnoreToggle(AstVar* nodep) {
        // Return true if this shouldn't be traced
        // See also similar rule in V3TraceDecl::varIgnoreTrace
        if (!nodep->isToggleCoverable())
            return "Not relevant signal type";
        if (!v3Global.opt.coverageUnderscore()) {
            string prettyName = nodep->prettyName();
            if (prettyName[0] == '_')
                return "Leading underscore";
            if (prettyName.find("._") != string::npos)
                return "Inlined leading underscore";
        }
        if ((nodep->width()*nodep->dtypep()->arrayUnpackedElements()) > 256) {
            return "Wide bus/array > 256 bits";
        }
        // We allow this, though tracing doesn't
        // if (nodep->arrayp(1)) return "Unsupported: Multi-dimensional array";
        return NULL;
    }

    AstCoverInc* newCoverInc(FileLine* fl, const string& hier,
                             const string& page_prefix, const string& comment,
                             const string& trace_var_name) {
        // For line coverage, we may have multiple if's on one line, so disambiguate if
        // everything is otherwise identical
        // (Don't set column otherwise as it may result in making bins not match up with
        // different types of coverage enabled.)
        string key = fl->filename()+"\001"+cvtToStr(fl->lineno())
            +"\001"+hier+"\001"+page_prefix+"\001"+comment;
        int column = 0;
        FileMap::iterator it = m_fileps.find(key);
        if (it == m_fileps.end()) {
            m_fileps.insert(make_pair(key, column+1));
        } else {
            column = (it->second)++;
        }

        // We could use the basename of the filename to the page, but seems
        // better for code from an include file to be listed under the
        // module using it rather than the include file.
        // Note the module name could have parameters appended, we'll consider this
        // a feature as it allows for each parameterized block to be counted separately.
        // Someday the user might be allowed to specify a different page suffix
        string page = page_prefix + "/" + m_modp->prettyName();

        AstCoverDecl* declp = new AstCoverDecl(fl, column, page, comment);
        declp->hier(hier);
        m_modp->addStmtp(declp);

        AstCoverInc* incp = new AstCoverInc(fl, declp);
        if (!trace_var_name.empty() && v3Global.opt.traceCoverage()) {
            AstVar* varp = new AstVar(incp->fileline(),
                                      AstVarType::MODULETEMP, trace_var_name,
                                      incp->findUInt32DType());
            varp->trace(true);
            varp->fileline()->modifyWarnOff(V3ErrorCode::UNUSED, true);
            m_modp->addStmtp(varp);
            UINFO(5, "New coverage trace: "<<varp<<endl);
            AstAssign* assp  = new AstAssign(
                incp->fileline(),
                new AstVarRef(incp->fileline(), varp, true),
                new AstAdd(incp->fileline(),
                           new AstVarRef(incp->fileline(), varp, false),
                           new AstConst(incp->fileline(), AstConst::WidthedValue(), 32, 1)));
            incp->addNext(assp);
        }
        return incp;
    }
    string traceNameForLine(AstNode* nodep, const string& type) {
        return "vlCoverageLineTrace_"+nodep->fileline()->filebasenameNoExt()
            +"__"+cvtToStr(nodep->fileline()->lineno())
            +"_"+type;
    }
    // VISITORS - BOTH
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        AstNodeModule* origModp = m_modp;
        bool origInModOff = m_inModOff;
        {
            m_modp = nodep;
            m_inModOff = nodep->isTop();  // Ignore coverage on top module; it's a shell we created
            m_fileps.clear();
            iterateChildren(nodep);
        }
        m_modp = origModp;
        m_inModOff = origInModOff;
    }

    // VISITORS - TOGGLE COVERAGE
    virtual void visit(AstNodeFTask* nodep) VL_OVERRIDE {
        bool oldtog = m_inToggleOff;
        {
            m_inToggleOff = true;
            iterateChildren(nodep);
        }
        m_inToggleOff = oldtog;
    }
    virtual void visit(AstVar* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        if (m_modp && !m_inModOff && !m_inToggleOff
            && nodep->fileline()->coverageOn() && v3Global.opt.coverageToggle()) {
            const char* disablep = varIgnoreToggle(nodep);
            if (disablep) {
                UINFO(4, "    Disable Toggle: "<<disablep<<" "<<nodep<<endl);
            } else {
                UINFO(4, "    Toggle: "<<nodep<<endl);
                // There's several overall ways to approach this
                //    Treat like tracing, where a end-of-timestamp action sees all changes
                //      Works ok, but would be quite slow as need to reform
                //      vectors before the calls
                //    Convert to "always @ (posedge signal[#]) coverinc"
                //      Would mark many signals as clocks, precluding many later optimizations
                //    Convert to "if (x & !lastx) CoverInc"
                //      OK, but we couldn't later detect them to schedule where the IFs get called
                //    Convert to "AstCoverInc(CoverInc...)"
                //      We'll do this, and make the if(...) coverinc later.

                // Add signal to hold the old value
                string newvarname = string("__Vtogcov__")+nodep->shortName();
                AstVar* chgVarp = new AstVar(nodep->fileline(),
                                             AstVarType::MODULETEMP, newvarname, nodep);
                chgVarp->fileline()->modifyWarnOff(V3ErrorCode::UNUSED, true);
                m_modp->addStmtp(chgVarp);

                // Create bucket for each dimension * bit.
                // This is necessarily an O(n^2) expansion, which is why
                // we limit coverage to signals with < 256 bits.

                ToggleEnt newvec (string(""),
                                  new AstVarRef(nodep->fileline(), nodep, false),
                                  new AstVarRef(nodep->fileline(), chgVarp, true));
                toggleVarRecurse(nodep->dtypeSkipRefp(), 0, newvec,
                                 nodep, chgVarp);
                newvec.cleanup();
            }
        }
    }

    void toggleVarBottom(const ToggleEnt& above, const AstVar* varp) {
        AstCoverToggle* newp
            = new AstCoverToggle(varp->fileline(),
                                 newCoverInc(varp->fileline(), "", "v_toggle",
                                             varp->name()+above.m_comment, ""),
                                 above.m_varRefp->cloneTree(true),
                                 above.m_chgRefp->cloneTree(true));
        m_modp->addStmtp(newp);
    }

    void toggleVarRecurse(AstNodeDType* dtypep, int depth,  // per-iteration
                     const ToggleEnt& above,
                     AstVar* varp, AstVar* chgVarp) {  // Constant
        if (const AstBasicDType* bdtypep = VN_CAST(dtypep, BasicDType)) {
            if (bdtypep->isRanged()) {
                for (int index_docs=bdtypep->lsb(); index_docs<bdtypep->msb()+1; index_docs++) {
                    int index_code = index_docs - bdtypep->lsb();
                    ToggleEnt newent (above.m_comment+string("[")+cvtToStr(index_docs)+"]",
                                      new AstSel(varp->fileline(),
                                                 above.m_varRefp->cloneTree(true), index_code, 1),
                                      new AstSel(varp->fileline(),
                                                 above.m_chgRefp->cloneTree(true), index_code, 1));
                    toggleVarBottom(newent, varp);
                    newent.cleanup();
                }
            } else {
                toggleVarBottom(above, varp);
            }
        }
        else if (AstUnpackArrayDType* adtypep = VN_CAST(dtypep, UnpackArrayDType)) {
            for (int index_docs=adtypep->lsb(); index_docs<=adtypep->msb(); ++index_docs) {
                int index_code = index_docs - adtypep->lsb();
                ToggleEnt newent (above.m_comment+string("[")+cvtToStr(index_docs)+"]",
                                  new AstArraySel(varp->fileline(),
                                                  above.m_varRefp->cloneTree(true), index_code),
                                  new AstArraySel(varp->fileline(),
                                                  above.m_chgRefp->cloneTree(true), index_code));
                toggleVarRecurse(adtypep->subDTypep()->skipRefp(), depth+1,
                                 newent,
                                 varp, chgVarp);
                newent.cleanup();
            }
        }
        else if (AstPackArrayDType* adtypep = VN_CAST(dtypep, PackArrayDType)) {
            for (int index_docs=adtypep->lsb(); index_docs<=adtypep->msb(); ++index_docs) {
                AstNodeDType* subtypep = adtypep->subDTypep()->skipRefp();
                int index_code = index_docs - adtypep->lsb();
                ToggleEnt newent (above.m_comment+string("[")+cvtToStr(index_docs)+"]",
                                  new AstSel(varp->fileline(), above.m_varRefp->cloneTree(true),
                                             index_code*subtypep->width(), subtypep->width()),
                                  new AstSel(varp->fileline(), above.m_chgRefp->cloneTree(true),
                                             index_code*subtypep->width(), subtypep->width()));
                toggleVarRecurse(adtypep->subDTypep()->skipRefp(), depth+1,
                                 newent,
                                 varp, chgVarp);
                newent.cleanup();
            }
        }
        else if (AstStructDType* adtypep = VN_CAST(dtypep, StructDType)) {
            // For now it's packed, so similar to array
            for (AstMemberDType* itemp = adtypep->membersp();
                 itemp; itemp=VN_CAST(itemp->nextp(), MemberDType)) {
                AstNodeDType* subtypep = itemp->subDTypep()->skipRefp();
                int index_code = itemp->lsb();
                ToggleEnt newent (above.m_comment+string(".")+itemp->name(),
                                  new AstSel(varp->fileline(), above.m_varRefp->cloneTree(true),
                                             index_code, subtypep->width()),
                                  new AstSel(varp->fileline(), above.m_chgRefp->cloneTree(true),
                                             index_code, subtypep->width()));
                toggleVarRecurse(subtypep, depth+1,
                                 newent,
                                 varp, chgVarp);
                newent.cleanup();
            }
        }
        else if (AstUnionDType* adtypep = VN_CAST(dtypep, UnionDType)) {
            // Arbitrarily handle only the first member of the union
            if (AstMemberDType* itemp = adtypep->membersp()) {
                AstNodeDType* subtypep = itemp->subDTypep()->skipRefp();
                ToggleEnt newent (above.m_comment+string(".")+itemp->name(),
                                  above.m_varRefp->cloneTree(true),
                                  above.m_chgRefp->cloneTree(true));
                toggleVarRecurse(subtypep, depth+1,
                                 newent,
                                 varp, chgVarp);
                newent.cleanup();
            }
        }
        else {
            dtypep->v3fatalSrc("Unexpected node data type in toggle coverage generation: "
                               <<dtypep->prettyTypeName());
        }
    }

    // VISITORS - LINE COVERAGE
    virtual void visit(AstIf* nodep) VL_OVERRIDE {  // Note not AstNodeIf; other types don't get covered
        UINFO(4," IF: "<<nodep<<endl);
        if (m_checkBlock) {
            // An else-if.  When we iterate the if, use "elsif" marking
            bool elsif = (VN_IS(nodep->elsesp(), If)
                          && !VN_CAST(nodep->elsesp(), If)->nextp());
            if (elsif) VN_CAST(nodep->elsesp(), If)->user1(true);
            //
            iterateAndNextNull(nodep->ifsp());
            if (m_checkBlock && !m_inModOff
                && nodep->fileline()->coverageOn() && v3Global.opt.coverageLine()) {  // if a "if" branch didn't disable it
                UINFO(4,"   COVER: "<<nodep<<endl);
                if (nodep->user1()) {
                    nodep->addIfsp(newCoverInc(nodep->fileline(), "", "v_line", "elsif",
                                               traceNameForLine(nodep, "elsif")));
                } else {
                    nodep->addIfsp(newCoverInc(nodep->fileline(), "", "v_line", "if",
                                               traceNameForLine(nodep, "if")));
                }
            }
            // Don't do empty else's, only empty if/case's
            if (nodep->elsesp()) {
                m_checkBlock = true;
                iterateAndNextNull(nodep->elsesp());
                if (m_checkBlock && !m_inModOff
                    && nodep->fileline()->coverageOn() && v3Global.opt.coverageLine()) {  // if a "else" branch didn't disable it
                    UINFO(4,"   COVER: "<<nodep<<endl);
                    if (!elsif) {  // elsif done inside if()
                        nodep->addElsesp(newCoverInc(nodep->elsesp()->fileline(),
                                                     "", "v_line", "else",
                                                     traceNameForLine(nodep, "else")));
                    }
                }
            }
            m_checkBlock = true;  // Reset as a child may have cleared it
        }
    }
    virtual void visit(AstCaseItem* nodep) VL_OVERRIDE {
        UINFO(4," CASEI: "<<nodep<<endl);
        if (m_checkBlock && !m_inModOff
            && nodep->fileline()->coverageOn() && v3Global.opt.coverageLine()) {
            iterateAndNextNull(nodep->bodysp());
            if (m_checkBlock) {  // if the case body didn't disable it
                UINFO(4,"   COVER: "<<nodep<<endl);
                nodep->addBodysp(newCoverInc(nodep->fileline(), "", "v_line", "case",
                                             traceNameForLine(nodep, "case")));
            }
            m_checkBlock = true;  // Reset as a child may have cleared it
        }
    }
    virtual void visit(AstCover* nodep) VL_OVERRIDE {
        UINFO(4," COVER: "<<nodep<<endl);
        m_checkBlock = true;  // Always do cover blocks, even if there's a $stop
        iterateChildren(nodep);
        if (!nodep->coverincp()) {
            // Note the name may be overridden by V3Assert processing
            nodep->coverincp(newCoverInc(nodep->fileline(), m_beginHier, "v_user", "cover",
                                         m_beginHier+"_vlCoverageUserTrace"));
        }
        m_checkBlock = true;  // Reset as a child may have cleared it
    }
    virtual void visit(AstStop* nodep) VL_OVERRIDE {
        UINFO(4,"  STOP: "<<nodep<<endl);
        m_checkBlock = false;
    }
    virtual void visit(AstPragma* nodep) VL_OVERRIDE {
        if (nodep->pragType() == AstPragmaType::COVERAGE_BLOCK_OFF) {
            // Skip all NEXT nodes under this block, and skip this if/case branch
            UINFO(4,"  OFF: "<<nodep<<endl);
            m_checkBlock = false;
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else {
            if (m_checkBlock) iterateChildren(nodep);
        }
    }
    virtual void visit(AstBegin* nodep) VL_OVERRIDE {
        // Record the hierarchy of any named begins, so we can apply to user
        // coverage points.  This is because there may be cov points inside
        // generate blocks; each point should get separate consideration.
        // (Currently ignored for line coverage, since any generate iteration
        // covers the code in that line.)
        string oldHier = m_beginHier;
        bool oldtog = m_inToggleOff;
        {
            m_inToggleOff = true;
            if (nodep->name()!="") {
                m_beginHier = m_beginHier + (m_beginHier!=""?".":"") + nodep->name();
            }
            iterateChildren(nodep);
        }
        m_beginHier = oldHier;
        m_inToggleOff = oldtog;
    }

    // VISITORS - BOTH
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        // Default: Just iterate
        if (m_checkBlock) {
            iterateChildren(nodep);
            m_checkBlock = true;  // Reset as a child may have cleared it
        }
    }

public:
    // CONSTRUCTORS
    explicit CoverageVisitor(AstNetlist* rootp) {
        // Operate on all modules
        m_checkBlock = true;
        m_modp = NULL;
        m_beginHier = "";
        m_inToggleOff = false;
        m_inModOff = true;
        iterateChildren(rootp);
    }
    virtual ~CoverageVisitor() {}
};

//######################################################################
// Coverage class functions

void V3Coverage::coverage(AstNetlist* rootp) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        CoverageVisitor visitor (rootp);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("coverage", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
