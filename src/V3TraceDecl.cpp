// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Waves tracing
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
// V3TraceDecl's Transformations:
//      Create trace CFUNCs
//      For each VARSCOPE
//          If appropriate type of signal, create a TRACE
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3TraceDecl.h"
#include "V3EmitCBase.h"
#include "V3Stats.h"

#include <cstdarg>

//######################################################################
// TraceDecl state, as a visitor of each AstNode

class TraceDeclVisitor : public EmitCBaseVisitor {
private:
    // NODE STATE

    // STATE
    AstScope* m_scopetopp;  // Current top scope
    AstCFunc* m_initFuncp;  // Trace function being built
    AstCFunc* m_initSubFuncp;  // Trace function being built (under m_init)
    int m_initSubStmts;  // Number of statements in function
    AstCFunc* m_fullFuncp;  // Trace function being built
    AstCFunc* m_chgFuncp;  // Trace function being built
    int m_funcNum;  // Function number being built
    AstVarScope* m_traVscp;  // Signal being trace constructed
    AstNode* m_traValuep;  // Signal being traced's value to trace in it
    string m_traShowname;  // Signal being traced's component name
    bool m_interface;  // Currently tracing an interface

    VDouble0 m_statSigs;  // Statistic tracking
    VDouble0 m_statIgnSigs;  // Statistic tracking

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    const char* vscIgnoreTrace(AstVarScope* nodep) {
        // Return true if this shouldn't be traced
        // See also similar rule in V3Coverage::varIgnoreToggle
        AstVar* varp = nodep->varp();
        if (!varp->isTrace()) {
            return "Verilator trace_off";
        } else if (!nodep->isTrace()) {
            return "Verilator cell trace_off";
        } else if (!v3Global.opt.traceUnderscore()) {
            string prettyName = varp->prettyName();
            if (!prettyName.empty() && prettyName[0] == '_') return "Leading underscore";
            if (prettyName.find("._") != string::npos) return "Inlined leading underscore";
        }
        return NULL;
    }

    AstCFunc* newCFunc(AstCFuncType type, const string& name, bool slow) {
        AstCFunc* funcp = new AstCFunc(m_scopetopp->fileline(), name, m_scopetopp);
        funcp->slow(slow);
        string argTypes(EmitCBaseVisitor::symClassVar() + ", " + v3Global.opt.traceClassBase()
                        + "* vcdp, uint32_t code");
        if (m_interface) argTypes += ", const char* scopep";
        funcp->argTypes(argTypes);
        funcp->funcType(type);
        funcp->symProlog(true);
        m_scopetopp->addActivep(funcp);
        UINFO(5, "  Newfunc " << funcp << endl);
        return funcp;
    }
    void callCFuncSub(AstCFunc* basep, AstCFunc* funcp, AstIntfRef* irp) {
        AstCCall* callp = new AstCCall(funcp->fileline(), funcp);
        callp->argTypes("vlSymsp, vcdp, code");
        if (irp) callp->addArgsp(irp->unlinkFrBack());
        basep->addStmtsp(callp);
    }
    AstCFunc* newCFuncSub(AstCFunc* basep) {
        string name = basep->name() + "__" + cvtToStr(++m_funcNum);
        AstCFunc* funcp = NULL;
        if (basep->funcType() == AstCFuncType::TRACE_INIT
            || basep->funcType() == AstCFuncType::TRACE_INIT_SUB) {
            funcp = newCFunc(AstCFuncType::TRACE_INIT_SUB, name, basep->slow());
        } else {
            basep->v3fatalSrc("Strange base function type");
        }
        if (!m_interface) callCFuncSub(basep, funcp, NULL);
        return funcp;
    }
    void addTraceDecl(const VNumRange& arrayRange,
                      int widthOverride) {  // If !=0, is packed struct/array where basicp size
                                            // misreflects one element
        VNumRange bitRange;
        AstBasicDType* bdtypep = m_traValuep->dtypep()->basicp();
        if (widthOverride) {
            bitRange = VNumRange(widthOverride - 1, 0, false);
        } else if (bdtypep) {
            bitRange = bdtypep->nrange();
        }
        AstTraceDecl* declp
            = new AstTraceDecl(m_traVscp->fileline(), m_traShowname, m_traVscp->varp(),
                               m_traValuep, bitRange, arrayRange, m_interface);
        UINFO(9, "Decl " << declp << endl);

        if (!m_interface && v3Global.opt.outputSplitCTrace()
            && m_initSubStmts > v3Global.opt.outputSplitCTrace()) {
            m_initSubFuncp = newCFuncSub(m_initFuncp);
            m_initSubStmts = 0;
        }

        m_initSubFuncp->addStmtsp(declp);
        m_initSubStmts += EmitCBaseCounterVisitor(declp).count();

        m_chgFuncp->addStmtsp(
            new AstTraceInc(m_traVscp->fileline(), declp, m_traValuep->cloneTree(true)));
        // The full version will get constructed in V3Trace
    }
    void addIgnore(const char* why) {
        ++m_statIgnSigs;
        m_initSubFuncp->addStmtsp(new AstComment(
            m_traVscp->fileline(), "Tracing: " + m_traShowname + " // Ignored: " + why, true));
    }

    // VISITORS
    virtual void visit(AstTopScope* nodep) VL_OVERRIDE {
        m_scopetopp = nodep->scopep();
        // Make containers for TRACEDECLs first
        m_initFuncp = newCFunc(AstCFuncType::TRACE_INIT, "traceInitThis", true);
        m_fullFuncp = newCFunc(AstCFuncType::TRACE_FULL, "traceFullThis", true);
        m_chgFuncp = newCFunc(AstCFuncType::TRACE_CHANGE, "traceChgThis", false);
        //
        m_initSubFuncp = newCFuncSub(m_initFuncp);
        // And find variables
        iterateChildren(nodep);
    }
    virtual void visit(AstScope* nodep) VL_OVERRIDE {
        AstCell* cellp = VN_CAST(nodep->aboveCellp(), Cell);
        if (cellp && VN_IS(cellp->modp(), Iface)) {
            AstCFunc* origSubFunc = m_initSubFuncp;
            int origSubStmts = m_initSubStmts;
            {
                m_interface = true;
                m_initSubFuncp = newCFuncSub(origSubFunc);
                string scopeName = nodep->prettyName();
                size_t lastDot = scopeName.find_last_of('.');
                UASSERT_OBJ(lastDot != string::npos, nodep,
                            "Expected an interface scope name to have at least one dot");
                scopeName = scopeName.substr(0, lastDot + 1);
                size_t scopeLen = scopeName.length();

                AstIntfRef* nextIrp = cellp->intfRefp();
                // While instead of for loop because interface references will
                // be unlinked as we go
                while (nextIrp) {
                    AstIntfRef* irp = nextIrp;
                    nextIrp = VN_CAST(irp->nextp(), IntfRef);

                    string irpName = irp->prettyName();
                    if (scopeLen > irpName.length()) continue;
                    string intfScopeName = irpName.substr(0, scopeLen);
                    if (scopeName != intfScopeName) continue;
                    callCFuncSub(origSubFunc, m_initSubFuncp, irp);
                    ++origSubStmts;
                }
                iterateChildren(nodep);
            }
            m_initSubFuncp = origSubFunc;
            m_initSubStmts = origSubStmts;
            m_interface = false;
        } else {
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstVarScope* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        // Prefilter - things that get through this if will either get
        // traced or get a comment as to why not traced.
        // Generally this equation doesn't need updating, instead use
        // varp->isTrace() and/or vscIgnoreTrace.
        if ((!nodep->varp()->isTemp() || nodep->varp()->isTrace())
            && !nodep->varp()->isClassMember() && !nodep->varp()->isFuncLocal()) {
            UINFO(5, "    vsc " << nodep << endl);
            AstVar* varp = nodep->varp();
            AstScope* scopep = nodep->scopep();
            // Compute show name
            // This code assumes SPTRACEVCDC_VERSION >= 1330;
            // it uses spaces to separate hierarchy components.
            if (m_interface) {
                m_traShowname = AstNode::vcdName(varp->name());
            } else {
                m_traShowname = AstNode::vcdName(scopep->name() + " " + varp->name());
                if (m_traShowname.substr(0, 4) == "TOP ") m_traShowname.replace(0, 4, "");
            }
            UASSERT_OBJ(m_initSubFuncp, nodep, "NULL");

            m_traVscp = nodep;
            m_traValuep = NULL;
            if (vscIgnoreTrace(nodep)) {
                addIgnore(vscIgnoreTrace(nodep));
            } else {
                ++m_statSigs;
                if (nodep->valuep()) {
                    m_traValuep = nodep->valuep()->cloneTree(true);
                } else {
                    m_traValuep = new AstVarRef(nodep->fileline(), nodep, false);
                }
                {
                    // Recurse into data type of the signal; the visitors will call addTraceDecl()
                    iterate(varp->dtypep()->skipRefToEnump());
                }
                // Cleanup
                if (m_traValuep) VL_DO_CLEAR(m_traValuep->deleteTree(), m_traValuep = NULL);
            }
            m_traVscp = NULL;
            m_traValuep = NULL;
            m_traShowname = "";
        }
    }
    // VISITORS - Data types when tracing
    virtual void visit(AstConstDType* nodep) VL_OVERRIDE {
        if (m_traVscp) iterate(nodep->subDTypep()->skipRefToEnump());
    }
    virtual void visit(AstRefDType* nodep) VL_OVERRIDE {
        if (m_traVscp) iterate(nodep->subDTypep()->skipRefToEnump());
    }
    virtual void visit(AstUnpackArrayDType* nodep) VL_OVERRIDE {
        // Note more specific dtypes above
        if (m_traVscp) {
            if (static_cast<int>(nodep->arrayUnpackedElements()) > v3Global.opt.traceMaxArray()) {
                addIgnore("Wide memory > --trace-max-array ents");
            } else if (VN_IS(nodep->subDTypep()->skipRefToEnump(),
                             BasicDType)  // Nothing lower than this array
                       && m_traVscp->dtypep()->skipRefToEnump()
                              == nodep) {  // Nothing above this array
                // Simple 1-D array, use existing V3EmitC runtime loop rather than unrolling
                // This will put "(index)" at end of signal name for us
                if (m_traVscp->dtypep()->skipRefToEnump()->isString()) {
                    addIgnore("Unsupported: strings");
                } else {
                    addTraceDecl(nodep->declRange(), 0);
                }
            } else {
                // Unroll now, as have no other method to get right signal names
                AstNodeDType* subtypep = nodep->subDTypep()->skipRefToEnump();
                for (int i = nodep->lsb(); i <= nodep->msb(); ++i) {
                    string oldShowname = m_traShowname;
                    AstNode* oldValuep = m_traValuep;
                    {
                        m_traShowname += string("(") + cvtToStr(i) + string(")");
                        m_traValuep = new AstArraySel(
                            nodep->fileline(), m_traValuep->cloneTree(true), i - nodep->lsb());

                        m_traValuep->dtypep(subtypep);
                        iterate(subtypep);
                        VL_DO_CLEAR(m_traValuep->deleteTree(), m_traValuep = NULL);
                    }
                    m_traShowname = oldShowname;
                    m_traValuep = oldValuep;
                }
            }
        }
    }
    virtual void visit(AstPackArrayDType* nodep) VL_OVERRIDE {
        if (m_traVscp) {
            if (!v3Global.opt.traceStructs()) {
                // Everything downstream is packed, so deal with as one trace unit.
                // This may not be the nicest for user presentation, but is
                // a much faster way to trace
                addTraceDecl(VNumRange(), nodep->width());
            } else {
                AstNodeDType* subtypep = nodep->subDTypep()->skipRefToEnump();
                for (int i = nodep->lsb(); i <= nodep->msb(); ++i) {
                    string oldShowname = m_traShowname;
                    AstNode* oldValuep = m_traValuep;
                    {
                        m_traShowname += string("(") + cvtToStr(i) + string(")");
                        m_traValuep = new AstSel(nodep->fileline(), m_traValuep->cloneTree(true),
                                                 (i - nodep->lsb()) * subtypep->width(),
                                                 subtypep->width());
                        m_traValuep->dtypep(subtypep);
                        iterate(subtypep);
                        VL_DO_CLEAR(m_traValuep->deleteTree(), m_traValuep = NULL);
                    }
                    m_traShowname = oldShowname;
                    m_traValuep = oldValuep;
                }
            }
        }
    }
    virtual void visit(AstNodeUOrStructDType* nodep) VL_OVERRIDE {
        if (m_traVscp) {
            if (nodep->packed() && !v3Global.opt.traceStructs()) {
                // Everything downstream is packed, so deal with as one trace unit
                // This may not be the nicest for user presentation, but is
                // a much faster way to trace
                addTraceDecl(VNumRange(), nodep->width());
            } else {
                if (!nodep->packed()) {
                    addIgnore("Unsupported: Unpacked struct/union");
                } else {
                    for (AstMemberDType* itemp = nodep->membersp(); itemp;
                         itemp = VN_CAST(itemp->nextp(), MemberDType)) {
                        AstNodeDType* subtypep = itemp->subDTypep()->skipRefToEnump();
                        string oldShowname = m_traShowname;
                        AstNode* oldValuep = m_traValuep;
                        {
                            m_traShowname += string(" ") + itemp->prettyName();
                            if (VN_IS(nodep, StructDType)) {
                                m_traValuep
                                    = new AstSel(nodep->fileline(), m_traValuep->cloneTree(true),
                                                 itemp->lsb(), subtypep->width());
                                m_traValuep->dtypep(subtypep);
                                iterate(subtypep);
                                VL_DO_CLEAR(m_traValuep->deleteTree(), m_traValuep = NULL);
                            } else {  // Else union, replicate fields
                                iterate(subtypep);
                            }
                        }
                        m_traShowname = oldShowname;
                        m_traValuep = oldValuep;
                    }
                }
            }
        }
    }
    virtual void visit(AstBasicDType* nodep) VL_OVERRIDE {
        if (m_traVscp) {
            if (nodep->isString()) {
                addIgnore("Unsupported: strings");
            } else {
                addTraceDecl(VNumRange(), 0);
            }
        }
    }
    virtual void visit(AstEnumDType* nodep) VL_OVERRIDE { iterate(nodep->skipRefp()); }
    virtual void visit(AstNodeDType* nodep) VL_OVERRIDE {
        // Note more specific dtypes above
        if (!m_traVscp) return;
        addIgnore("Unsupported: data type");
    }

    //--------------------
    virtual void visit(AstNode* nodep) VL_OVERRIDE { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit TraceDeclVisitor(AstNetlist* nodep) {
        m_scopetopp = NULL;
        m_initFuncp = NULL;
        m_initSubFuncp = NULL;
        m_initSubStmts = 0;
        m_fullFuncp = NULL;
        m_chgFuncp = NULL;
        m_funcNum = 0;
        m_traVscp = NULL;
        m_traValuep = NULL;
        m_interface = false;
        iterate(nodep);
    }
    virtual ~TraceDeclVisitor() {
        V3Stats::addStat("Tracing, Traced signals", m_statSigs);
        V3Stats::addStat("Tracing, Ignored signals", m_statIgnSigs);
    }
};

//######################################################################
// Trace class functions

void V3TraceDecl::traceDeclAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { TraceDeclVisitor visitor(nodep); }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("tracedecl", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
