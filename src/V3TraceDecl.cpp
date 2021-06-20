// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Waves tracing
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2021 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3TraceDecl's Transformations:
//      Create trace init CFunc
//      For each VarScope
//          If appropriate type of signal, create a TraceDecl
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include "verilated_trace_defs.h"  // For VLT_TRACE_SCOPE_*

#include "V3Global.h"
#include "V3TraceDecl.h"
#include "V3EmitCBase.h"
#include "V3Stats.h"

//######################################################################
// TraceDecl state, as a visitor of each AstNode

class TraceDeclVisitor final : public EmitCBaseVisitor {
private:
    // NODE STATE

    // STATE
    AstScope* m_topScopep = nullptr;  // Current top scope
    AstCFunc* m_initFuncp = nullptr;  // Trace function being built
    AstCFunc* m_initSubFuncp = nullptr;  // Trace function being built (under m_init)
    int m_initSubStmts = 0;  // Number of statements in function
    int m_funcNum = 0;  // Function number being built
    AstVarScope* m_traVscp = nullptr;  // Signal being trace constructed
    AstNode* m_traValuep = nullptr;  // Signal being traced's value to trace in it
    string m_traShowname;  // Signal being traced's component name
    bool m_interface = false;  // Currently tracing an interface

    VDouble0 m_statSigs;  // Statistic tracking
    VDouble0 m_statIgnSigs;  // Statistic tracking

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    const char* vscIgnoreTrace(const AstVarScope* nodep) {
        // Return true if this shouldn't be traced
        // See also similar rule in V3Coverage::varIgnoreToggle
        const AstVar* const varp = nodep->varp();
        if (!varp->isTrace()) {
            return "Verilator trace_off";
        } else if (!nodep->isTrace()) {
            return "Verilator instance trace_off";
        } else if (!v3Global.opt.traceUnderscore()) {
            const string prettyName = varp->prettyName();
            if (!prettyName.empty() && prettyName[0] == '_') return "Leading underscore";
            if (prettyName.find("._") != string::npos) return "Inlined leading underscore";
        }
        return nullptr;
    }

    AstCFunc* newCFunc(AstCFuncType type, const string& name) {
        FileLine* const flp = m_topScopep->fileline();
        AstCFunc* const funcp = new AstCFunc(flp, name, m_topScopep);
        string argTypes = v3Global.opt.traceClassBase() + "* tracep";
        if (m_interface) argTypes += ", int scopet, const char* scopep";
        funcp->argTypes(argTypes);
        funcp->funcType(type);
        funcp->isStatic(false);
        funcp->isLoose(true);
        funcp->slow(true);
        m_topScopep->addActivep(funcp);
        UINFO(5, "  Newfunc " << funcp << endl);
        return funcp;
    }
    void callCFuncSub(AstCFunc* basep, AstCFunc* funcp, AstIntfRef* irp) {
        AstCCall* callp = new AstCCall(funcp->fileline(), funcp);
        if (irp) {
            callp->argTypes("tracep, VLT_TRACE_SCOPE_INTERFACE");
            callp->addArgsp(irp->unlinkFrBack());
        } else {
            callp->argTypes("tracep");
        }
        basep->addStmtsp(callp);
    }
    AstCFunc* newCFuncSub(AstCFunc* basep) {
        const string name = "traceInitSub" + cvtToStr(m_funcNum++);
        AstCFunc* const funcp = newCFunc(AstCFuncType::TRACE_INIT_SUB, name);
        if (!m_interface) callCFuncSub(basep, funcp, nullptr);
        return funcp;
    }

    std::string getScopeChar(VltTraceScope sct) { return std::string(1, (char)(0x80 + sct)); }

    void addTraceDecl(const VNumRange& arrayRange,
                      int widthOverride) {  // If !=0, is packed struct/array where basicp size
                                            // misreflects one element
        VNumRange bitRange;
        if (widthOverride) {
            bitRange = VNumRange{widthOverride - 1, 0};
        } else if (const AstBasicDType* const bdtypep = m_traValuep->dtypep()->basicp()) {
            bitRange = bdtypep->nrange();
        }
        AstTraceDecl* const declp
            = new AstTraceDecl(m_traVscp->fileline(), m_traShowname, m_traVscp->varp(),
                               m_traValuep->cloneTree(true), bitRange, arrayRange, m_interface);
        UINFO(9, "Decl " << declp << endl);

        if (!m_interface && v3Global.opt.outputSplitCTrace()
            && m_initSubStmts > v3Global.opt.outputSplitCTrace()) {
            m_initSubFuncp = newCFuncSub(m_initFuncp);
            m_initSubStmts = 0;
        }

        m_initSubFuncp->addStmtsp(declp);
        m_initSubStmts += EmitCBaseCounterVisitor(declp).count();
    }
    void addIgnore(const char* why) {
        ++m_statIgnSigs;
        m_initSubFuncp->addStmtsp(new AstComment(
            m_traVscp->fileline(), "Tracing: " + m_traShowname + " // Ignored: " + why, true));
    }

    // VISITORS
    virtual void visit(AstTopScope* nodep) override {
        m_topScopep = nodep->scopep();
        // Create the trace init function
        m_initFuncp = newCFunc(AstCFuncType::TRACE_INIT, "traceInitTop");
        // Create initial sub function
        m_initSubFuncp = newCFuncSub(m_initFuncp);
        // And find variables
        iterateChildren(nodep);
    }
    virtual void visit(AstScope* nodep) override {
        AstCell* const cellp = VN_CAST(nodep->aboveCellp(), Cell);
        if (cellp && VN_IS(cellp->modp(), Iface)) {
            AstCFunc* const origSubFunc = m_initSubFuncp;
            int origSubStmts = m_initSubStmts;
            {
                m_interface = true;
                m_initSubFuncp = newCFuncSub(origSubFunc);
                string scopeName = nodep->prettyName();
                const size_t lastDot = scopeName.find_last_of('.');
                UASSERT_OBJ(lastDot != string::npos, nodep,
                            "Expected an interface scope name to have at least one dot");
                scopeName = scopeName.substr(0, lastDot + 1);
                const size_t scopeLen = scopeName.length();

                AstIntfRef* nextIrp = cellp->intfRefp();
                // While instead of for loop because interface references will
                // be unlinked as we go
                while (nextIrp) {
                    AstIntfRef* const irp = nextIrp;
                    nextIrp = VN_CAST(irp->nextp(), IntfRef);

                    const string irpName = irp->prettyName();
                    if (scopeLen > irpName.length()) continue;
                    const string intfScopeName = irpName.substr(0, scopeLen);
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
    virtual void visit(AstVarScope* nodep) override {
        iterateChildren(nodep);
        // Prefilter - things that get through this if will either get
        // traced or get a comment as to why not traced.
        // Generally this equation doesn't need updating, instead use
        // varp->isTrace() and/or vscIgnoreTrace.
        if ((!nodep->varp()->isTemp() || nodep->varp()->isTrace())
            && !nodep->varp()->isClassMember() && !nodep->varp()->isFuncLocal()) {
            UINFO(5, "    vsc " << nodep << endl);
            const AstVar* const varp = nodep->varp();
            const AstScope* const scopep = nodep->scopep();
            // Compute show name
            // This code assumes SPTRACEVCDC_VERSION >= 1330;
            // it uses spaces to separate hierarchy components.
            if (m_interface) {
                m_traShowname = AstNode::vcdName(varp->name());
            } else {
                m_traShowname = AstNode::vcdName(scopep->name() + " " + varp->name());
                if (m_traShowname.substr(0, 4) == "TOP ") m_traShowname.erase(0, 4);
            }
            UASSERT_OBJ(m_initSubFuncp, nodep, "nullptr");

            m_traVscp = nodep;
            if (const char* const ignoreReasonp = vscIgnoreTrace(nodep)) {
                addIgnore(ignoreReasonp);
            } else {
                ++m_statSigs;
                if (nodep->valuep()) {
                    m_traValuep = nodep->valuep()->cloneTree(true);
                } else {
                    m_traValuep = new AstVarRef(nodep->fileline(), nodep, VAccess::READ);
                }
                // Recurse into data type of the signal; the visitors will call addTraceDecl()
                iterate(varp->dtypep()->skipRefToEnump());
                // Cleanup
                if (m_traValuep) VL_DO_CLEAR(m_traValuep->deleteTree(), m_traValuep = nullptr);
            }
            m_traVscp = nullptr;
            m_traShowname = "";
        }
    }
    // VISITORS - Data types when tracing
    virtual void visit(AstConstDType* nodep) override {
        if (m_traVscp) iterate(nodep->subDTypep()->skipRefToEnump());
    }
    virtual void visit(AstRefDType* nodep) override {
        if (m_traVscp) iterate(nodep->subDTypep()->skipRefToEnump());
    }
    virtual void visit(AstUnpackArrayDType* nodep) override {
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
                AstNodeDType* const subtypep = nodep->subDTypep()->skipRefToEnump();
                for (int i = nodep->lo(); i <= nodep->hi(); ++i) {
                    VL_RESTORER(m_traShowname);
                    VL_RESTORER(m_traValuep);
                    {
                        m_traShowname += string("(") + cvtToStr(i) + string(")");
                        m_traValuep = new AstArraySel(
                            nodep->fileline(), m_traValuep->cloneTree(true), i - nodep->lo());

                        m_traValuep->dtypep(subtypep);
                        iterate(subtypep);
                        VL_DO_CLEAR(m_traValuep->deleteTree(), m_traValuep = nullptr);
                    }
                }
            }
        }
    }
    virtual void visit(AstPackArrayDType* nodep) override {
        if (m_traVscp) {
            if (!v3Global.opt.traceStructs()) {
                // Everything downstream is packed, so deal with as one trace unit.
                // This may not be the nicest for user presentation, but is
                // a much faster way to trace
                addTraceDecl(VNumRange(), nodep->width());
            } else {
                AstNodeDType* const subtypep = nodep->subDTypep()->skipRefToEnump();
                for (int i = nodep->lo(); i <= nodep->hi(); ++i) {
                    VL_RESTORER(m_traShowname);
                    VL_RESTORER(m_traValuep);
                    {
                        m_traShowname += string("(") + cvtToStr(i) + string(")");
                        m_traValuep
                            = new AstSel(nodep->fileline(), m_traValuep->cloneTree(true),
                                         (i - nodep->lo()) * subtypep->width(), subtypep->width());
                        m_traValuep->dtypep(subtypep);
                        iterate(subtypep);
                        VL_DO_CLEAR(m_traValuep->deleteTree(), m_traValuep = nullptr);
                    }
                }
            }
        }
    }
    virtual void visit(AstNodeUOrStructDType* nodep) override {
        if (m_traVscp) {
            if (nodep->packed() && !v3Global.opt.traceStructs()) {
                // Everything downstream is packed, so deal with as one trace unit
                // This may not be the nicest for user presentation, but is
                // a much faster way to trace
                addTraceDecl(VNumRange(), nodep->width());
            } else if (!nodep->packed()) {
                addIgnore("Unsupported: Unpacked struct/union");
            } else {
                for (const AstMemberDType* itemp = nodep->membersp(); itemp;
                     itemp = VN_CAST_CONST(itemp->nextp(), MemberDType)) {
                    AstNodeDType* const subtypep = itemp->subDTypep()->skipRefToEnump();
                    VL_RESTORER(m_traShowname);
                    VL_RESTORER(m_traValuep);
                    {
                        if (VN_IS(nodep, StructDType)) {
                            // Mark scope as a struct by setting the last char to 0x80 + the
                            // fstScopeType
                            m_traShowname += getScopeChar(VLT_TRACE_SCOPE_STRUCT) + " "
                                             + itemp->prettyName();

                            m_traValuep
                                = new AstSel(nodep->fileline(), m_traValuep->cloneTree(true),
                                             itemp->lsb(), subtypep->width());
                            m_traValuep->dtypep(subtypep);
                            iterate(subtypep);
                            VL_DO_CLEAR(m_traValuep->deleteTree(), m_traValuep = nullptr);
                        } else {  // Else union, replicate fields
                            m_traShowname
                                += getScopeChar(VLT_TRACE_SCOPE_UNION) + " " + itemp->prettyName();
                            iterate(subtypep);
                        }
                    }
                }
            }
        }
    }
    virtual void visit(AstBasicDType* nodep) override {
        if (m_traVscp) {
            if (nodep->isString()) {
                addIgnore("Unsupported: strings");
            } else {
                addTraceDecl(VNumRange(), 0);
            }
        }
    }
    virtual void visit(AstEnumDType* nodep) override { iterate(nodep->skipRefp()); }
    virtual void visit(AstNodeDType*) override {
        // Note more specific dtypes above
        if (!m_traVscp) return;
        addIgnore("Unsupported: data type");
    }

    //--------------------
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit TraceDeclVisitor(AstNetlist* nodep) { iterate(nodep); }
    virtual ~TraceDeclVisitor() override {
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
