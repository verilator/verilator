// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Waves tracing
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
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

#include "V3TraceDecl.h"

#include "verilated_trace_defs.h"  // For VLT_TRACE_SCOPE_*

#include "V3Config.h"
#include "V3EmitCBase.h"
#include "V3Global.h"
#include "V3Stats.h"

#include <algorithm>
#include <functional>
#include <limits>
#include <vector>

//######################################################################
// Utility class to emit path adjustments

class PathAdjustor final {
    FileLine* const m_flp;  // FileLine used for created nodes
    std::function<void(AstNodeStmt*)> m_emit;  // Function called with adjustment statements
    std::vector<std::string> m_stack{""};  // Stack of current paths

    static constexpr char SEPARATOR = ' ';

public:
    explicit PathAdjustor(FileLine* flp, std::function<void(AstNodeStmt*)> emit)
        : m_flp{flp}
        , m_emit{emit} {}

    // Emit Prefix adjustments until the current path is 'newPath'
    void adjust(const string& newPath) {
        // Move up to enclosing path
        unsigned toPop = 0;
        while (!VString::startsWith(newPath, m_stack.back())) {
            ++toPop;
            m_stack.pop_back();
        }
        if (toPop) m_emit(new AstTracePopNamePrefix{m_flp, toPop});
        // Move down, one path element at a time
        if (newPath != m_stack.back()) {
            const string& extraPrefix = newPath.substr(m_stack.back().size());
            size_t begin = 0;
            while (true) {
                const size_t end = extraPrefix.find(SEPARATOR, begin);
                if (end == string::npos) break;
                const string& extra = extraPrefix.substr(begin, end + 1 - begin);
                m_emit(new AstTracePushNamePrefix{m_flp, extra});
                m_stack.push_back(m_stack.back() + extra);
                begin = end + 1;
            }
            const string& extra = extraPrefix.substr(begin);
            if (!extra.empty()) {
                m_emit(new AstTracePushNamePrefix{m_flp, extra + SEPARATOR});
                m_stack.push_back(m_stack.back() + extra);
            }
        }
    }

    // Emit Prefix adjustments to unwind the path back to its original state
    void unwind() {
        const unsigned toPop = m_stack.size() - 1;
        if (toPop) m_emit(new AstTracePopNamePrefix{m_flp, toPop});
    }
};

//######################################################################
// TraceDecl state, as a visitor of each AstNode

class TraceDeclVisitor final : public EmitCBaseVisitor {
private:
    // NODE STATE

    // STATE
    AstTopScope* const m_topScopep;  // The singleton AstTopScope
    const AstScope* m_currScopep = nullptr;  // Current scope being visited

    std::vector<AstCFunc*> m_topFuncps;  // Top level trace initialization functions
    std::vector<AstCFunc*> m_subFuncps;  // Trace sub functions for this scope
    int m_topFuncSize = 0;  // Size of the top function currently being built
    int m_subFuncSize = 0;  // Size of the sub function currently being built
    const int m_funcSizeLimit  // Maximum size of a function
        = v3Global.opt.outputSplitCTrace() ? v3Global.opt.outputSplitCTrace()
                                           : std::numeric_limits<int>::max();
    // Trace init sub functions to invoke for path names in the hierarchy. Note path names and
    // AstScope instances are not one to one due to the presence of AstIntfRef.
    std::map<std::string, std::vector<AstCFunc*>> m_scopeSubFuncps;

    struct Signal final {
        AstVarScope* m_vscp;  // AstVarScope being traced (non const to allow copy during sorting)
        std::string m_path;  // Path to enclosing module in hierarchy
        std::string m_name;  // Name of signal
        explicit Signal(AstVarScope* vscp)
            : m_vscp{vscp} {
            // Compute path in hierarchy and signal name
            const string& vcdName = AstNode::vcdName(vscp->varp()->name());
            const size_t pos = vcdName.rfind(' ');
            const size_t pathLen = pos == string::npos ? 0 : pos + 1;
            m_path = vcdName.substr(0, pathLen);
            m_name = vcdName.substr(pathLen);
        }
    };
    std::vector<Signal> m_signals;  // Signals under current scope
    AstVarScope* m_traVscp = nullptr;  // Current AstVarScope we are constructing AstTraceDecls for
    AstNode* m_traValuep = nullptr;  // Value expression for current signal
    string m_traName;  // Name component for current signal

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
        } else {
            const string prettyName = varp->prettyName();
            if (!v3Global.opt.traceUnderscore()) {
                if (!prettyName.empty() && prettyName[0] == '_') return "Leading underscore";
                if (prettyName.find("._") != string::npos) return "Inlined leading underscore";
            }
            if (!V3Config::getScopeTraceOn(prettyName)) return "Vlt scope trace_off";
        }
        return nullptr;
    }

    AstCFunc* newCFunc(FileLine* flp, const string& name) {
        AstScope* const topScopep = m_topScopep->scopep();
        AstCFunc* const funcp = new AstCFunc{flp, name, topScopep};
        funcp->argTypes(v3Global.opt.traceClassBase() + "* tracep");
        funcp->isTrace(true);
        funcp->isStatic(false);
        funcp->isLoose(true);
        funcp->slow(true);
        topScopep->addActivep(funcp);
        return funcp;
    }

    void addToTopFunc(AstNodeStmt* stmtp) {
        if (m_topFuncSize > m_funcSizeLimit || m_topFuncps.empty()) {
            m_topFuncSize = 0;
            //
            const string n = cvtToStr(m_topFuncps.size());
            const string name{"trace_init_top__" + n};
            AstCFunc* const funcp = newCFunc(m_topScopep->fileline(), name);
            m_topFuncps.push_back(funcp);
        }
        m_topFuncps.back()->addStmtsp(stmtp);
        m_topFuncSize += stmtp->nodeCount();
    }

    void addToSubFunc(AstNodeStmt* stmtp) {
        if (m_subFuncSize > m_funcSizeLimit || m_subFuncps.empty()) {
            m_subFuncSize = 0;
            //
            FileLine* const flp = m_currScopep->fileline();
            const string n = cvtToStr(m_subFuncps.size());
            const string name{"trace_init_sub__" + m_currScopep->nameDotless() + "__" + n};
            AstCFunc* const funcp = newCFunc(flp, name);
            funcp->addInitsp(new AstCStmt{flp, "const int c = vlSymsp->__Vm_baseCode;\n"});
            m_subFuncps.push_back(funcp);
        }
        m_subFuncps.back()->addStmtsp(stmtp);
        m_subFuncSize += stmtp->nodeCount();
    }

    std::string getScopeChar(VltTraceScope sct) {
        return std::string(1, static_cast<char>(0x80 + sct));
    }

    std::string addAboveInterface(const std::string& scopeName) {
        std::string out;
        // Hierarchical interfaces didn't know if interface vs module
        // above them. so convert a scope string to have the interface character.
        // Uses list of scopes to see what's an interface above.
        size_t begin = 0;
        while (true) {
            const size_t end = scopeName.find(' ', begin);
            if (end == string::npos) break;
            const string& extra = scopeName.substr(begin, end - begin);
            out += extra;
            if (m_scopeSubFuncps.count(out + getScopeChar(VLT_TRACE_SCOPE_INTERFACE) + " ")) {
                out += getScopeChar(VLT_TRACE_SCOPE_INTERFACE) + " ";
            } else {
                out += " ";
            }
            begin = end + 1;
        }
        return out;
    }

    void addTraceDecl(const VNumRange& arrayRange,
                      int widthOverride) {  // If !=0, is packed struct/array where basicp size
                                            // misreflects one element
        VNumRange bitRange;
        if (widthOverride) {
            bitRange = VNumRange{widthOverride - 1, 0};
        } else if (const AstBasicDType* const bdtypep = m_traValuep->dtypep()->basicp()) {
            bitRange = bdtypep->nrange();
        }
        auto* const newp
            = new AstTraceDecl{m_traVscp->fileline(),         m_traName, m_traVscp->varp(),
                               m_traValuep->cloneTree(false), bitRange,  arrayRange};
        addToSubFunc(newp);
    }

    void addIgnore(const char* why) {
        ++m_statIgnSigs;
        addToSubFunc(new AstComment{m_traVscp->fileline(),
                                    "Tracing: " + m_traName + " // Ignored: " + why, true});
    }

    // VISITORS
    virtual void visit(AstScope* nodep) override {
        UASSERT_OBJ(!m_currScopep, nodep, "Should not nest");
        UASSERT_OBJ(m_subFuncps.empty(), nodep, "Should not nest");
        UASSERT_OBJ(m_signals.empty(), nodep, "Should not nest");
        UASSERT_OBJ(!m_traVscp, nodep, "Should not nest");
        UASSERT_OBJ(m_traName.empty(), nodep, "Should not nest");

        VL_RESTORER(m_currScopep);
        m_currScopep = nodep;

        // Gather all signals under this AstScope
        iterateChildrenConst(nodep);

        // If nothing to trace in this scope, then job done
        if (m_signals.empty()) return;

        // Sort signals, first by enclosing instance, then by source location, then by name
        std::stable_sort(m_signals.begin(), m_signals.end(), [](const Signal& a, const Signal& b) {
            if (const int cmp = a.m_path.compare(b.m_path)) return cmp < 0;
            const FileLine* const aflp = a.m_vscp->fileline();
            const FileLine* const bflp = b.m_vscp->fileline();
            if (const int cmp = aflp->operatorCompare(*bflp)) return cmp < 0;
            return a.m_name < b.m_name;
        });

        // Build trace initialization functions for this AstScope
        FileLine* const flp = nodep->fileline();
        PathAdjustor pathAdjustor{flp, [&](AstNodeStmt* stmtp) { addToSubFunc(stmtp); }};
        for (const Signal& signal : m_signals) {
            // Adjust name prefix based on path in hierarchy
            pathAdjustor.adjust(signal.m_path);

            // Build AstTraceDecl for this signal
            m_traVscp = signal.m_vscp;
            m_traName = signal.m_name;
            if (const char* const ignoreReasonp = vscIgnoreTrace(m_traVscp)) {
                addIgnore(ignoreReasonp);
            } else {
                ++m_statSigs;
                m_traValuep = new AstVarRef{m_traVscp->fileline(), m_traVscp, VAccess::READ};
                // Recurse into data type of the signal. The visit methods will add AstTraceDecls.
                iterate(m_traVscp->varp()->dtypep()->skipRefToEnump());
                // Cleanup
                if (m_traValuep) VL_DO_DANGLING(m_traValuep->deleteTree(), m_traValuep);
            }
        }
        pathAdjustor.unwind();
        m_traVscp = nullptr;
        m_traName.clear();
        UASSERT_OBJ(!m_traValuep, nodep, "Should have been deleted");
        m_signals.clear();

        // Add sub functions to m_scopeSubFuncps
        const AstCell* const cellp = nodep->aboveCellp();
        if (cellp && VN_IS(cellp->modp(), Iface)) {
            string scopeName = nodep->prettyName();
            const size_t lastDot = scopeName.find_last_of('.');
            UASSERT_OBJ(lastDot != string::npos, nodep,
                        "Expected an interface scope name to have at least one dot");
            scopeName = scopeName.substr(0, lastDot + 1);
            const size_t scopeLen = scopeName.length();

            UASSERT_OBJ(cellp->intfRefp(), cellp, "Interface without tracing reference");
            for (AstIntfRef *irp = cellp->intfRefp(), *nextIrp; irp; irp = nextIrp) {
                nextIrp = VN_AS(irp->nextp(), IntfRef);

                const string irpName = irp->prettyName();
                if (scopeLen > irpName.length()) continue;
                const string intfScopeName = irpName.substr(0, scopeLen);
                if (scopeName != intfScopeName) continue;

                string iscopeName = AstNode::vcdName(irp->name());
                if (iscopeName.substr(0, 4) == "TOP ") iscopeName.erase(0, 4);
                // Note this insert doesn't know what above is interfaces.
                // Perhaps all scopes should be changed to include the VLT_TRACE_SCOPE characters.
                // Instead we fix up when printing m_scopeSubFuncps
                iscopeName += getScopeChar(VLT_TRACE_SCOPE_INTERFACE) + ' ';
                m_scopeSubFuncps.emplace(iscopeName, m_subFuncps);

                VL_DO_DANGLING(irp->unlinkFrBack(), irp);
            }

            m_subFuncps.clear();
        } else {
            string scopeName = AstNode::vcdName(nodep->name()) + ' ';
            if (VString::startsWith(scopeName, "TOP ")) scopeName.erase(0, 4);
            m_scopeSubFuncps.emplace(scopeName, std::move(m_subFuncps));
        }
    }
    virtual void visit(AstVarScope* nodep) override {
        UASSERT_OBJ(m_currScopep, nodep, "AstVarScope not under AstScope");

        // Prefilter - things that get added to m_vscps will either get traced or get a comment as
        // to why they are not traced. Generally these conditions doesn't need updating, instead
        // use varp->isTrace() and/or vscIgnoreTrace.
        if (nodep->varp()->isTemp() && !nodep->varp()->isTrace()) return;
        if (nodep->varp()->isClassMember()) return;
        if (nodep->varp()->isFuncLocal()) return;

        // Add to traced signal list
        m_signals.emplace_back(nodep);
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
                FileLine* const flp = nodep->fileline();
                AstNodeDType* const subtypep = nodep->subDTypep()->skipRefToEnump();
                VL_RESTORER(m_traName);
                addToSubFunc(new AstTracePushNamePrefix{flp, m_traName});
                for (int i = nodep->lo(); i <= nodep->hi(); ++i) {
                    VL_RESTORER(m_traValuep);
                    m_traName = std::string{"["} + cvtToStr(i) + std::string{"]"};
                    m_traValuep = m_traValuep->cloneTree(false);
                    m_traValuep = new AstArraySel{flp, m_traValuep, i - nodep->lo()};
                    m_traValuep->dtypep(subtypep);
                    iterate(subtypep);
                    VL_DO_CLEAR(m_traValuep->deleteTree(), m_traValuep = nullptr);
                }
                addToSubFunc(new AstTracePopNamePrefix{flp, 1});
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
                FileLine* const flp = nodep->fileline();
                AstNodeDType* const subtypep = nodep->subDTypep()->skipRefToEnump();
                VL_RESTORER(m_traName);
                addToSubFunc(new AstTracePushNamePrefix{flp, m_traName});
                for (int i = nodep->lo(); i <= nodep->hi(); ++i) {
                    VL_RESTORER(m_traValuep);
                    m_traName = std::string{"["} + cvtToStr(i) + std::string{"]"};
                    const int lsb = (i - nodep->lo()) * subtypep->width();
                    m_traValuep = m_traValuep->cloneTree(false);
                    m_traValuep = new AstSel{flp, m_traValuep, lsb, subtypep->width()};
                    m_traValuep->dtypep(subtypep);
                    iterate(subtypep);
                    VL_DO_CLEAR(m_traValuep->deleteTree(), m_traValuep = nullptr);
                }
                addToSubFunc(new AstTracePopNamePrefix{flp, 1});
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
                FileLine* const flp = nodep->fileline();
                const bool isStruct = VN_IS(nodep, StructDType);  // Otherwise union
                VL_RESTORER(m_traName);
                string prefix{m_traName};
                prefix += isStruct ? getScopeChar(VLT_TRACE_SCOPE_STRUCT)  // Mark scope type
                                   : getScopeChar(VLT_TRACE_SCOPE_UNION);
                addToSubFunc(new AstTracePushNamePrefix{flp, prefix + ' '});
                for (const AstMemberDType* itemp = nodep->membersp(); itemp;
                     itemp = VN_AS(itemp->nextp(), MemberDType)) {
                    AstNodeDType* const subtypep = itemp->subDTypep()->skipRefToEnump();
                    m_traName = itemp->prettyName();
                    if (isStruct) {
                        VL_RESTORER(m_traValuep);
                        m_traValuep = m_traValuep->cloneTree(false);
                        m_traValuep
                            = new AstSel{flp, m_traValuep, itemp->lsb(), subtypep->width()};
                        m_traValuep->dtypep(subtypep);
                        iterate(subtypep);
                        VL_DO_CLEAR(m_traValuep->deleteTree(), m_traValuep = nullptr);
                    } else {  // Else union, replicate fields
                        iterate(subtypep);
                    }
                }
                addToSubFunc(new AstTracePopNamePrefix{flp, 1});
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
    explicit TraceDeclVisitor(AstNetlist* nodep)
        : m_topScopep{nodep->topScopep()} {
        FileLine* const flp = nodep->fileline();

        // Iterate modules to build per scope initialization sub functions
        iterateAndNextConstNull(nodep->modulesp());
        UASSERT_OBJ(m_subFuncps.empty(), nodep, "Should have been emptied");

        // Build top level trace initialization functions
        PathAdjustor pathAdjustor{flp, [&](AstNodeStmt* stmtp) { addToTopFunc(stmtp); }};
        for (const auto& item : m_scopeSubFuncps) {
            const std::string scopeName = item.first;
            const std::string scopeNameInterfaced = addAboveInterface(scopeName);
            // Adjust name prefix based on path in hierarchy
            pathAdjustor.adjust(scopeNameInterfaced);
            // Call all sub functions for this path
            for (AstCFunc* const subFuncp : item.second) {
                AstCCall* const callp = new AstCCall{flp, subFuncp};
                callp->argTypes("tracep");
                addToTopFunc(callp);
            }
        }
        pathAdjustor.unwind();

        // Ensure a top function exists, in case there was nothing to trace at all
        if (m_topFuncps.empty()) addToTopFunc(new AstComment{flp, "Empty"});

        // Create single top level function, if more than one exists
        if (m_topFuncps.size() > 1) {
            AstCFunc* const topFuncp = newCFunc(flp, "");
            for (AstCFunc* funcp : m_topFuncps) {
                AstCCall* const callp = new AstCCall{flp, funcp};
                callp->argTypes("tracep");
                topFuncp->addStmtsp(callp);
            }
            m_topFuncps.clear();
            m_topFuncps.push_back(topFuncp);
        }

        // Set name of top level function
        AstCFunc* const topFuncp = m_topFuncps.front();
        topFuncp->name("trace_init_top");
    }
    virtual ~TraceDeclVisitor() override {
        V3Stats::addStat("Tracing, Traced signals", m_statSigs);
        V3Stats::addStat("Tracing, Ignored signals", m_statIgnSigs);
    }
};

//######################################################################
// Trace class functions

void V3TraceDecl::traceDeclAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { TraceDeclVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("tracedecl", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
