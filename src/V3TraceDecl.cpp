// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Waves tracing
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
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

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3TraceDecl.h"

#include "V3Config.h"
#include "V3EmitCBase.h"
#include "V3Stats.h"

#include <functional>
#include <limits>
#include <tuple>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

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
        while (toPop--) m_emit(new AstTracePopPrefix{m_flp});
        // Move down, one path element at a time
        if (newPath != m_stack.back()) {
            const string& extraPrefix = newPath.substr(m_stack.back().size());
            size_t begin = 0;
            while (true) {
                const size_t end = extraPrefix.find(SEPARATOR, begin);
                if (end == string::npos) break;
                const string& extra = extraPrefix.substr(begin, end - begin);
                m_emit(new AstTracePushPrefix{m_flp, extra, VTracePrefixType::SCOPE_MODULE});
                m_stack.push_back(m_stack.back() + extra + SEPARATOR);
                begin = end + 1;
            }
            const string& extra = extraPrefix.substr(begin);
            if (!extra.empty()) {
                m_emit(new AstTracePushPrefix{m_flp, extra, VTracePrefixType::SCOPE_MODULE});
                m_stack.push_back(m_stack.back() + extra);
            }
        }
    }

    // Emit Prefix adjustments to unwind the path back to its original state
    void unwind() {
        unsigned toPop = m_stack.size() - 1;
        while (toPop--) m_emit(new AstTracePopPrefix{m_flp});
    }
};

//######################################################################
// TraceDecl state, as a visitor of each AstNode

class TraceDeclVisitor final : public VNVisitor {
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
    // Trace init functions to for each scope
    std::unordered_map<const AstScope*, std::vector<AstCFunc*>> m_scopeInitFuncps;
    // Map from hierarchical scope name to the corresponding AstScope. Note that
    // this is a many-to-one mapping for interfaces, due to interface refs.
    std::unordered_map<std::string, const AstScope*> m_pathToScopep;
    // Cell initialization placeholders:
    // (parent scope, cell under parent scope, statement)
    std::vector<std::tuple<AstScope*, AstCell*, AstNodeStmt*>> m_cellInitPlaceholders;
    // Interface refs initialization placeholders:
    // (Interface ref variable, placeholder statement)
    std::vector<std::tuple<AstVarScope*, AstNodeStmt*>> m_ifaceRefInitPlaceholders;

    // A trace entry under a scope is either:
    // - A variable (including interface references)
    // - A sub scope (stored as the cell corresponding to the sub scope)
    // Note: members are non-const to allow copy during sorting
    class TraceEntry final {
        // AstVarScope under scope being traced
        AstVarScope* m_vscp{nullptr};
        // Sub scope (as AstCell) under scope being traced
        AstCell* m_cellp{nullptr};
        // Path to enclosing module in original hierarchy (non-trivail due to inlining)
        std::string m_path;
        // Name of signal/subscope
        std::string m_name;

        void init(const std::string& name) {
            // Compute path in hierarchy and item name
            const std::string& vcdName = AstNode::vcdName(name);
            const size_t pos = vcdName.rfind(' ');
            const size_t pathLen = pos == std::string::npos ? 0 : pos + 1;
            m_path = vcdName.substr(0, pathLen);
            m_name = vcdName.substr(pathLen);
        }

    public:
        explicit TraceEntry(AstVarScope* vscp)
            : m_vscp{vscp} {
            init(vscp->varp()->name());
        }
        explicit TraceEntry(AstCell* cellp)
            : m_cellp{cellp} {
            init(cellp->name());
        }

        AstVarScope* vscp() const { return m_vscp; }
        AstCell* cellp() const { return m_cellp; }
        const std::string& path() const { return m_path; }
        const std::string& name() const { return m_name; }
        FileLine& fileline() const { return m_vscp ? *m_vscp->fileline() : *m_cellp->fileline(); }
    };
    std::vector<TraceEntry> m_entries;  // Trace entries under current scope
    AstVarScope* m_traVscp = nullptr;  // Current AstVarScope we are constructing AstTraceDecls for
    AstNodeExpr* m_traValuep = nullptr;  // Value expression for current signal
    string m_traName;  // Name component for current signal

    VDouble0 m_statSigs;  // Statistic tracking
    VDouble0 m_statIgnSigs;  // Statistic tracking

    // METHODS

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
        topScopep->addBlocksp(funcp);
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
        std::string cmt = "Tracing: "s + m_traName + " // Ignored: " + why;
        if (debug() > 3 && m_traVscp) std::cout << "- " << m_traVscp->fileline() << cmt << endl;
    }

    void fixupPlaceholder(const std::string& path, AstNodeStmt* placeholderp) {
        // Find the scope for the path. As we are working based on cell names,
        // it is possible there is no corresponding scope (e.g.: for an empty
        // module).
        const auto it = m_pathToScopep.find(path);
        if (it != m_pathToScopep.end()) {
            const AstScope* const scopep = it->second;
            FileLine* const flp = placeholderp->fileline();

            // Pick up the last path element. The prefixes have already been pushed
            // when building the initialization functions
            const size_t pos = path.rfind('.');
            const std::string name = path.substr(pos == string::npos ? 0 : pos + 1);

            // Compute the type of the scope being fixed up
            const AstCell* const cellp = scopep->aboveCellp();
            const VTracePrefixType scopeType
                = cellp ? (VN_IS((cellp->modp()), Iface) ? VTracePrefixType::SCOPE_INTERFACE
                                                         : VTracePrefixType::SCOPE_MODULE)
                        : VTracePrefixType::SCOPE_MODULE;

            // Push the scope prefix
            AstNodeStmt* const pushp = new AstTracePushPrefix{flp, name, scopeType};

            // Call the initialization functions for the scope
            for (AstCFunc* const subFuncp : m_scopeInitFuncps.at(scopep)) {
                AstCCall* const callp = new AstCCall{flp, subFuncp};
                callp->dtypeSetVoid();
                callp->argTypes("tracep");
                pushp->addNext(callp->makeStmt());
            }

            // Pop the scope prefix
            pushp->addNext(new AstTracePopPrefix{flp});

            // Add after the placeholder
            placeholderp->addNextHere(pushp);
        }
        // Delete the placeholder
        placeholderp->unlinkFrBack();
        VL_DO_DANGLING(placeholderp->deleteTree(), placeholderp);
    }

    void fixupPlaceholders() {
        // Fix up cell initialization placehodlers
        for (const auto& item : m_cellInitPlaceholders) {
            const AstScope* const parentp = std::get<0>(item);
            const AstCell* const cellp = std::get<1>(item);
            AstNodeStmt* const placeholderp = std::get<2>(item);
            const std::string path = AstNode::prettyName(parentp->name() + "." + cellp->name());
            fixupPlaceholder(path, placeholderp);
        }

        // Fix up interface reference initialization placeholders
        for (const auto& item : m_ifaceRefInitPlaceholders) {
            const AstVarScope* const vscp = std::get<0>(item);
            AstNodeStmt* const placeholderp = std::get<1>(item);
            const std::string path = vscp->prettyName();
            fixupPlaceholder(path, placeholderp);
        }
    }

    void removeRedundantPrefixPushPop() {
        for (const auto& pair : m_scopeInitFuncps) {
            for (AstCFunc* const funcp : pair.second) {
                AstNode* prevp = nullptr;
                AstNode* currp = funcp->stmtsp();
                while (true) {
                    AstNode* const nextp = currp->nextp();
                    if (VN_IS(prevp, TracePushPrefix) && VN_IS(currp, TracePopPrefix)) {
                        VL_DO_DANGLING(prevp->unlinkFrBack()->deleteTree(), prevp);
                        VL_DO_DANGLING(currp->unlinkFrBack()->deleteTree(), currp);
                    }
                    if (!nextp) break;
                    prevp = nextp->backp();
                    currp = nextp;
                }
            }
        }
    }

    // VISITORS
    void visit(AstScope* nodep) override {
        UASSERT_OBJ(!m_currScopep, nodep, "Should not nest");
        UASSERT_OBJ(m_subFuncps.empty(), nodep, "Should not nest");
        UASSERT_OBJ(m_entries.empty(), nodep, "Should not nest");
        UASSERT_OBJ(!m_traVscp, nodep, "Should not nest");
        UASSERT_OBJ(!m_traValuep, nodep, "Should not nest");
        UASSERT_OBJ(m_traName.empty(), nodep, "Should not nest");

        VL_RESTORER(m_currScopep);
        m_currScopep = nodep;

        // Gather signals under this scope
        iterateChildrenConst(nodep);

        // Gather cells under this scope
        for (AstNode* stmtp = nodep->modp()->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstCell* const cellp = VN_CAST(stmtp, Cell)) { m_entries.emplace_back(cellp); }
        }

        if (!m_entries.empty()) {
            // Sort trace entries, first by enclosing instance (necessary for
            // single traversal of hierarchy during initialization), then by
            // source location, then by name.
            std::stable_sort(m_entries.begin(), m_entries.end(),
                             [](const TraceEntry& a, const TraceEntry& b) {
                                 if (const int cmp = a.path().compare(b.path())) return cmp < 0;
                                 if (const int cmp = a.fileline().operatorCompare(b.fileline()))
                                     return cmp < 0;
                                 return a.name() < b.name();
                             });

            // Build trace initialization functions for this AstScope
            FileLine* const flp = nodep->fileline();
            PathAdjustor pathAdjustor{flp, [&](AstNodeStmt* stmtp) { addToSubFunc(stmtp); }};
            for (const TraceEntry& entry : m_entries) {
                // Adjust name prefix based on path in hierarchy
                pathAdjustor.adjust(entry.path());

                m_traName = entry.name();

                if (AstVarScope* const vscp = entry.vscp()) {
                    // This is a signal: build AstTraceDecl for it
                    m_traVscp = vscp;
                    if (const char* const ignoreReasonp = vscIgnoreTrace(m_traVscp)) {
                        addIgnore(ignoreReasonp);
                    } else {
                        ++m_statSigs;
                        // Create reference to whole signal. We will operate on this during the
                        // traversal.
                        m_traValuep
                            = new AstVarRef{m_traVscp->fileline(), m_traVscp, VAccess::READ};
                        // Recurse into data type of the signal. The visit methods will add
                        // AstTraceDecls.
                        iterate(m_traVscp->varp()->dtypep()->skipRefToEnump());
                        // Delete reference created above. Traversal cloned it as required.
                        if (m_traValuep) {
                            VL_DO_DANGLING(m_traValuep->deleteTree(), m_traValuep);
                            // Note: Sometimes VL_DANGLING is a no-op, but we have assertions
                            // on m_traValuep being nullptr, so make sure it is.
                            m_traValuep = nullptr;
                        }
                    }
                } else {
                    // This is a subscope: insert a placeholder to be fixed up later
                    AstCell* const cellp = entry.cellp();
                    AstNodeStmt* const stmtp = new AstComment{
                        cellp->fileline(), "Cell init for: " + cellp->prettyName()};
                    addToSubFunc(stmtp);
                    m_cellInitPlaceholders.emplace_back(nodep, cellp, stmtp);
                }
            }
            pathAdjustor.unwind();
            m_traVscp = nullptr;
            m_traName.clear();
            UASSERT_OBJ(!m_traValuep, nodep, "Should have been deleted");
            m_entries.clear();
        }

        // Save the initialization functions of this scope
        m_scopeInitFuncps.emplace(nodep, std::move(m_subFuncps));

        // Save the hierarchical name of this scope
        const std::string path = nodep->prettyName();
        m_pathToScopep.emplace(path, nodep);

        // Save the hierarchical names of interface references that reference this scope
        const AstCell* const cellp = nodep->aboveCellp();
        if (cellp && VN_IS(cellp->modp(), Iface)) {
            const size_t lastDot = path.find_last_of('.');
            UASSERT_OBJ(lastDot != string::npos, nodep,
                        "Expected an interface scope name to have at least one dot");
            const std::string parentPath = path.substr(0, lastDot + 1);

            for (AstIntfRef *intfRefp = cellp->intfRefsp(), *nextp; intfRefp; intfRefp = nextp) {
                nextp = VN_AS(intfRefp->nextp(), IntfRef);

                const std::string refName = intfRefp->prettyName();

                // Assume only references under the same parent scope reference
                // the same interface.
                // TODO: This is not actually correct. An interface can propagate
                //       upwards and sideways when passed to a port via a downward
                //       hierarchical reference, which we will miss here.
                if (!VString::startsWith(refName, parentPath)) continue;

                // Save the mapping from the path of the reference to the scope
                m_pathToScopep.emplace(refName, nodep);

                // No more need for AstIntfRef
                intfRefp->unlinkFrBack();
                VL_DO_DANGLING(intfRefp->deleteTree(), intfRefp);
            }
        }
    }
    void visit(AstVarScope* nodep) override {
        UASSERT_OBJ(m_currScopep, nodep, "AstVarScope not under AstScope");

        // Prefilter - things that get added to m_vscps will either get traced or get a comment as
        // to why they are not traced. Generally these conditions doesn't need updating, instead
        // use varp->isTrace() and/or vscIgnoreTrace.
        if (nodep->varp()->isTemp() && !nodep->varp()->isTrace()) return;
        if (nodep->varp()->isClassMember()) return;
        if (nodep->varp()->isFuncLocal()) return;

        // Add to traced signal list
        m_entries.emplace_back(nodep);
    }

    // VISITORS - Data types when tracing
    void visit(AstConstDType* nodep) override {
        if (!m_traVscp) return;
        iterate(nodep->subDTypep()->skipRefToEnump());
    }
    void visit(AstRefDType* nodep) override {
        if (!m_traVscp) return;
        iterate(nodep->subDTypep()->skipRefToEnump());
    }
    void visit(AstIfaceRefDType* nodep) override {
        if (!m_traVscp) return;
        // Insert a placeholder to be fixed up later
        FileLine* const flp = m_traVscp->fileline();
        AstNodeStmt* const stmtp
            = new AstComment{flp, "Interface ref init for: " + m_traVscp->prettyName()};
        addToSubFunc(stmtp);
        m_ifaceRefInitPlaceholders.emplace_back(m_traVscp, stmtp);
    }
    void visit(AstUnpackArrayDType* nodep) override {
        // Note more specific dtypes above
        if (!m_traVscp) return;

        if (static_cast<int>(nodep->arrayUnpackedElements()) > v3Global.opt.traceMaxArray()) {
            addIgnore("Wide memory > --trace-max-array ents");
            return;
        }

        VL_RESTORER(m_traName);
        FileLine* const flp = nodep->fileline();

        addToSubFunc(new AstTracePushPrefix{flp, m_traName, VTracePrefixType::ARRAY_UNPACKED});

        if (VN_IS(nodep->subDTypep()->skipRefToEnump(),
                  BasicDType)  // Nothing lower than this array
            && m_traVscp->dtypep()->skipRefToEnump() == nodep) {  // Nothing above this array
            // Simple 1-D array, use existing V3EmitC runtime loop rather than unrolling
            // This will put "(index)" at end of signal name for us
            if (m_traVscp->dtypep()->skipRefToEnump()->isString()) {
                addIgnore("Unsupported: strings");
            } else {
                m_traName = "";
                addTraceDecl(nodep->declRange(), 0);
            }
        } else {
            AstNodeDType* const subtypep = nodep->subDTypep()->skipRefToEnump();
            for (int i = nodep->lo(); i <= nodep->hi(); ++i) {
                VL_RESTORER(m_traValuep);
                m_traName = '[' + std::to_string(i) + ']';
                m_traValuep = m_traValuep->cloneTree(false);
                m_traValuep = new AstArraySel{flp, m_traValuep, i - nodep->lo()};
                m_traValuep->dtypep(subtypep);
                iterate(subtypep);
                VL_DO_DANGLING(m_traValuep->deleteTree(), m_traValuep);
            }
        }

        addToSubFunc(new AstTracePopPrefix{flp});
    }
    void visit(AstPackArrayDType* nodep) override {
        if (!m_traVscp) return;

        if (!v3Global.opt.traceStructs()) {
            // Everything downstream is packed, so deal with as one trace unit.
            // This may not be the nicest for user presentation, but is
            // a much faster way to trace
            addTraceDecl(VNumRange{}, nodep->width());
            return;
        }

        VL_RESTORER(m_traName);
        FileLine* const flp = nodep->fileline();
        addToSubFunc(new AstTracePushPrefix{flp, m_traName, VTracePrefixType::ARRAY_PACKED});

        AstNodeDType* const subtypep = nodep->subDTypep()->skipRefToEnump();
        for (int i = nodep->lo(); i <= nodep->hi(); ++i) {
            VL_RESTORER(m_traValuep);
            m_traName = '[' + std::to_string(i) + ']';
            const int lsb = (i - nodep->lo()) * subtypep->width();
            m_traValuep = m_traValuep->cloneTree(false);
            m_traValuep = new AstSel{flp, m_traValuep, lsb, subtypep->width()};
            m_traValuep->dtypep(subtypep);
            iterate(subtypep);
            VL_DO_CLEAR(m_traValuep->deleteTree(), m_traValuep = nullptr);
        }

        addToSubFunc(new AstTracePopPrefix{flp});
    }
    void visit(AstStructDType* nodep) override {
        if (!m_traVscp) return;

        if (nodep->packed() && !v3Global.opt.traceStructs()) {
            // Everything downstream is packed, so deal with as one trace unit
            // This may not be the nicest for user presentation, but is
            // a much faster way to trace
            addTraceDecl(VNumRange{}, nodep->width());
            return;
        }

        VL_RESTORER(m_traName);
        FileLine* const flp = nodep->fileline();

        if (!nodep->packed()) {
            addToSubFunc(
                new AstTracePushPrefix{flp, m_traName, VTracePrefixType::STRUCT_UNPACKED});
            for (const AstMemberDType *itemp = nodep->membersp(), *nextp; itemp; itemp = nextp) {
                nextp = VN_AS(itemp->nextp(), MemberDType);
                AstNodeDType* const subtypep = itemp->subDTypep()->skipRefToEnump();
                m_traName = itemp->prettyName();
                VL_RESTORER(m_traValuep);
                m_traValuep = m_traValuep->cloneTree(false);
                m_traValuep = new AstStructSel{flp, m_traValuep, itemp->name()};
                m_traValuep->dtypep(subtypep);
                iterate(subtypep);
                VL_DO_DANGLING(m_traValuep->deleteTree(), m_traValuep);
            }
            addToSubFunc(new AstTracePopPrefix{flp});
        } else {
            addToSubFunc(new AstTracePushPrefix{flp, m_traName, VTracePrefixType::STRUCT_PACKED});
            for (const AstMemberDType *itemp = nodep->membersp(), *nextp; itemp; itemp = nextp) {
                nextp = VN_AS(itemp->nextp(), MemberDType);
                AstNodeDType* const subtypep = itemp->subDTypep()->skipRefToEnump();
                m_traName = itemp->prettyName();
                VL_RESTORER(m_traValuep);
                m_traValuep = m_traValuep->cloneTree(false);
                m_traValuep = new AstSel{flp, m_traValuep, itemp->lsb(), subtypep->width()};
                m_traValuep->dtypep(subtypep);
                iterate(subtypep);
                VL_DO_DANGLING(m_traValuep->deleteTree(), m_traValuep);
            }
            addToSubFunc(new AstTracePopPrefix{flp});
        }
    }
    void visit(AstUnionDType* nodep) override {
        if (!m_traVscp) return;

        if (nodep->packed() && !v3Global.opt.traceStructs()) {
            // Everything downstream is packed, so deal with as one trace unit
            // This may not be the nicest for user presentation, but is
            // a much faster way to trace
            addTraceDecl(VNumRange{}, nodep->width());
            return;
        }

        VL_RESTORER(m_traName);
        FileLine* const flp = nodep->fileline();

        if (!nodep->packed()) {
            addIgnore("Unsupported: Unpacked union");
        } else {
            addToSubFunc(new AstTracePushPrefix{flp, m_traName, VTracePrefixType::UNION_PACKED});
            for (const AstMemberDType *itemp = nodep->membersp(), *nextp; itemp; itemp = nextp) {
                nextp = VN_AS(itemp->nextp(), MemberDType);
                AstNodeDType* const subtypep = itemp->subDTypep()->skipRefToEnump();
                m_traName = itemp->prettyName();
                iterate(subtypep);
            }
            addToSubFunc(new AstTracePopPrefix{flp});
        }
    }
    void visit(AstBasicDType* nodep) override {
        if (!m_traVscp) return;
        if (nodep->isString()) {
            addIgnore("Unsupported: strings");
        } else {
            addTraceDecl(VNumRange{}, 0);
        }
    }
    void visit(AstEnumDType* nodep) override { iterate(nodep->skipRefp()); }
    void visit(AstNodeDType*) override {
        // Note more specific dtypes above
        if (!m_traVscp) return;
        addIgnore("Unsupported: data type");
    }

    //--------------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit TraceDeclVisitor(AstNetlist* nodep)
        : m_topScopep{nodep->topScopep()} {
        FileLine* const flp = nodep->fileline();

        // Iterate modules to build per scope initialization functions
        iterateAndNextConstNull(nodep->modulesp());
        UASSERT_OBJ(m_subFuncps.empty(), nodep, "Should have been emptied");

        // Fix up the placeholders in the initialization functions
        fixupPlaceholders();

        // Now that we have everything ready, remove redundant pushPrefix/popPrefix
        // pairs. While functionally this is not really necessary (the trace files
        // might have some empty scope declarations), we do it to preserve previous
        // behaviour. Note: unfortunately generating these without the redundant
        // push/pop pairs is a bit hard. It is cleaner to remove them.
        removeRedundantPrefixPushPop();

        // Call the initialization functions of the root scope from the top function
        for (AstCFunc* const funcp : m_scopeInitFuncps.at(m_topScopep->scopep())) {
            AstCCall* const callp = new AstCCall{flp, funcp};
            callp->dtypeSetVoid();
            callp->argTypes("tracep");
            addToTopFunc(callp->makeStmt());
        }

        // Ensure a top function exists, in case there was nothing to trace at all
        if (m_topFuncps.empty()) addToTopFunc(new AstComment{flp, "Empty"});

        // Create single top level function, if more than one exists
        if (m_topFuncps.size() > 1) {
            AstCFunc* const topFuncp = newCFunc(flp, "");
            for (AstCFunc* funcp : m_topFuncps) {
                AstCCall* const callp = new AstCCall{flp, funcp};
                callp->dtypeSetVoid();
                callp->argTypes("tracep");
                topFuncp->addStmtsp(callp->makeStmt());
            }
            m_topFuncps.clear();
            m_topFuncps.push_back(topFuncp);
        }

        // Set name of top level function
        AstCFunc* const topFuncp = m_topFuncps.front();
        topFuncp->name("trace_init_top");
    }
    ~TraceDeclVisitor() override {
        V3Stats::addStat("Tracing, Traced signals", m_statSigs);
        V3Stats::addStat("Tracing, Ignored signals", m_statIgnSigs);
    }
};

//######################################################################
// Trace class functions

void V3TraceDecl::traceDeclAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { TraceDeclVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("tracedecl", 0, dumpTreeEitherLevel() >= 3);
}
