// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Mark modules affected by assertcontrol
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
// AssertCtlVisitor does not perform any AST transformations.
// Instead it propagates two types of flags:
// - flag "has assert": (for detecting what modules are affected by an assert statement)
//      The visitor locates all modules with assert statements and marks them
//      with _M_HAS_ASSERT flag.
// - flag "has assertctl": (for detecting what modules are affected by an assertcontrol statement)
//      The visitor locates all modules with assertcontrol statements and marks
//      them with _M_HAS_ASSERTCTL flag.
//  The _M_HAS_ASSERT is propagated upwards to the nodes marked with that flag.
//  The _M_HAS_ASSERTCTL is propagated downwards through the nodes marked with
//  that flag.
//  After propagation phase, if a module has both flags, we mark it as
//  "affected by assertcontrol" and save this information in a "user" field
//  for later use in the V3Assert phase.
//*************************************************************************

#include "V3AssertCtl.h"

#include "V3Broken.h"
#include "V3Error.h"
#include "V3Global.h"
#include "V3Graph.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// AssertCtl class functions

class AssertCtlVisitor final : public VNVisitor {

    // TYPES
    class DepVtx VL_NOT_FINAL : public V3GraphVertex {
        VL_RTTI_IMPL(DepVtx, V3GraphVertex)
        AstNode* const m_nodep;  // AST node represented by this graph vertex.

        // ACCESSORS
        string name() const override {
            return cvtToHex(nodep()) + ' ' + nodep()->prettyTypeName();
        }
        FileLine* fileline() const override { return nodep()->fileline(); }
        string dotColor() const override {
            if (VN_IS(nodep(), Module)) {
                if (hasFlags(nodep(), M_HAS_ASSERT)) {
                    if (hasFlags(nodep(), M_HAS_ASSERTCTL)) return "green";
                    return "red";
                }
                if (hasFlags(nodep(), M_HAS_ASSERTCTL)) return "blue";
                return "black";
            } else if (VN_IS(nodep(), AssertInstance)) {
                return "orange";
            } else if (VN_IS(nodep(), AssertCtl)) {
                return "magenta";
            }
            return "gray";
        }

    public:
        // CONSTRUCTORS
        DepVtx(V3Graph* graphp, AstNode* nodep)
            : V3GraphVertex{graphp}
            , m_nodep{nodep} {}
        ~DepVtx() override = default;

        // ACCESSORS
        virtual AstNode* nodep() const VL_MT_STABLE { return m_nodep; }
    };

    enum ModuleFlag : uint8_t { M_HAS_ASSERT = 1 << 0, M_HAS_ASSERTCTL = 1 << 1 };
    using ModuleFlagType = std::underlying_type_t<ModuleFlag>;

    // NODE STATE
    // The rest of the users are defined in the AssertVisitor.
    //  AstNodeModule::user1()  -> DependencyVertex*.  Vertex in m_assertGraph
    //  AstNodeModule::user2()  -> int.                ModuleFlag
    //  AstNodeModule::user3()  -> bool.               True if module is affected by AssertCtl
    //  AstNodeModule::user4()  -> bool.               True if processed
    const VNUser4InUse m_user4InUse;

    // STATE
    V3Graph m_assertGraph;
    AstNode* m_parentp = nullptr;
    string m_hierarchicalName{};
    bool m_moduleInCell = false;
    bool m_inClass = false;
    bool m_inIface = false;

    static void addFlags(AstNode* const nodep, ModuleFlagType flags) {
        nodep->user2(nodep->user2() | flags);
    }
    static bool hasFlags(const AstNode* const nodep, ModuleFlagType flags) {
        return !(~nodep->user2() & flags);
    }
    static bool passFlag(const AstNode* const from, AstNode* const to, ModuleFlag flag) {
        if (hasFlags(from, flag) && !hasFlags(to, flag)) {
            addFlags(to, flag);
            return true;
        }
        return false;
    }
    static void setModuleAffectedByCtl(AstNode* const nodep) { nodep->user3(true); }

    // METHODS
    // Get or create the dependency vertex for the given node.
    DepVtx* getDepVtx(AstNode* const nodep) {
        if (!nodep->user1p()) nodep->user1p(new DepVtx{&m_assertGraph, nodep});
        return nodep->user1u().to<DepVtx*>();
    }

    void propagateBackwardAssert(DepVtx* const vxp) {
        const AstNode* const parentp = vxp->nodep();
        for (V3GraphEdge& edge : vxp->inEdges()) {
            DepVtx* const depVxp = static_cast<DepVtx*>(edge.fromp());
            AstNode* const depp = depVxp->nodep();
            if (!hasFlags(depp, M_HAS_ASSERT) && passFlag(parentp, depp, M_HAS_ASSERT))
                propagateBackwardAssert(depVxp);
        }
    }

    void propagateForwardCtl(DepVtx* const vxp) {
        const AstNode* const parentp = vxp->nodep();
        for (V3GraphEdge& edge : vxp->outEdges()) {
            DepVtx* const depVxp = static_cast<DepVtx*>(edge.top());
            AstNode* const depp = depVxp->nodep();
            if (!hasFlags(depp, M_HAS_ASSERTCTL) && passFlag(parentp, depp, M_HAS_ASSERTCTL))
                propagateForwardCtl(depVxp);
        }
    }

    void propagateFlags() {
        for (V3GraphVertex& vtx : m_assertGraph.vertices()) {
            DepVtx& depVxp = static_cast<DepVtx&>(vtx);
            if (hasFlags(depVxp.nodep(), M_HAS_ASSERT)) propagateBackwardAssert(&depVxp);
            if (hasFlags(depVxp.nodep(), M_HAS_ASSERTCTL)) propagateForwardCtl(&depVxp);
        }
    }

    static void markModuleAffected(DepVtx* const vxp) {
        for (V3GraphEdge& edge : vxp->outEdges()) {
            DepVtx* const depVxp = static_cast<DepVtx*>(edge.top());
            AstNode* const depp = depVxp->nodep();
            if (VN_IS(depp, Module)) {
                if (hasFlags(depp, M_HAS_ASSERT | M_HAS_ASSERTCTL)) {
                    UINFO(9, "found vertex with both assert and assertctl: '"
                                 << depp->name() << "', marking as affected" << endl);
                    setModuleAffectedByCtl(depp);
                } else {
                    UINFO(9, "found module not affected by assertctl: '" << depp->name() << "'"
                                                                         << endl);
                }
            }
        }
    }

    void markModulesAffected() {
        for (V3GraphVertex& vxp : m_assertGraph.vertices()) {
            DepVtx& depVxp = static_cast<DepVtx&>(vxp);
            markModuleAffected(&depVxp);
        }
    }

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        // Ignore non-top modules not traversed through cell references.
        if (!m_moduleInCell && nodep->level() > 2) return;
        if (nodep->level() <= 2) m_hierarchicalName = nodep->name();
        new V3GraphEdge{&m_assertGraph, getDepVtx(m_parentp), getDepVtx(nodep), 1};

        VL_RESTORER(m_inClass);
        VL_RESTORER(m_inIface);
        VL_RESTORER(m_parentp);
        {
            if (VN_IS(nodep, Class)) {
                m_inClass = true;
            } else if (VN_IS(nodep, Iface)) {
                m_inIface = true;
            }

            m_parentp = nodep;
            iterateChildren(nodep);
        }
    }
    void visit(AstCell* nodep) override {
        VL_RESTORER(m_moduleInCell);
        VL_RESTORER(m_hierarchicalName);

        m_moduleInCell = true;
        m_hierarchicalName += "." + nodep->name();
        iterate(nodep->modp());
    }
    void visit(AstBegin* nodep) override {
        VL_RESTORER(m_hierarchicalName);

        // Handle named blocks.
        if (!nodep->name().empty()) m_hierarchicalName += "." + nodep->name();
        iterateChildren(nodep);
    }
    void visit(AstTask* nodep) override {
        VL_RESTORER(m_hierarchicalName);

        // Handle asserts under functions.
        if (!nodep->name().empty()) m_hierarchicalName += "." + nodep->name();
        iterateChildren(nodep);
    }
    void visit(AstAssert* nodep) override {
        addFlags(m_parentp, M_HAS_ASSERT);

        // Since scopes are not yet resolved, we need to create assert 'instances'
        // that would mimic them for the propagation sake.
        AstAssertInstance* const instancep
            = new AstAssertInstance{nodep->fileline(), m_hierarchicalName};
        pushDeletep(instancep);

        new V3GraphEdge{&m_assertGraph, getDepVtx(m_parentp), getDepVtx(instancep), 1};
        new V3GraphEdge{&m_assertGraph, getDepVtx(instancep), getDepVtx(nodep), 1};
    }
    void visit(AstAssertCtl* nodep) override {
        if (nodep->user4SetOnce()) return;
        if (m_inClass) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: assertcontrols in classes");
        } else if (m_inIface) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: assertcontrols in ifaces");
        } else {
            addFlags(m_parentp, M_HAS_ASSERTCTL);
        }

        nodep->name(m_hierarchicalName);

        new V3GraphEdge{&m_assertGraph, getDepVtx(m_parentp), getDepVtx(nodep), 1};
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit AssertCtlVisitor(AstNetlist* nodep)
        : m_parentp(nodep) {
        iterateChildren(nodep);
        propagateFlags();
        markModulesAffected();
        if (dumpGraphLevel() >= 6) m_assertGraph.dumpDotFilePrefixed("assertctl-graph");

        // Clear users for the Assert stage.
        VNUser1InUse::clear();
        VNUser2InUse::clear();
    }
    ~AssertCtlVisitor() = default;
};

//######################################################################
// Top AssertCtl class

void V3AssertCtl::markModulesAffectedByCtl(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { AssertCtlVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("assertctl", 0, dumpTreeEitherLevel() >= 3);
}
