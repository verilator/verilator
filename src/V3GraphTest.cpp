// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Graph tests
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#define VL_MT_DISABLED_CODE_UNIT 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Graph.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
//######################################################################
// Test class

class V3GraphTest VL_NOT_FINAL {
protected:
    // MEMBERS
    V3Graph m_graph;  // Graph under test

    // METHODS - for children
    virtual void runTest() = 0;  // Run the test
    virtual string name() = 0;  // Name of the test

    // Utilities
    void dumpSelf() {
        if (dumpGraphLevel() >= 9) m_graph.dumpDotFilePrefixed("v3graphtest_" + name());
    }

public:
    V3GraphTest() = default;
    virtual ~V3GraphTest() = default;

    void run() { runTest(); }
};

//######################################################################
//######################################################################
// Vertices and nodes

class V3GraphTestVertex VL_NOT_FINAL : public V3GraphVertex {
    VL_RTTI_IMPL(V3GraphTestVertex, V3GraphVertex)
    const string m_name;  // Vertex name

public:
    V3GraphTestVertex(V3Graph* graphp, const string& name)
        : V3GraphVertex{graphp}
        , m_name{name} {}
    ~V3GraphTestVertex() override = default;
    // ACCESSORS
    string name() const override VL_MT_STABLE { return m_name; }
};

class V3GraphTestVarVertex final : public V3GraphTestVertex {
public:
    V3GraphTestVarVertex(V3Graph* graphp, const string& name)
        : V3GraphTestVertex{graphp, name} {}
    ~V3GraphTestVarVertex() override = default;
    // ACCESSORS
    string dotColor() const override { return "blue"; }
};

//######################################################################
//######################################################################
// Test vertices and nodes

class V3GraphTestStrong final : public V3GraphTest {
public:
    string name() override { return "strong"; }
    void runTest() override {
        V3Graph* gp = &m_graph;
        // Verify we break edges at a good point
        // A simple alg would make 3 breaks, below only requires b->i to break
        V3GraphTestVertex* ip = new V3GraphTestVarVertex{gp, "*INPUTS*"};
        V3GraphTestVertex* ap = new V3GraphTestVarVertex{gp, "a"};
        V3GraphTestVertex* bp = new V3GraphTestVarVertex{gp, "b"};
        V3GraphTestVertex* g1p = new V3GraphTestVarVertex{gp, "g1"};
        V3GraphTestVertex* g2p = new V3GraphTestVarVertex{gp, "g2"};
        V3GraphTestVertex* g3p = new V3GraphTestVarVertex{gp, "g3"};
        V3GraphTestVertex* qp = new V3GraphTestVarVertex{gp, "q"};
        new V3GraphEdge{gp, ip, ap, 2, true};
        new V3GraphEdge{gp, ap, bp, 2, true};
        new V3GraphEdge{gp, bp, g1p, 2, true};
        new V3GraphEdge{gp, bp, g2p, 2, true};
        new V3GraphEdge{gp, bp, g3p, 2, true};
        new V3GraphEdge{gp, g1p, ap, 2, true};
        new V3GraphEdge{gp, g3p, g2p, 2, true};
        new V3GraphEdge{gp, g2p, g3p, 2, true};
        new V3GraphEdge{gp, g1p, qp, 2, true};
        new V3GraphEdge{gp, g2p, qp, 2, true};
        new V3GraphEdge{gp, g3p, qp, 2, true};

        gp->stronglyConnected(&V3GraphEdge::followAlwaysTrue);
        dumpSelf();

        UASSERT(ip->color() != ap->color() && ap->color() != g2p->color()
                    && g2p->color() != qp->color(),
                "SelfTest: Separate colors not assigned");
        UASSERT(ap->color() == bp->color() && ap->color() == g1p->color(),
                "SelfTest: Strongly connected nodes not colored together");
        UASSERT(g2p->color() == g3p->color(),
                "SelfTest: Strongly connected nodes not colored together");
    }
};

class V3GraphTestAcyc final : public V3GraphTest {
public:
    string name() override { return "acyc"; }
    void runTest() override {
        V3Graph* gp = &m_graph;
        // Verify we break edges at a good point
        // A simple alg would make 3 breaks, below only requires b->i to break
        V3GraphTestVertex* ip = new V3GraphTestVarVertex{gp, "*INPUTS*"};
        V3GraphTestVertex* ap = new V3GraphTestVarVertex{gp, "a"};
        V3GraphTestVertex* bp = new V3GraphTestVarVertex{gp, "b"};
        V3GraphTestVertex* g1p = new V3GraphTestVarVertex{gp, "g1"};
        V3GraphTestVertex* g2p = new V3GraphTestVarVertex{gp, "g2"};
        V3GraphTestVertex* g3p = new V3GraphTestVarVertex{gp, "g3"};
        new V3GraphEdge{gp, ip, ap, 2, true};
        new V3GraphEdge{gp, ap, bp, 2, true};
        new V3GraphEdge{gp, bp, g1p, 2, true};
        new V3GraphEdge{gp, bp, g2p, 2, true};
        new V3GraphEdge{gp, bp, g3p, 2, true};
        new V3GraphEdge{gp, g1p, ap, 2, true};
        new V3GraphEdge{gp, g2p, ap, 2, true};
        new V3GraphEdge{gp, g3p, ap, 2, true};

        gp->acyclic(&V3GraphEdge::followAlwaysTrue);
        gp->order();
        dumpSelf();
    }
};

class V3GraphTestVars final : public V3GraphTest {
public:
    string name() override { return "vars"; }
    void runTest() override {
        V3Graph* const gp = &m_graph;

        V3GraphTestVertex* const clkp = new V3GraphTestVarVertex{gp, "$clk"};

        V3GraphTestVertex* const ap = new V3GraphTestVarVertex{gp, "$a"};
        V3GraphTestVertex* const a_dlyp = new V3GraphTestVarVertex{gp, "$a_dly"};
        V3GraphTestVertex* const a_dlyblkp = new V3GraphTestVarVertex{gp, "$a_dlyblk"};
        V3GraphTestVertex* const bp = new V3GraphTestVarVertex{gp, "$b"};
        V3GraphTestVertex* const b_dlyp = new V3GraphTestVarVertex{gp, "$b_dly"};
        V3GraphTestVertex* const b_dlyblkp = new V3GraphTestVarVertex{gp, "$b_dlyblk"};
        V3GraphTestVertex* const cp = new V3GraphTestVarVertex{gp, "$c"};
        V3GraphTestVertex* const ip = new V3GraphTestVarVertex{gp, "$i"};

        V3GraphTestVertex* const a_prep = new V3GraphTestVarVertex{gp, "$a_pre"};
        V3GraphTestVertex* const b_prep = new V3GraphTestVarVertex{gp, "$b_pre"};
        V3GraphTestVertex* const c_prep = new V3GraphTestVarVertex{gp, "$c_pre"};

        V3GraphTestVertex* np;

        // Logical order between clk, and posedge blocks
        //   implemented by special CLK prod/cons?
        // Required order between first x_DLY<=x_pre and final x<=x_DLY
        //   implemented by producer/consumer on a_dly signals
        // Required order between first x_DLY<=x_pre and x_DLY<=setters
        //   implemented by fake dependency on _dlyblk
        // Required order between x_DLY<=setters and final x<=x_DLY
        //   implemented by producer/consumer on a_dly signals
        // Desired order between different _DLY blocks so we can elim temporaries
        //   implemented by cutable "pre" signal dependencies

        np = new V3GraphTestVertex{gp, "*INPUTS*"};
        {
            new V3GraphEdge{gp, np, clkp, 2};
            new V3GraphEdge{gp, np, ip, 2};
        }

        V3GraphTestVertex* const posedgep = np = new V3GraphTestVertex{gp, "*posedge clk*"};
        { new V3GraphEdge{gp, clkp, np, 2}; }

        // AlwaysPre's     VarRefs on LHS:  generate special BLK
        //    normal:      VarRefs on LHS:  generate normal
        //    underSBlock: VarRefs on RHS:  consume 'pre' (required to save cutable tests)
        np = new V3GraphTestVertex{gp, "a_dly<PRE=a"};
        {
            new V3GraphEdge{gp, np, a_dlyblkp, 2};  // Block ordering
            new V3GraphEdge{gp, np, a_dlyp, 2};
            new V3GraphEdge{gp, a_prep, np, 2,
                            true};  // DESIRED delayed ordering (inp is required)
            new V3GraphEdge{gp, posedgep, np, 2};
        }
        np = new V3GraphTestVertex{gp, "b_dly<PRE=b"};
        {
            new V3GraphEdge{gp, np, b_dlyblkp, 2};  // Block ordering
            new V3GraphEdge{gp, np, b_dlyp, 2};
            new V3GraphEdge{gp, b_prep, np, 2, true};  // DESIRED delayed ordering
            new V3GraphEdge{gp, posedgep, np, 2};
        }

        // AssignDly's     VarRefs on LHS:  consume special BLK
        //    normal:      VarRefs on LHS:  generate normal
        //    underSBlock: VarRefs on RHS:  generate 'pre' signals (cutable)
        //    SenItems:    consume CLOCK dependency
        np = new V3GraphTestVertex{gp, "a_dly<=b|c"};
        {
            new V3GraphEdge{gp, a_dlyblkp, np, 2};  // Block ordering in
            new V3GraphEdge{gp, np, a_dlyp, 2};
            // Note we don't include a_prep as we're generating a_dly
            new V3GraphEdge{gp, np, b_prep, 2};  // DESIRED delayed usage
            new V3GraphEdge{gp, np, c_prep, 2};  // DESIRED delayed usage
            new V3GraphEdge{gp, posedgep, np, 2};
        }
        np = new V3GraphTestVertex{gp, "b_dly<=a"};
        {
            new V3GraphEdge{gp, b_dlyblkp, np, 2};  // Block ordering in
            new V3GraphEdge{gp, np, b_dlyp, 2};
            new V3GraphEdge{gp, np, a_prep, 2};  // DESIRED delayed usage
            new V3GraphEdge{gp, posedgep, np, 2};
        }

        // AlwaysPost's
        //    normal:      VarRefs on LHS:  generate normal
        //    underSBlock: VarRefs on RHS:  consume normal
        np = new V3GraphTestVertex{gp, "a=POST=a_dly"};
        {
            new V3GraphEdge{gp, np, ap, 3};
            new V3GraphEdge{gp, a_dlyp, np, 3};
            new V3GraphEdge{gp, posedgep, np, 2};
        }
        np = new V3GraphTestVertex{gp, "b=POST=b_dly"};
        {
            new V3GraphEdge{gp, np, bp, 3};
            new V3GraphEdge{gp, b_dlyp, np, 3};
            new V3GraphEdge{gp, posedgep, np, 2};
        }

        // COMBO
        // Inbound edges are always uncutable, because we must put combo logic after sequential
        // Outbound are cutable, as we may need to evaluate multiple times

        {
            np = new V3GraphTestVertex{gp, "c=a|b|i"};
            new V3GraphEdge{gp, np, cp, 1, true};
            new V3GraphEdge{gp, ap, np, 1, false};
            new V3GraphEdge{gp, bp, np, 1, false};
            new V3GraphEdge{gp, ip, np, 1, false};
        }

        gp->acyclic(&V3GraphEdge::followAlwaysTrue);
        gp->order();

        // Test debug function
        gp->dumpEdges(std::cout, *a_prep);

        dumpSelf();
    }
};

//======================================================================

class V3GraphTestImport final : public V3GraphTest {

#ifdef GRAPH_IMPORT
    void dotImport();
#else
    void dotImport() {}
#endif

public:
    string name() override { return "import"; }
    void runTest() override {
        V3Graph* const gp = &m_graph;
        dotImport();
        dumpSelf();
        gp->acyclic(&V3GraphEdge::followAlwaysTrue);
        dumpSelf();
        gp->rank(&V3GraphEdge::followAlwaysTrue);
        dumpSelf();
    }
};

// clang-format off
#ifdef GRAPH_IMPORT
# include "graph_export.cpp"
#endif
// clang-format on

//======================================================================

void V3Graph::selfTest() {
    // Execute all of the tests
    UINFO(2, __FUNCTION__ << ":");
    { V3GraphTestStrong{}.run(); }
    { V3GraphTestAcyc{}.run(); }
    { V3GraphTestVars{}.run(); }
    { V3GraphTestImport{}.run(); }
}
