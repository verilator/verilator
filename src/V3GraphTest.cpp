// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Graph tests
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

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Graph.h"

//######################################################################
//######################################################################
// Test class

class V3GraphTest VL_NOT_FINAL {
protected:
    // MEMBERS
    V3Graph m_graph;

    // METHODS - for children
    virtual void runTest() = 0;  // Run the test
    virtual string name() = 0;  // Name of the test

    // Utilities
    void dump() {
        if (debug() >= 9) m_graph.dumpDotFilePrefixed("v3graphtest_" + name());
    }

public:
    V3GraphTest() = default;
    virtual ~V3GraphTest() = default;
    VL_DEBUG_FUNC;  // Declare debug()
    void run() { runTest(); }
};

//######################################################################
//######################################################################
// Vertices and nodes

class V3GraphTestVertex VL_NOT_FINAL : public V3GraphVertex {
    const string m_name;

public:
    V3GraphTestVertex(V3Graph* graphp, const string& name)
        : V3GraphVertex{graphp}
        , m_name{name} {}
    virtual ~V3GraphTestVertex() override = default;
    // ACCESSORS
    virtual string name() const override { return m_name; }
};

class V3GraphTestVarVertex final : public V3GraphTestVertex {
public:
    V3GraphTestVarVertex(V3Graph* graphp, const string& name)
        : V3GraphTestVertex{graphp, name} {}
    virtual ~V3GraphTestVarVertex() override = default;
    // ACCESSORS
    virtual string dotColor() const override { return "blue"; }
};

//######################################################################
//######################################################################
// Test vertices and nodes

class V3GraphTestStrong final : public V3GraphTest {
public:
    virtual string name() override { return "strong"; }
    virtual void runTest() override {
        V3Graph* gp = &m_graph;
        // Verify we break edges at a good point
        // A simple alg would make 3 breaks, below only requires b->i to break
        V3GraphTestVertex* i = new V3GraphTestVarVertex(gp, "*INPUTS*");
        V3GraphTestVertex* a = new V3GraphTestVarVertex(gp, "a");
        V3GraphTestVertex* b = new V3GraphTestVarVertex(gp, "b");
        V3GraphTestVertex* g1 = new V3GraphTestVarVertex(gp, "g1");
        V3GraphTestVertex* g2 = new V3GraphTestVarVertex(gp, "g2");
        V3GraphTestVertex* g3 = new V3GraphTestVarVertex(gp, "g3");
        V3GraphTestVertex* q = new V3GraphTestVarVertex(gp, "q");
        new V3GraphEdge(gp, i, a, 2, true);
        new V3GraphEdge(gp, a, b, 2, true);
        new V3GraphEdge(gp, b, g1, 2, true);
        new V3GraphEdge(gp, b, g2, 2, true);
        new V3GraphEdge(gp, b, g3, 2, true);
        new V3GraphEdge(gp, g1, a, 2, true);
        new V3GraphEdge(gp, g3, g2, 2, true);
        new V3GraphEdge(gp, g2, g3, 2, true);
        new V3GraphEdge(gp, g1, q, 2, true);
        new V3GraphEdge(gp, g2, q, 2, true);
        new V3GraphEdge(gp, g3, q, 2, true);

        gp->stronglyConnected(&V3GraphEdge::followAlwaysTrue);
        dump();

        UASSERT(i->color() != a->color() && a->color() != g2->color() && g2->color() != q->color(),
                "SelfTest: Separate colors not assigned");
        UASSERT(a->color() == b->color() && a->color() == g1->color(),
                "SelfTest: Strongly connected nodes not colored together");
        UASSERT(g2->color() == g3->color(),
                "SelfTest: Strongly connected nodes not colored together");
    }
};

class V3GraphTestAcyc final : public V3GraphTest {
public:
    virtual string name() override { return "acyc"; }
    virtual void runTest() override {
        V3Graph* gp = &m_graph;
        // Verify we break edges at a good point
        // A simple alg would make 3 breaks, below only requires b->i to break
        V3GraphTestVertex* i = new V3GraphTestVarVertex(gp, "*INPUTS*");
        V3GraphTestVertex* a = new V3GraphTestVarVertex(gp, "a");
        V3GraphTestVertex* b = new V3GraphTestVarVertex(gp, "b");
        V3GraphTestVertex* g1 = new V3GraphTestVarVertex(gp, "g1");
        V3GraphTestVertex* g2 = new V3GraphTestVarVertex(gp, "g2");
        V3GraphTestVertex* g3 = new V3GraphTestVarVertex(gp, "g3");
        new V3GraphEdge(gp, i, a, 2, true);
        new V3GraphEdge(gp, a, b, 2, true);
        new V3GraphEdge(gp, b, g1, 2, true);
        new V3GraphEdge(gp, b, g2, 2, true);
        new V3GraphEdge(gp, b, g3, 2, true);
        new V3GraphEdge(gp, g1, a, 2, true);
        new V3GraphEdge(gp, g2, a, 2, true);
        new V3GraphEdge(gp, g3, a, 2, true);

        gp->acyclic(&V3GraphEdge::followAlwaysTrue);
        gp->order();
        dump();
    }
};

class V3GraphTestVars final : public V3GraphTest {
public:
    virtual string name() override { return "vars"; }
    virtual void runTest() override {
        V3Graph* gp = &m_graph;

        V3GraphTestVertex* clk = new V3GraphTestVarVertex(gp, "$clk");

        V3GraphTestVertex* a = new V3GraphTestVarVertex(gp, "$a");
        V3GraphTestVertex* a_dly = new V3GraphTestVarVertex(gp, "$a_dly");
        V3GraphTestVertex* a_dlyblk = new V3GraphTestVarVertex(gp, "$a_dlyblk");
        V3GraphTestVertex* b = new V3GraphTestVarVertex(gp, "$b");
        V3GraphTestVertex* b_dly = new V3GraphTestVarVertex(gp, "$b_dly");
        V3GraphTestVertex* b_dlyblk = new V3GraphTestVarVertex(gp, "$b_dlyblk");
        V3GraphTestVertex* c = new V3GraphTestVarVertex(gp, "$c");
        V3GraphTestVertex* i = new V3GraphTestVarVertex(gp, "$i");

        V3GraphTestVertex* ap = new V3GraphTestVarVertex(gp, "$a_pre");
        V3GraphTestVertex* bp = new V3GraphTestVarVertex(gp, "$b_pre");
        V3GraphTestVertex* cp = new V3GraphTestVarVertex(gp, "$c_pre");

        V3GraphTestVertex* n;

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

        n = new V3GraphTestVertex(gp, "*INPUTS*");
        {
            new V3GraphEdge(gp, n, clk, 2);
            new V3GraphEdge(gp, n, i, 2);
        }

        V3GraphTestVertex* posedge = n = new V3GraphTestVertex(gp, "*posedge clk*");
        { new V3GraphEdge(gp, clk, n, 2); }

        // AssignPre's     VarRefs on LHS:  generate special BLK
        //    normal:      VarRefs on LHS:  generate normal
        //    underSBlock: VarRefs on RHS:  consume 'pre' (required to save cutable tests)
        n = new V3GraphTestVertex(gp, "a_dly<PRE=a");
        {
            new V3GraphEdge(gp, n, a_dlyblk, 2);  // Block ordering
            new V3GraphEdge(gp, n, a_dly, 2);
            new V3GraphEdge(gp, ap, n, 2, true);  // DESIRED delayed ordering (inp is required)
            new V3GraphEdge(gp, posedge, n, 2);
        }
        n = new V3GraphTestVertex(gp, "b_dly<PRE=b");
        {
            new V3GraphEdge(gp, n, b_dlyblk, 2);  // Block ordering
            new V3GraphEdge(gp, n, b_dly, 2);
            new V3GraphEdge(gp, bp, n, 2, true);  // DESIRED delayed ordering
            new V3GraphEdge(gp, posedge, n, 2);
        }

        // AssignDly's     VarRefs on LHS:  consume special BLK
        //    normal:      VarRefs on LHS:  generate normal
        //    underSBlock: VarRefs on RHS:  generate 'pre' signals (cutable)
        //    SenItems:    consume CLOCK dependency
        n = new V3GraphTestVertex(gp, "a_dly<=b|c");
        {
            new V3GraphEdge(gp, a_dlyblk, n, 2);  // Block ordering in
            new V3GraphEdge(gp, n, a_dly, 2);
            // Note we don't include ap as we're generating a_dly
            new V3GraphEdge(gp, n, bp, 2);  // DESIRED delayed usage
            new V3GraphEdge(gp, n, cp, 2);  // DESIRED delayed usage
            new V3GraphEdge(gp, posedge, n, 2);
        }
        n = new V3GraphTestVertex(gp, "b_dly<=a");
        {
            new V3GraphEdge(gp, b_dlyblk, n, 2);  // Block ordering in
            new V3GraphEdge(gp, n, b_dly, 2);
            new V3GraphEdge(gp, n, ap, 2);  // DESIRED delayed usage
            new V3GraphEdge(gp, posedge, n, 2);
        }

        // AssignPost's
        //    normal:      VarRefs on LHS:  generate normal
        //    underSBlock: VarRefs on RHS:  consume normal
        n = new V3GraphTestVertex(gp, "a=POST=a_dly");
        {
            new V3GraphEdge(gp, n, a, 3);
            new V3GraphEdge(gp, a_dly, n, 3);
            new V3GraphEdge(gp, posedge, n, 2);
        }
        n = new V3GraphTestVertex(gp, "b=POST=b_dly");
        {
            new V3GraphEdge(gp, n, b, 3);
            new V3GraphEdge(gp, b_dly, n, 3);
            new V3GraphEdge(gp, posedge, n, 2);
        }

        // COMBO
        // Inbound edges are always uncutable, because we must put combo logic after sequential
        // Outbound are cutable, as we may need to evaluate multiple times

        {
            n = new V3GraphTestVertex(gp, "c=a|b|i");
            new V3GraphEdge(gp, n, c, 1, true);
            new V3GraphEdge(gp, a, n, 1, false);
            new V3GraphEdge(gp, b, n, 1, false);
            new V3GraphEdge(gp, i, n, 1, false);
        }

        gp->acyclic(&V3GraphEdge::followAlwaysTrue);
        gp->order();

        dump();
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
    virtual string name() override { return "import"; }
    virtual void runTest() override {
        V3Graph* const gp = &m_graph;
        dotImport();
        dump();
        gp->acyclic(&V3GraphEdge::followAlwaysTrue);
        dump();
        gp->rank(&V3GraphEdge::followAlwaysTrue);
        dump();
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
    UINFO(2, __FUNCTION__ << ": " << endl);
    // clang-format off
    { V3GraphTestStrong test; test.run(); }
    { V3GraphTestAcyc test; test.run(); }
    { V3GraphTestVars test; test.run(); }
    { V3GraphTestImport test; test.run(); }
    // clang-format on
}
