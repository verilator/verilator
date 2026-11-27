#pragma once

#include "../algorithm/parallel_push_relabel.h"
#include "../io/hmetis_io.h"
#include "../logger.h"

namespace whfc::Test {

    class FlowHypergraphTests {
    public:
        static constexpr bool log = true;

        bool tryFlowAlgo2(std::string file, Flow expected_flow, Node s, Node t) {
            FlowHypergraph hg = HMetisIO::readFlowHypergraph(file);
            ParallelPushRelabel pr(hg);
            pr.reset();
            pr.initialize(s, t);
            Flow f = pr.findMinCuts();
            std::cout << V(file) << " " << V(f) << std::endl;

            assert(f == expected_flow);
            return f == expected_flow;
        }

        void flowAlgoTest(std::string file, Flow expected_flow, Node s, Node t) { tryFlowAlgo2(file, expected_flow, s, t); }

        void run() {
            flowAlgoTest("../test_hypergraphs/testhg.hgr", Flow(1), Node(14), Node(10));
            flowAlgoTest("../test_hypergraphs/twocenters.hgr", Flow(2), Node(0), Node(2));
            flowAlgoTest("../test_hypergraphs/twocenters.hgr", Flow(2), Node(0), Node(3));
            flowAlgoTest("../test_hypergraphs/push_back.hgr", Flow(6), Node(0), Node(7));
        }
    };
} // namespace whfc::Test
