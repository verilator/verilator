#pragma once

#include "../datastructure/flow_hypergraph.h"

namespace whfc {
    namespace Test {
        class CreateDummyHypergraphs {
        public:
            static whfc::FlowHypergraph noHyperedgesGivenNodeWeights(std::vector<whfc::NodeWeight>& nodeWeights) {
                std::vector<whfc::HyperedgeWeight> heWeights;
                std::vector<whfc::PinIndex> heSizes;
                std::vector<whfc::Node> pins;
                return whfc::FlowHypergraph(nodeWeights, heWeights, heSizes, pins);
            }
        };
    } // namespace Test
} // namespace whfc
