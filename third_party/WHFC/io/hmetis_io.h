#pragma once

#include <fstream>
#include "../datastructure/flow_hypergraph.h"
#include "../datastructure/flow_hypergraph_builder.h"

namespace whfc {
    class HMetisIO {
    private:
        inline static void mgetline(std::ifstream& f, std::string& line) {
            std::getline(f, line);
            while (line[0] == '%') {
                std::getline(f, line);
            }
        }

    public:
        enum class HGType : uint8_t {
            Unweighted = 0,
            EdgeWeights = 1,
            NodeWeights = 10,
            EdgeAndNodeWeights = 11,
        };


        static auto readHeader(std::ifstream& f) {
            std::string line;
            size_t numHEs, numNodes;
            HGType hg_type = HGType::Unweighted;
            {
                // read header
                mgetline(f, line);
                std::istringstream iss(line);
                iss >> numHEs >> numNodes;
                uint32_t type = 0;
                if (iss >> type) {
                    hg_type = static_cast<HGType>(type);
                }
            }
            return std::make_tuple(numNodes, numHEs, hg_type);
        }

        static FlowHypergraphBuilder readFlowHypergraphWithBuilder(const std::string& filename) {
            FlowHypergraphBuilder hgb;
            return readFlowHypergraphWithBuilder(hgb, filename);
        }

        static FlowHypergraphBuilder& readFlowHypergraphWithBuilder(FlowHypergraphBuilder& hgb, const std::string& filename) {
            std::ifstream f(filename);
            if (!f)
                throw std::runtime_error("File: " + filename + " not found.");

            auto [numNodes, numHEs, hg_type] = readHeader(f);
            hgb.clear();
            hgb.reinitialize(numNodes);

            std::string line;

            bool hasHyperedgeWeights = hg_type == HGType::EdgeAndNodeWeights || hg_type == HGType ::EdgeWeights;
            bool hasNodeWeights = hg_type == HGType::EdgeAndNodeWeights || hg_type == HGType::NodeWeights;

            for (size_t e = 0; e < numHEs; ++e) {
                mgetline(f, line);
                std::istringstream iss(line);
                uint32_t pin;
                uint32_t he_weight = 1;

                if (hasHyperedgeWeights)
                    iss >> he_weight;

                hgb.startHyperedge(he_weight);
                size_t he_size = 0;
                while (iss >> pin) {
                    if (pin < 1)
                        throw std::runtime_error("File: " + filename + " has pin id < 1 (in one-based ids).");
                    if (pin > numNodes)
                        throw std::runtime_error("File: " + filename + " has pin id > number of nodes.");
                    hgb.addPin(Node(pin - 1));
                    he_size++;
                }
                if (he_size <= 1)
                    throw std::runtime_error("File: " + filename + " has pin with zero or one pins.");
            }

            for (Node u(0); u < numNodes; ++u) {
                NodeWeight nw(1);
                if (hasNodeWeights) {
                    mgetline(f, line);
                    std::istringstream iss(line);
                    iss >> nw;
                }
                hgb.nodeWeight(u) = nw;
            }

            hgb.finalize();

            f.close();
            return hgb;
        }


        static FlowHypergraph readFlowHypergraph(const std::string& filename) {

            std::vector<NodeWeight> nodeWeights;
            std::vector<HyperedgeWeight> hyperedgeWeights;
            std::vector<Node> pins;
            std::vector<PinIndex> hyperedgeSizes;

            std::ifstream f(filename);
            if (!f)
                throw std::runtime_error("File: " + filename + " not found.");

            auto [numNodes, numHEs, hg_type] = readHeader(f);

            std::string line;

            bool hasHyperedgeWeights = hg_type == HGType::EdgeAndNodeWeights || hg_type == HGType ::EdgeWeights;

            bool hasNodeWeights = hg_type == HGType::EdgeAndNodeWeights || hg_type == HGType::NodeWeights;
            if (!hasNodeWeights)
                nodeWeights.resize(numNodes, NodeWeight(1));

            for (size_t e = 0; e < numHEs; ++e) {
                mgetline(f, line);
                std::istringstream iss(line);
                uint32_t pin;
                uint32_t he_size = 0;
                uint32_t he_weight = 1;

                if (hasHyperedgeWeights)
                    iss >> he_weight;
                hyperedgeWeights.emplace_back(he_weight);

                while (iss >> pin) {
                    if (pin < 1)
                        throw std::runtime_error("File: " + filename + " has pin id < 1 (in one-based ids).");
                    if (pin > numNodes)
                        throw std::runtime_error("File: " + filename + " has pin id > number of nodes.");
                    he_size++;
                    pins.emplace_back(pin - 1);
                }
                hyperedgeSizes.emplace_back(he_size);

                if (he_size > numNodes)
                    throw std::runtime_error("File: " + filename + " has hyperedge with more pins than nodes in the hypergraph.");
                if (he_size == 0)
                    throw std::runtime_error("File: " + filename + " has hyperedge with zero pins.");
                if (he_size == 1) {
                    // ignore single pin hyperedges
                    pins.pop_back();
                    hyperedgeWeights.pop_back();
                    hyperedgeSizes.pop_back();
                }
            }

            if (hasNodeWeights) {
                for (size_t u = 0; u < numNodes; ++u) {
                    uint32_t nw;
                    mgetline(f, line);
                    std::istringstream iss(line);
                    iss >> nw;
                    nodeWeights.emplace_back(nw);
                }
            }

            f.close();

            return FlowHypergraph(nodeWeights, hyperedgeWeights, hyperedgeSizes, pins);
        }

        static void writeFlowHypergraph(FlowHypergraph& hg, std::string& filename) {
            if (filename.empty())
                throw std::runtime_error("No filename for Flow Hypergraph specified");
            std::ofstream f(filename);
            if (!f)
                throw std::runtime_error("Failed at creating Flow Hypergraph file " + filename);

            bool hasNodeWeights = hg.hasNodeWeights();
            bool hasHyperedgeWeights = hg.hasHyperedgeWeights();

            {
                // write header
                f << hg.numHyperedges() << " " << hg.numNodes();
                if (hasNodeWeights)
                    if (hasHyperedgeWeights)
                        f << " " << static_cast<uint32_t>(HGType::EdgeAndNodeWeights);
                    else
                        f << " " << static_cast<uint32_t>(HGType::NodeWeights);
                else if (hasHyperedgeWeights)
                    f << " " << static_cast<uint32_t>(HGType::EdgeWeights);
                f << "\n";
            }

            for (Hyperedge e : hg.hyperedgeIDs()) {
                auto pinsOfE = hg.pinsOf(e);
                if (pinsOfE.empty())
                    throw std::runtime_error("Hypergraph has hyperedge with zero pins");
                if (hasHyperedgeWeights)
                    f << hg.capacity(e) << " ";

                f << (pinsOfE.begin()->pin + 1);
                pinsOfE.advance_begin(); // special case first pin since we have |e|-1 white spaces
                for (const FlowHypergraph::Pin& p : pinsOfE)
                    f << " " << (p.pin + 1); // yes... hMetis insists on 1-based IDs -.-
                f << "\n";
            }

            if (hasNodeWeights)
                for (Node u : hg.nodeIDs())
                    f << hg.nodeWeight(u) << "\n";


            f << std::flush;
            f.close();
        }
    };
} // namespace whfc
