#include "ClusterGraph.h"
#include "DAG.h"

#include <filesystem>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <vector>

using repcut::ClusterGraph;

static void require(bool condition, const char* message)
{
    if (!condition)
        throw std::runtime_error(message);
}

static uint64_t km1(const std::vector<ClusterGraph::Hyperedge>& edges, const std::vector<unsigned>& assignment)
{
    uint64_t cost = 0;
    for (const auto& edge : edges) {
        unsigned blocks = 0;
        for (const auto pin : edge.pins)
            blocks |= 1U << assignment[pin];
        unsigned count = 0;
        for (; blocks; blocks &= blocks - 1)
            ++count;
        cost += uint64_t{edge.weight} * (count - 1);
    }
    return cost;
}

int main(int argc, char** argv)
{
    try {
        require(argc == 2, "Usage: test-hypergraph WORKDIR");
        std::filesystem::create_directories(argv[1]);
        const auto path = std::filesystem::path(argv[1]) / "input.graph";
        std::ofstream(path) << "11 9\nn 0.75 5 6\nn 1.25 6 7\nn 1.75 5 6\nn 0 5 6 7\nn 1.25 5 6\n"
                               "n 0\nn 0\nn 0\nn -1\n";
        repcut::DirectedAcyclicGraph dag;
        require(dag.buildFromFile(path.c_str()), "Cannot read graph");
        dag.findSinkNodes();
        ClusterGraph graph;
        graph.collapseFromDAG(dag);

        require(graph.hypernodeWeights() == std::vector<uint32_t>({3, 4, 2}), "Hypernode weights changed");
        const std::vector<ClusterGraph::Hyperedge> original{
            {{0, 1}, 1}, {{1, 2}, 2}, {{0, 1}, 2}, {{0, 1, 2}, 1}, {{0, 1}, 2}};
        require(graph.hyperedges.size() == 3, "Wrong number of unique hyperedges");
        const std::vector<ClusterGraph::Hyperedge> expected{{{0, 1}, 5}, {{1, 2}, 2}, {{0, 1, 2}, 1}};
        for (size_t i = 0; i < expected.size(); ++i) {
            require(graph.hyperedges[i].pins == expected[i].pins, "Pin sets or first-occurrence order changed");
            require(graph.hyperedges[i].weight == expected[i].weight, "Wrong merged edge weight");
        }
        // Every assignment of these three cones to three blocks must retain
        // its objective, including assignments with unused blocks.
        for (unsigned a = 0; a < 3; ++a)
            for (unsigned b = 0; b < 3; ++b)
                for (unsigned c = 0; c < 3; ++c)
                    require(km1(original, {a, b, c}) == km1(graph.hyperedges, {a, b, c}), "km1 objective changed");
        std::cout << "Merged hyperedges preserve weights, ordering and every assignment's km1 objective\n";
    }
    catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
