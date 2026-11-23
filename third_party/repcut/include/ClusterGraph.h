#pragma once

#include <cstdint>
#include <memory>
#include <vector>

#include "DAG.h"
#include "repcut.h"

#include "ConeTrie.h"

namespace repcut {
    // Intermediate structure: DAG of clusters (groups sharing the same cone
    // set), with identical intersection hyperedges merged for both backends.
    class ClusterGraph
    {
    private:
        // Collapse phases.  See collapseFromDAG for the orchestration.
        void _mark_cones();
        void _collect_clusters();
        void _update_cluster_weight();
        void _build_hypergraph();

        // Trie mapping vertex -> leaf with its cone-id set; equality = node-id equality.
        std::unique_ptr<ConeTrie> coneTrie;
        std::vector<ConeTrie::NodeId> vtxToNode;
        std::vector<uint32_t> nodeWeights;

    public:
        std::vector<uint32_t> sinkNodes;

        // Clusters should be non-overlapping
        std::vector<std::vector<uint32_t>> clusters;

        // -1: unvisited
        // -2 invalid
        std::vector<int32_t> idToClusterId;

        // Non-owning DAG pointer (set once, must not outlive the DAG).
        const DirectedAcyclicGraph* dag = nullptr;

        struct Hyperedge
        {
            // Sorted unique cone ids, derived from the canonical trie path.
            std::vector<uint32_t> pins;
            uint32_t weight = 0;
        };
        // One edge per distinct non-cone pin set, in first-cluster order.
        std::vector<Hyperedge> hyperedges;

        // Per-cluster weight (float).
        std::vector<float> nodeWeight;

        // Log threshold carried from RepCutContext.
        RepCutLogLevel log_level = REPCUT_LOG_SILENT;

        void collapseFromDAG(const DirectedAcyclicGraph& dag);

        uint32_t clusterWeight(size_t cluster_id) const;
        const std::vector<uint32_t>& hypernodeWeights() const { return nodeWeights; }

        // Write hMetis-format file (nodes=cones, edges=merged non-cone clusters).
        void writeHMetisFile(const char* filename);
    };
} // namespace repcut
