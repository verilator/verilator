#pragma once

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "repcut.h"

namespace repcut {

    class Adjacency
    {
    public:
        struct Range
        {
            using Iterator = std::vector<uint32_t>::const_iterator;
            Iterator first, last;

            Iterator begin() const { return first; }
            Iterator end() const { return last; }
            bool empty() const { return first == last; }
            size_t size() const { return empty() ? 0 : static_cast<size_t>(last - first); }
        };

        Range operator[](size_t vertex) const
        {
            assert(vertex < size());
            const auto first = offsets_[vertex], last = offsets_[vertex + 1];
            if (first == last)
                return {neighbors_.end(), neighbors_.end()};
            return {neighbors_.begin() + first, neighbors_.begin() + last};
        }

        size_t size() const { return offsets_.empty() ? 0 : offsets_.size() - 1; }

    private:
        friend class DirectedAcyclicGraph;
        // Offsets count edges, so they may exceed the 32-bit vertex-id range.
        std::vector<size_t> offsets_;
        std::vector<uint32_t> neighbors_;
    };

    // Compressed sparse row representation of the design DAG.
    class DirectedAcyclicGraph
    {
    public:
        // Per-vertex properties, indexed by vertex id.
        std::vector<float> weight; // numVertices; 0 for invalid nodes
        std::vector<bool> valid;   // numVertices

        // Adjacency (both directions kept for cone-marking and flood fill).
        Adjacency inNeigh;
        Adjacency outNeigh;

        // Valid vertices with empty outNeigh, populated by findSinkNodes().
        std::vector<uint32_t> sinkNodes;

        // Log threshold carried from RepCutContext.  Defaults to SILENT.
        RepCutLogLevel log_level = REPCUT_LOG_SILENT;

        // Parse the graph file into this DAG.  Returns true on success,
        // false on malformed input (with an error logged via rcp_log).
        bool buildFromFile(const char* filename);

        bool buildFromMemory(const RepCutGraph& graph);

        void findSinkNodes();

        size_t numVertices() const { return weight.size(); }

    private:
        void buildIncoming();
    };
} // namespace repcut
