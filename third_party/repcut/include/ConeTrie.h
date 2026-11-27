// Persistent cone-id trie: vertices with the same cone set share a leaf
// node id. Cones MUST be inserted in strictly increasing cone-id order.

#pragma once

#include <cstddef>
#include <cstdint>
#include <memory>
#include <vector>

namespace repcut {

    class ConeTrie
    {
    public:
        using NodeId = uint32_t;

        ConeTrie();

        NodeId root() const { return 0; }

        // Add the current cone, or return node unchanged if it already ends
        // with that cone. Equal paths share a node. Once a larger cone id is
        // visited, earlier cone ids must never be visited again.
        NodeId visit(NodeId node, uint32_t cone_id);

        // Cone ids from root to leaf in increasing order (empty for root).
        std::vector<uint32_t> pathConeIds(NodeId leaf) const;

        // Excludes the root.
        size_t nodeCount() const { return size_ - 1; }

    private:
        static constexpr NodeId NO_NODE = UINT32_MAX;
        static constexpr size_t CHUNK_BITS = 16;
        static constexpr size_t CHUNK_SIZE = size_t{1} << CHUNK_BITS;

        struct Node
        {
            // Cone id added at this trie level. Root uses UINT32_MAX as sentinel.
            uint32_t value;
            NodeId parent;
            NodeId lastChild;
        };
        static_assert(sizeof(Node) == 12, "Cone trie nodes must remain compact");

        Node& node(NodeId id);
        const Node& node(NodeId id) const;
        NodeId append(uint32_t value, NodeId parent);

        // Growing the arena never moves existing nodes or copies a full arena.
        std::vector<std::unique_ptr<Node[]>> chunks_;
        size_t size_ = 0;
    };

} // namespace repcut
