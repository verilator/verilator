#include "ConeTrie.h"

#include <algorithm>
#include <cassert>
#include <stdexcept>

namespace repcut {

    ConeTrie::ConeTrie()
    {
        append(UINT32_MAX, NO_NODE);
    }

    ConeTrie::Node& ConeTrie::node(NodeId id)
    {
        assert(id < size_);
        return chunks_[id >> CHUNK_BITS][id & (CHUNK_SIZE - 1)];
    }

    const ConeTrie::Node& ConeTrie::node(NodeId id) const
    {
        assert(id < size_);
        return chunks_[id >> CHUNK_BITS][id & (CHUNK_SIZE - 1)];
    }

    ConeTrie::NodeId ConeTrie::append(uint32_t value, NodeId parent)
    {
        if (size_ == NO_NODE)
            throw std::length_error("Cone trie exceeds the 32-bit node limit");
        if ((size_ & (CHUNK_SIZE - 1)) == 0) {
            // Initialize nodes as they are used, rather than touching a whole
            // chunk for a small graph. The temporary owns it if growth throws.
            chunks_.push_back(std::unique_ptr<Node[]>(new Node[CHUNK_SIZE]));
        }
        const NodeId id = static_cast<NodeId>(size_++);
        node(id) = {value, parent, NO_NODE};
        return id;
    }

    ConeTrie::NodeId ConeTrie::visit(NodeId id, uint32_t cone_id)
    {
        Node& parent = node(id);
        assert(cone_id != UINT32_MAX);
        if (parent.value == cone_id)
            return id;
        assert(id == root() || parent.value < cone_id);
        if (parent.lastChild != NO_NODE) {
            const auto last_cone = node(parent.lastChild).value;
            assert(last_cone <= cone_id);
            if (last_cone == cone_id)
                return parent.lastChild;
        }

        // Cone ids arrive in increasing order, so earlier children will never
        // be looked up again. Their ids and parent links remain valid.
        const NodeId child = append(cone_id, id);
        parent.lastChild = child;
        return child;
    }

    std::vector<uint32_t> ConeTrie::pathConeIds(NodeId leaf) const
    {
        std::vector<uint32_t> ids;
        for (NodeId id = leaf; id != root(); id = node(id).parent)
            ids.push_back(node(id).value);
        std::reverse(ids.begin(), ids.end());
        return ids;
    }

} // namespace repcut
