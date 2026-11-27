#pragma once

#include <numeric>

#include "../definitions.h"
#include "../util/unused.h"

namespace whfc {

    class FlowHypergraph {
    public:
        struct Pin {
            Node pin = invalidNode;
            InHeIndex he_inc_iter;
            bool operator==(const Pin& o) const { return o.pin == pin && o.he_inc_iter == he_inc_iter; }
        };

        struct InHe { // Hyperedge Incidence
            Hyperedge e = invalidHyperedge;
            PinIndex pin_iter;
        };

        struct HyperedgeData {
            PinIndex first_out = PinIndex(0);
            Flow capacity = Flow(0);
        };

        struct NodeData {
            InHeIndex first_out = InHeIndex(0);
            NodeWeight weight = NodeWeight(0);
        };

        using PinRange = mutable_range<std::vector<Pin>>;
        using PinIterator = PinRange::iterator;
        using PinIndexRange = mutable_index_range<PinIndex>;
        using InHeRange = mutable_range<std::vector<InHe>>;
        using InHeIterator = InHeRange::iterator;
        using InHeIndexRange = mutable_index_range<InHeIndex>;

        inline auto nodeIDs() const { return mutable_index_range<Node>(Node(0), Node::fromOtherValueType(numNodes())); }
        inline auto hyperedgeIDs() const { return mutable_index_range<Hyperedge>(Hyperedge(0), Hyperedge::fromOtherValueType(numHyperedges())); }
        inline auto pinIndices() const { return PinIndexRange(PinIndex(0), PinIndex::fromOtherValueType(numPins())); }

        FlowHypergraph() : nodes(1), hyperedges(1) {}

        // use in FlowHypergraphBuilder to get rid of any allocations
        FlowHypergraph(size_t maxNumNodes, size_t maxNumHyperedges, size_t maxNumPins) :
            nodes(maxNumNodes + 1), hyperedges(maxNumHyperedges + 1), pins(maxNumPins), incident_hyperedges(maxNumPins) {}

        FlowHypergraph(std::vector<NodeWeight>& node_weights, std::vector<HyperedgeWeight>& hyperedge_weights, std::vector<PinIndex>& hyperedge_sizes,
                       std::vector<Node>& _pins) :
            maxHyperedgeCapacity(0),
            nodes(node_weights.size() + 1), hyperedges(hyperedge_weights.size() + 1), pins(_pins.size()), incident_hyperedges(_pins.size()),
            total_node_weight(std::accumulate(node_weights.begin(), node_weights.end(), NodeWeight(0))) {
            size_t i = 0;
            for (const Node p : _pins) {
                pins[i++].pin = p; // copy pins
                nodes[p + 1].first_out++; // bucket sizes
            }

            for (Node u : nodeIDs()) {
                nodes[u + 1].first_out += nodes[u].first_out; // prefix sum
                nodes[u].weight = node_weights[u]; // copy node weights
            }

            for (Hyperedge e : hyperedgeIDs()) {
                hyperedges[e].capacity = hyperedge_weights[e];
                hyperedges[e + 1].first_out = hyperedges[e].first_out + hyperedge_sizes[e]; // prefix sum
                for (auto pin_it = beginIndexPins(e); pin_it != endIndexPins(e); pin_it++) {
                    Pin& p = pins[pin_it];
                    InHeIndex ind_he = nodes[p.pin].first_out++; // destroy first_out temporarily and reset later
                    InHe& inc_he = incident_hyperedges[ind_he];
                    inc_he.e = e;
                    inc_he.pin_iter = pin_it; // set iterator for pin -> its position in the pins of the hyperedge
                    p.he_inc_iter = ind_he; // set iterator for incident hyperedge -> its position in incident_hyperedges of the node
                }
                maxHyperedgeCapacity = std::max(maxHyperedgeCapacity, hyperedges[e].capacity);
            }

            for (Node u(numNodes() - 1); u > 0; u--)
                nodes[u].first_out = nodes[u - 1].first_out; // reset temporarily destroyed first_out
            nodes[0].first_out = InHeIndex(0);
        }


        bool hasNodeWeights() const {
            return std::any_of(nodes.begin(), nodes.begin() + numNodes(), [](const NodeData& u) { return u.weight > 1; });
        }
        bool hasHyperedgeWeights() const {
            return std::any_of(hyperedges.begin(), hyperedges.begin() + numHyperedges(), [](const HyperedgeData& e) { return e.capacity > 1; });
        }
        inline size_t numNodes() const { return nodes.size() - 1; }
        inline size_t numHyperedges() const { return hyperedges.size() - 1; }
        inline size_t numPins() const { return pins.size(); }
        inline PinIndex pinCount(const Hyperedge e) const { return hyperedges[e + 1].first_out - hyperedges[e].first_out; }
        inline InHeIndex degree(const Node u) const { return nodes[u + 1].first_out - nodes[u].first_out; }
        inline NodeWeight totalNodeWeight() const { return total_node_weight; }
        inline NodeWeight nodeWeight(const Node u) const { return nodes[u].weight; }
        inline NodeWeight& nodeWeight(const Node u) { return nodes[u].weight; }

        inline InHeIndex beginIndexHyperedges(Node u) const { return nodes[u].first_out; }
        inline InHeIndex endIndexHyperedges(Node u) const { return nodes[u + 1].first_out; }
        // interface for irange is front(), drop_front(), empty(), size(), begin(), end()
        inline InHeIndexRange incidentHyperedgeIndices(const Node u) const { return InHeIndexRange(beginIndexHyperedges(u), endIndexHyperedges(u)); }
        inline InHe& getInHe(const InHeIndex ind_e) { return incident_hyperedges[ind_e]; }
        inline InHe& getInHe(const Pin& pin) { return getInHe(pin.he_inc_iter); }
        inline const InHe& getInHe(const InHeIndex ind_e) const { return incident_hyperedges[ind_e]; }
        inline const InHe& getInHe(const Pin& pin) const { return getInHe(pin.he_inc_iter); }

        inline PinIndex beginIndexPins(const Hyperedge e) const { return hyperedges[e].first_out; }
        inline PinIndex endIndexPins(const Hyperedge e) const { return hyperedges[e + 1].first_out; }
        inline PinIndexRange pinIndices(const Hyperedge e) const { return PinIndexRange(beginIndexPins(e), endIndexPins(e)); }
        inline Pin& getPin(const PinIndex ind_p) { return pins[ind_p]; }
        inline Pin& getPin(const InHe& inc_p) { return getPin(inc_p.pin_iter); }
        inline const Pin& getPin(const PinIndex ind_p) const { return pins[ind_p]; }
        inline const Pin& getPin(const InHe& inc_p) const { return getPin(inc_p.pin_iter); }


        inline InHeIterator beginHyperedges() { return incident_hyperedges.begin(); }
        inline InHeIterator endHyperedges() { return incident_hyperedges.end(); }
        inline InHeIterator beginHyperedges(const Node u) { return incident_hyperedges.begin() + nodes[u].first_out; }
        inline InHeIterator endHyperedges(const Node u) { return incident_hyperedges.begin() + nodes[u + 1].first_out; }
        InHeRange hyperedgesOf(const Node u) { return InHeRange(beginHyperedges(u), endHyperedges(u)); }
        InHeRange hyperedgesInRange(const InHeIndexRange hir) { return InHeRange(beginHyperedges() + hir.begin(), beginHyperedges() + hir.end()); }

        inline PinIterator beginPins() { return pins.begin(); }
        inline PinIterator endPins() { return pins.end(); }
        inline PinIterator beginPins(const Hyperedge e) { return pins.begin() + hyperedges[e].first_out; }
        inline PinIterator endPins(const Hyperedge e) { return pins.begin() + hyperedges[e + 1].first_out; }
        PinRange pinsOf(const Hyperedge e) { return PinRange(beginPins(e), endPins(e)); }
        PinRange pinsInRange(const PinIndexRange pir) { return PinRange(beginPins() + pir.begin(), beginPins() + pir.end()); }

        inline Flow capacity(const Hyperedge e) const { return hyperedges[e].capacity; }
        inline Flow& capacity(const Hyperedge e) { return hyperedges[e].capacity; }

        // for testing only
        InHe& findIncidence(const Node u, const Hyperedge e) {
            for (InHe& x : hyperedgesOf(u))
                if (x.e == e)
                    return x;
            throw std::out_of_range("e is not in the list of incident hyperedges of u");
        }

        // for testing only
        Pin& findPin(const Hyperedge e, const Node v) {
            for (Pin& x : pinsOf(e))
                if (x.pin == v)
                    return x;
            throw std::out_of_range("v is not a pin of e");
        }

        Flow maxHyperedgeCapacity = maxFlow;

    protected:
        std::vector<NodeData> nodes;
        std::vector<HyperedgeData> hyperedges;
        std::vector<Pin> pins;
        std::vector<InHe> incident_hyperedges;

        NodeWeight total_node_weight = NodeWeight(0);

        static_assert(std::is_trivially_destructible<Pin>::value);
        static_assert(std::is_trivially_destructible<InHe>::value);
        static_assert(std::is_trivially_destructible<HyperedgeData>::value);
        static_assert(std::is_trivially_destructible<NodeData>::value);
        static_assert(std::is_trivially_destructible<PinIndexRange>::value);

    public:
        void printNodes(std::ostream& out) {
            out << "---Nodes---\n";
            for (const Node u : nodeIDs()) {
                out << u << " deg = " << degree(u) << " w= " << nodeWeight(u) << " inc_hes = [";
                for (const InHe e : hyperedgesOf(u))
                    out << e.e << " ";
                out << "]"
                    << "\n";
            }
            out << std::flush;
        }

        void printHyperedges(std::ostream& out) {
            out << "---Hyperedges---\n";
            for (const Hyperedge e : hyperedgeIDs()) {
                out << e << " pincount = " << pinCount(e) << " w= " << capacity(e) << " pins = [";
                for (const Pin& u : pinsOf(e)) {
                    out << u.pin << " ";
                }
                out << "]"
                    << "\n";
            }
            out << std::flush;
        }

        void printHypergraph(std::ostream& out) {
            printNodes(out);
            printHyperedges(out);
        }

        friend std::ostream& operator<<(std::ostream& out, FlowHypergraph& hg) noexcept {
            hg.printHypergraph(out);
            return out;
        }
    };
} // namespace whfc
