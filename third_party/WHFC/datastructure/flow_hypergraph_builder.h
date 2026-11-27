#pragma once

#include "flow_hypergraph.h"

/*
 * hyperedges with zero/one pins are removed automatically during build process
 */

namespace whfc {
    class FlowHypergraphBuilder : public FlowHypergraph {
    public:
        using Base = FlowHypergraph;

        FlowHypergraphBuilder() : Base() { clear(); }

        explicit FlowHypergraphBuilder(size_t nNodes) { reinitialize(nNodes); }

        // use to get rid of any allocations
        FlowHypergraphBuilder(size_t maxNumNodes, size_t maxNumHyperedges, size_t maxNumPins) : Base(maxNumNodes, maxNumHyperedges, maxNumPins) {
            // don't do clean-up here yet, so that we can use the numbers for allocating the remaining datastructures
        }

        void clear() {
            finalized = false;
            numPinsAtHyperedgeStart = 0;
            maxHyperedgeCapacity = 0;

            nodes.clear();
            hyperedges.clear();
            pins.clear();
            incident_hyperedges.clear();
            total_node_weight = NodeWeight(0);

            // sentinels
            nodes.push_back({ InHeIndex(0), NodeWeight(0) });
            hyperedges.push_back({ PinIndex(0), Flow(0) });
        }

        void reinitialize(size_t numNodes) {
            clear();
            nodes.resize(numNodes + 1);
        }

        void addNode(const NodeWeight w) {
            nodes.back().weight = w;
            nodes.push_back({ InHeIndex(0), NodeWeight(0) });
        }

        void startHyperedge(const Flow capacity) {
            finishHyperedge(); // finish last hyperedge
            hyperedges.back().capacity = capacity; // exploit sentinel
            numPinsAtHyperedgeStart = numPins();
            maxHyperedgeCapacity = std::max(maxHyperedgeCapacity, capacity);
        }

        void addPin(const Node u) {
            assert(u < numNodes());
            pins.push_back({ u, InHeIndex::Invalid() });
            nodes[u + 1].first_out++;
        }

        size_t currentHyperedgeSize() const { return numPins() - numPinsAtHyperedgeStart; }

        void removeCurrentHyperedge() {
            while (numPins() > numPinsAtHyperedgeStart)
                removeLastPin();
        }

        void finalize() {
            if (!finishHyperedge()) // finish last open hyperedge
                hyperedges.back().capacity = 0; // maybe the last started hyperedge has zero/one pins and thus we still use the previous sentinel. was never a
                                                // bug, since that capacity is never read

            total_node_weight = NodeWeight(0);
            for (Node u : nodeIDs()) {
                nodes[u + 1].first_out += nodes[u].first_out;
                total_node_weight += nodes[u].weight;
            }

            incident_hyperedges.resize(numPins());
            for (Hyperedge e : hyperedgeIDs()) {
                for (auto pin_it = beginIndexPins(e); pin_it != endIndexPins(e); pin_it++) {
                    Pin& p = pins[pin_it];
                    InHeIndex ind_he = nodes[p.pin].first_out++; // destroy first_out temporarily and reset later
                    incident_hyperedges[ind_he] = { e, pin_it };
                    p.he_inc_iter = ind_he; // set iterator for incident hyperedge -> its position in incident_hyperedges of the node
                }
            }

            for (Node u(numNodes() - 1); u > 0; u--)
                nodes[u].first_out = nodes[u - 1].first_out; // reset temporarily destroyed first_out
            nodes[0].first_out = InHeIndex(0);

            finalized = true;
        }

        void shrink_to_fit() {
            nodes.shrink_to_fit();
            hyperedges.shrink_to_fit();
            pins.shrink_to_fit();
            incident_hyperedges.shrink_to_fit();
        }

    private:
        void removeLastPin() {
            nodes[pins.back().pin + 1].first_out--;
            pins.pop_back();
        }

        bool finishHyperedge() {
            if (currentHyperedgeSize() == 1) {
                removeLastPin();
            }

            if (currentHyperedgeSize() > 0) {
                hyperedges.push_back({ PinIndex::fromOtherValueType(numPins()), Flow(0) }); // sentinel
                return true;
            }
            return false;
        }

        bool finalized = false;
        size_t numPinsAtHyperedgeStart = 0;
    };
} // namespace whfc
