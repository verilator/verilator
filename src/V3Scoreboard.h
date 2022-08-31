// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Scoreboard for mtask coarsening
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3SCOREBOARD_H_
#define VERILATOR_V3SCOREBOARD_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3PairingHeap.h"

//===============================================================================================
// V3Scoreboard is essentially a heap that can be hinted that some elements have changed keys, at
// which points those elements will be deferred as 'unknown' until the next 'rescore' call. We
// largely reuse the implementation of the slightly more generic PairingHeap, but we do rely on the
// internal structure of the PairingHeap so changing that class requires changing this.
//
// For efficiency, the elements themselves must be the heap nodes, by deriving them from
// V3Scoreboard<T_Elem, T_Key>::Node. This also means a single element can only be associated with
// a single scoreboard.

template <typename T_Elem, typename T_Key>
class V3Scoreboard final {
    // TYPES
    using Heap = PairingHeap<T_Key>;

public:
    using Node = typename Heap::Node;

private:
    using Link = typename Heap::Link;

    // Note: T_Elem is incomplete here, so we cannot assert 'std::is_base_of<Node, T_Elem>::value'

    // MEMBERS
    Heap m_known;  // The heap of entries with known scores
    Link m_unknown;  // List of entries with unknown scores

public:
    // CONSTRUCTORS
    explicit V3Scoreboard() = default;
    ~V3Scoreboard() = default;

private:
    VL_UNCOPYABLE(V3Scoreboard);

    // METHODSs
    void addUnknown(T_Elem* nodep) {
        // Just prepend it to the list of unknown entries
        nodep->m_next.link(m_unknown.unlink());
        m_unknown.linkNonNull(nodep);
        // We mark nodes on the unknown list by making their child pointer point to themselves
        nodep->m_kids.m_ptr = nodep;
    }

public:
    // Returns true if the element is present in the scoreboard, false otherwise. Every other
    // method that takes a T_Elem* (except for 'add') has undefined behavior if the element is not
    // in this scoreboard. Furthermore, this method is only valid if the element can only possibly
    // be in this scoreboard. That is: if the element might be in another scoreboard, the behaviour
    // of this method is undefined.
    static bool contains(const T_Elem* nodep) { return nodep->m_ownerpp; }

    // Add an element to the scoreboard. This will not be returned before the next 'rescore' call.
    void add(T_Elem* nodep) {
#if VL_DEBUG
        UASSERT(!contains(nodep), "Adding element to scoreboard that was already in a scoreboard");
#endif
        addUnknown(nodep);
    }

    // Remove element from scoreboard.
    void remove(T_Elem* nodep) {
        if (nodep->m_kids.m_ptr == nodep) {
            // Node is on the unknown list, replace with next
            nodep->replaceWith(nodep->m_next.unlink());
            return;
        }
        // Node is in the known heap, remove it
        m_known.remove(nodep);
    }

    // Get the known element with the highest score (as we are using a max-heap), or nullptr if
    // there are no elements with known entries. This does not automatically 'rescore'. The client
    // must call 'rescore' appropriately to ensure all elements in the scoreboard are reflected in
    // the result of this method.
    T_Elem* best() const { return T_Elem::heapNodeToElem(m_known.max()); }

    // Tell the scoreboard that this element's score may have changed. At the time of this call,
    // the element's score becomes 'unknown' to the scoreboard. Unknown elements will not be
    // returned by 'best until the next call to 'rescore'.
    void hintScoreChanged(T_Elem* nodep) {
        // If it's already in the unknown list, then nothing to do
        if (nodep->m_kids.m_ptr == nodep) return;
        // Otherwise it was in the heap, remove it
        m_known.remove(nodep);
        // Prepend it to the unknown list
        addUnknown(nodep);
    }

    // True if we have elements with unknown score
    bool needsRescore() const { return m_unknown; }

    // True if the element's score is unknown, false otherwise.
    static bool needsRescore(const T_Elem* nodep) { return nodep->m_kids.m_ptr == nodep; }

    // For each element whose score is unknown, recompute the score and add to the known heap
    void rescore() {
        // Rescore and insert all unknown elements
        for (Node *nodep = m_unknown.unlink(), *nextp; nodep; nodep = nextp) {
            // Pick up next
            nextp = nodep->m_next.ptr();
            // Reset pointers
            nodep->m_next.m_ptr = nullptr;
            nodep->m_kids.m_ptr = nullptr;
            nodep->m_ownerpp = nullptr;
            // Re-compute the score of the element
            T_Elem::heapNodeToElem(nodep)->rescore();
            // re-insert into the heap
            m_known.insert(nodep);
        }
    }
};

// ######################################################################

namespace V3ScoreboardBase {
void selfTest();
}  // namespace V3ScoreboardBase

#endif  // Guard
