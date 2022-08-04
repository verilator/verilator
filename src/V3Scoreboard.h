// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Scoreboards for thread partitioner
//
// Provides scoreboard classes:
//
//  * SortByValueMap
//  * V3Scoreboard
//
// See details below
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

#include <functional>
#include <map>
#include <set>
#include <unordered_map>

// ######################################################################
//  SortByValueMap

// A generic key-value map, except iteration is in *value* sorted order. Values need not be unique.
// Uses T_KeyCompare to break ties in the sort when values collide. Note: Only const iteration is
// possible, as updating mapped values via iterators is not safe.

template <typename T_Key, typename T_Value, class T_KeyCompare = std::less<T_Key>>
class SortByValueMap final {
    // Current implementation is a std::set of key/value pairs, plus a std_unordered_map from keys
    // to iterators into the set. This keeps most operations fairly cheap and also has the benefit
    // of being able to re-use the std::set iterators.

    // TYPES

    using Pair = std::pair<T_Key, T_Value>;

    struct PairCmp final {
        bool operator()(const Pair& a, const Pair& b) const {
            // First compare values
            if (a.second != b.second) return a.second < b.second;
            // Then compare keys
            return T_KeyCompare{}(a.first, b.first);
        }
    };

    using PairSet = std::set<Pair, PairCmp>;

public:
    using const_iterator = typename PairSet::const_iterator;
    using const_reverse_iterator = typename PairSet::const_reverse_iterator;

private:
    // MEMBERS
    PairSet m_pairs;  // The contents of the map, stored directly as key-value pairs
    std::unordered_map<T_Key, const_iterator> m_kiMap;  // Key to iterator map

    VL_UNCOPYABLE(SortByValueMap);

public:
    // CONSTRUCTORS
    SortByValueMap() = default;

    // Only const iteration is possible
    const_iterator begin() const { return m_pairs.begin(); }
    const_iterator end() const { return m_pairs.end(); }
    const_iterator cbegin() const { m_pairs.cbegin(); }
    const_iterator cend() const { return m_pairs.cend(); }
    const_reverse_iterator rbegin() const { return m_pairs.rbegin(); }
    const_reverse_iterator rend() const { return m_pairs.rend(); }
    const_reverse_iterator crbegin() const { return m_pairs.crbegin(); }
    const_reverse_iterator crend() const { return m_pairs.crend(); }

    const_iterator find(const T_Key& key) const {
        const auto kiIt = m_kiMap.find(key);
        if (kiIt == m_kiMap.end()) return cend();
        return kiIt->second;
    }
    size_t erase(const T_Key& key) {
        const auto kiIt = m_kiMap.find(key);
        if (kiIt == m_kiMap.end()) return 0;
        m_pairs.erase(kiIt->second);
        m_kiMap.erase(kiIt);
        return 1;
    }
    void erase(const_iterator it) {
        m_kiMap.erase(it->first);
        m_pairs.erase(it);
    }
    void erase(const_reverse_iterator rit) {
        m_kiMap.erase(rit->first);
        m_pairs.erase(std::next(rit).base());
    }
    bool has(const T_Key& key) const { return m_kiMap.count(key); }
    bool empty() const { return m_pairs.empty(); }
    // Returns const reference.
    const T_Value& at(const T_Key& key) const { return m_kiMap.at(key)->second; }
    // Note this returns const_iterator
    template <typename... Args>  //
    std::pair<const_iterator, bool> emplace(const T_Key& key, Args&&... args) {
        const auto kiEmp = m_kiMap.emplace(key, end());
        if (kiEmp.second) {
            const auto result = m_pairs.emplace(key, std::forward<Args>(args)...);
#if VL_DEBUG
            UASSERT(result.second, "Should not be in set yet");
#endif
            kiEmp.first->second = result.first;
            return result;
        }
        return {kiEmp.first->second, false};
    }
    // Invalidates iterators
    void update(const_iterator it, T_Value value) {
        const auto kiIt = m_kiMap.find(it->first);
        m_pairs.erase(it);
        kiIt->second = m_pairs.emplace(kiIt->first, value).first;
    }
};

//######################################################################

/// V3Scoreboard takes a set of Elem*'s, each having some score.
/// Scores are assigned by a user-supplied scoring function.
///
/// At any time, the V3Scoreboard can return th515e elem with the "best" score
/// among those elements whose scores are known.
///
/// The best score is the _lowest_ score. This makes sense in contexts
/// where scores represent costs.
///
/// The Scoreboard supports mutating element scores efficiently. The client
/// must hint to the V3Scoreboard when an element's score may have
/// changed. When it receives this hint, the V3Scoreboard will move the
/// element into the set of elements whose scores are unknown. Later the
/// client can tell V3Scoreboard to re-sort the list, which it does
/// incrementally, by re-scoring all elements whose scores are unknown, and
/// then moving these back into the score-sorted map. This is efficient
/// when the subset of elements whose scores change is much smaller than
/// the full set size.

template <typename T_Elem, typename T_Score, class T_ElemCompare = std::less<T_Elem>>
class V3Scoreboard final {
private:
    // TYPES
    class CmpElems final {
    public:
        bool operator()(const T_Elem* const& ap, const T_Elem* const& bp) const {
            const T_ElemCompare cmp;
            return cmp.operator()(*ap, *bp);
        }
    };
    using SortedMap = SortByValueMap<const T_Elem*, T_Score, CmpElems>;
    using UserScoreFnp = T_Score (*)(const T_Elem*);

    // MEMBERS
    // Below uses set<> not an unordered_set<>. unordered_set::clear() and
    // construction results in a 491KB clear operation to zero all the
    // buckets. Since the set size is generally small, and we iterate the
    // set members, set is better performant.
    std::set<const T_Elem*> m_unknown;  // Elements with unknown scores
    SortedMap m_sorted;  // Set of elements with known scores
    const UserScoreFnp m_scoreFnp;  // Scoring function
    const bool m_slowAsserts;  // Do some asserts that require extra lookups

public:
    // CONSTRUCTORS
    explicit V3Scoreboard(UserScoreFnp scoreFnp, bool slowAsserts)
        : m_scoreFnp{scoreFnp}
        , m_slowAsserts{slowAsserts} {}
    ~V3Scoreboard() = default;

    // METHODS

    // Add an element to the scoreboard.
    // Element begins in needs-rescore state; it won't be returned by
    // bestp() until after the next rescore().
    void addElem(const T_Elem* elp) {
        if (m_slowAsserts) {
            UASSERT(!contains(elp), "Adding element to scoreboard that was already in scoreboard");
        }
        m_unknown.insert(elp);
    }

    // Remove elp from scoreboard.
    void removeElem(const T_Elem* elp) {
        if (0 == m_sorted.erase(elp)) {
            UASSERT(m_unknown.erase(elp),
                    "Could not find requested elem to remove from scoreboard");
        }
    }

    // Returns true if elp is present in the scoreboard, false otherwise.
    //
    // Note: every other V3Scoreboard routine that takes an T_Elem* has
    // undefined behavior if the element is not in the scoreboard.
    bool contains(const T_Elem* elp) const {
        if (m_unknown.find(elp) != m_unknown.end()) return true;
        return (m_sorted.find(elp) != m_sorted.end());
    }

    // Get the best element, with the lowest score (lower is better), among
    // elements whose scores are known. Returns nullptr if no elements with
    // known scores exist.
    //
    // Note: This does not automatically rescore. Client must call
    // rescore() periodically to ensure all elems in the scoreboard are
    // reflected in the result of bestp(). Otherwise, bestp() only
    // considers elements that aren't pending rescore.
    const T_Elem* bestp() {
        const auto it = m_sorted.begin();
        if (VL_UNLIKELY(it == m_sorted.end())) return nullptr;
        return it->first;
    }

    // Tell the scoreboard that this element's score may have changed.
    //
    // At the time of this call, the element's score becomes "unknown"
    // to the V3Scoreboard. Unknown elements won't be returned by bestp().
    // The element's score will remain unknown until the next rescore().
    //
    // The client MUST call this for each element whose score has changed.
    //
    // The client MAY call this for elements whose score has not changed.
    // Doing so incurs some compute cost (to re-sort the element back to
    // its original location) and still makes it ineligible to be returned
    // by bestp() until the next rescore().
    void hintScoreChanged(const T_Elem* elp) {
        m_unknown.insert(elp);
        m_sorted.erase(elp);
    }

    // True if any element's score is unknown to V3Scoreboard.
    bool needsRescore() { return !m_unknown.empty(); }
    // False if elp's score is known to V3Scoreboard,
    // else true if elp's score is unknown until the next rescore().
    bool needsRescore(const T_Elem* elp) { return m_unknown.count(elp); }
    // Retrieve the last known score for an element.
    T_Score cachedScore(const T_Elem* elp) { return m_sorted.at(elp); }
    // For each element whose score is unknown to V3Scoreboard,
    // call the client's scoring function to get a new score,
    // and sort all elements by their current score.
    void rescore() {
        for (const T_Elem* elp : m_unknown) {
            VL_ATTR_UNUSED const bool exists = !m_sorted.emplace(elp, m_scoreFnp(elp)).second;
#if VL_DEBUG
            UASSERT(!exists, "Should not be in both m_unknown and m_sorted");
#endif
        }
        m_unknown.clear();
    }

private:
    VL_UNCOPYABLE(V3Scoreboard);
};

//######################################################################

namespace V3ScoreboardBase {
void selfTest();
}  // namespace V3ScoreboardBase

#endif  // Guard
