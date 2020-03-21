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
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef _V3SCOREBOARD_H_
#define _V3SCOREBOARD_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"

#include <map>
#include VL_INCLUDE_UNORDERED_MAP
#include VL_INCLUDE_UNORDERED_SET

//######################################################################
// SortByValueMap

/// A generic key-value map, except it also supports iterating in
/// value-sorted order.  Values need not be unique. Uses T_KeyCompare to
/// break ties in the sort when values collide.

template <typename T_Key, typename T_Value, class T_KeyCompare = std::less<T_Key> >
class SortByValueMap {
    // TYPES
private:
    typedef vl_unordered_map<T_Key, T_Value> Key2Val;
    typedef std::set<T_Key, T_KeyCompare> KeySet;
    typedef std::map<T_Value, KeySet> Val2Keys;

    // MEMBERS
    Key2Val m_keys;  // Map each key to its value. Not sorted.
    Val2Keys m_vals;  // Map each value to its keys. Sorted.

public:
    // CONSTRUCTORS
    SortByValueMap() {}

    class const_iterator {
        // TYPES
    public:
        typedef const_iterator value_type;
        typedef const_iterator reference;  // See comment on operator*()
        typedef void pointer;
        typedef std::ptrdiff_t difference_type;
        typedef std::bidirectional_iterator_tag iterator_category;
    protected:
        friend class SortByValueMap;

        // MEMBERS
        typename KeySet::iterator m_keyIt;
        typename Val2Keys::iterator m_valIt;
        SortByValueMap* m_sbvmp;
        bool m_end;  // At the end()

        // CONSTRUCTORS
        explicit const_iterator(SortByValueMap* sbmvp)  // for end()
            : m_sbvmp(sbmvp)
            , m_end(true) {}
        const_iterator(typename Val2Keys::iterator valIt,
                       typename KeySet::iterator keyIt,
                       SortByValueMap* sbvmp)
            : m_keyIt(keyIt)
            , m_valIt(valIt)
            , m_sbvmp(sbvmp)
            , m_end(false) {}

        // METHODS
        void advanceUntilValid() {
            ++m_keyIt;
            if (m_keyIt != m_valIt->second.end()) {  // Valid iterator, done.
                return;
            }
            // Try the next value?
            ++m_valIt;
            if (m_valIt == m_sbvmp->m_vals.end()) {  // No more values
                m_end = true;
                return;
            }
            // Should find a value here, as every value bucket is supposed
            // to have at least one key, even after keys get removed.
            m_keyIt = m_valIt->second.begin();
            UASSERT(m_keyIt != m_valIt->second.end(), "Algorithm should have key left");
        }
        void reverseUntilValid() {
            if (m_end) {
                UASSERT(!m_sbvmp->m_vals.empty(), "Reverse iterator causes underflow");
                m_valIt = m_sbvmp->m_vals.end();
                --m_valIt;

                UASSERT(!m_valIt->second.empty(), "Reverse iterator causes underflow");
                m_keyIt = m_valIt->second.end();
                --m_keyIt;

                m_end = false;
                return;
            }
            if (m_keyIt != m_valIt->second.begin()) {
                // Valid iterator, we're done.
                --m_keyIt;
                return;
            }
            // Try the previous value?
            if (VL_UNCOVERABLE(m_valIt == m_sbvmp->m_vals.begin())) {
                // No more values but it's not defined to decrement an
                // iterator past the beginning.
                v3fatalSrc("Decremented iterator past beginning");
                return;
            }
            --m_valIt;
            // Should find a value here, as Every value bucket is supposed
            // to have at least one key, even after keys get removed.
            UASSERT(!m_valIt->second.empty(), "Value bucket should have key");
            m_keyIt = m_valIt->second.end();
            --m_keyIt;
            UASSERT(m_keyIt != m_valIt->second.end(), "Value bucket should have key");
        }
    public:
        const T_Key& key() const { return *m_keyIt; }
        const T_Value& value() const { return m_valIt->first; }
        const_iterator& operator++() {
            advanceUntilValid();
            return *this;
        }
        const_iterator& operator--() {
            reverseUntilValid();
            return *this;
        }
        bool operator==(const const_iterator& other) const {
            // It's not legal to compare iterators from different
            // sequences.  So check m_end before comparing m_valIt, and
            // compare m_valIt's before comparing m_keyIt to ensure nothing
            // here is undefined.
            if (m_end || other.m_end) {
                return m_end && other.m_end;
            }
            return ((m_valIt == other.m_valIt)
                    && (m_keyIt == other.m_keyIt));
        }
        bool operator!=(const const_iterator& other) const {
            return (!this->operator==(other));
        }

        // WARNING: Cleverness.
        //
        // The "reference" returned by *it must remain valid after 'it'
        // gets destroyed. The reverse_iterator relies on this for its
        // operator*(), so it's not just a theoretical requirement, it's a
        // real requirement.
        //
        // To make that work, define the "reference" type to be the
        // iterator itself. So clients can do (*it).key() and
        // (*it).value(). This is the clever part.
        //
        // That's mostly useful for a reverse iterator, where *rit returns
        // the forward iterator pointing the to same element, so
        // (*rit).key() and (*rit).value() work where rit.key() and
        // rit.value() cannot.
        //
        // It would be nice to support it->key() and it->value(), however
        // uncertain what would be an appropriate 'pointer' type define
        // that makes this work safely through a reverse iterator. So this
        // class does not provide an operator->().
        //
        // Q) Why not make our value_type be a pair<T_Key, T_Value> like a
        //    normal map, and return a reference to that?  This could
        //    return a reference to one of the pairs inside m_keys, that
        //    would satisfy the constraint above.
        //
        // A) It would take a lookup to find that pair within m_keys. This
        //    iterator is designed to minimize the number of hashtable and
        //    tree lookups. Increment, decrement, key(), value(), erase()
        //    by iterator, begin(), end() -- none of these require a
        //    container lookup. That's true for reverse_iterators too.
        reference operator*() const {
            UASSERT(!m_end, "Dereferencing iterator that is at end()");
            return *this;
        }
    };

    class iterator : public const_iterator {
    public:
        // TYPES
        typedef iterator value_type;
        typedef iterator reference;
        // pointer, difference_type, and iterator_category inherit from
        // const_iterator

        // CONSTRUCTORS
        explicit iterator(SortByValueMap* sbvmp)
            : const_iterator(sbvmp) {}
        iterator(typename Val2Keys::iterator valIt,
                 typename KeySet::iterator keyIt,
                 SortByValueMap* sbvmp)
            : const_iterator(valIt, keyIt, sbvmp) {}

        // METHODS
        iterator& operator++() {
            this->advanceUntilValid();
            return *this;
        }
        iterator& operator--() {
            this->reverseUntilValid();
            return *this;
        }
        reference operator*() const {
            UASSERT(!this->m_end, "Dereferencing iterator that is at end()");
            return *this;
        }
    };

    typedef std::reverse_iterator<iterator> reverse_iterator;
    typedef std::reverse_iterator<const_iterator> const_reverse_iterator;

    // METHODS
private:
    void removeKeyFromOldVal(const T_Key& k, const T_Value& oldVal) {
        // The value of 'k' is about to change, or, 'k' is about to be
        // removed from the map.
        // Clear the m_vals mapping for k.
        KeySet& keysAtOldVal = m_vals[oldVal];
        size_t erased = keysAtOldVal.erase(k);
        UASSERT(erased == 1, "removeKeyFromOldVal() removal key not found");
        if (keysAtOldVal.empty()) {
            // Don't keep empty sets in the value map.
            m_vals.erase(oldVal);
        }
    }
    void removeKeyFromOldVal(iterator it) {
        it.m_valIt->second.erase(it.m_keyIt);
        if (it.m_valIt->second.empty()) {
            m_vals.erase(it.m_valIt);
        }
    }

public:
    iterator begin() {
        typename Val2Keys::iterator valIt = m_vals.begin();
        if (valIt == m_vals.end()) {
            return end();
        }
        typename KeySet::const_iterator keyIt = valIt->second.begin();
        return iterator(valIt, keyIt, this);
    }
    const_iterator begin() const {
        SortByValueMap* mutp = const_cast<SortByValueMap*>(this);
        typename Val2Keys::iterator valIt = mutp->m_vals.begin();
        if (valIt == mutp->m_vals.end()) {
            return end();
        }
        typename KeySet::const_iterator keyIt = valIt->second.begin();
        return const_iterator(valIt, keyIt, mutp);
    }
    iterator end() {
        return iterator(this);
    }
    const_iterator end() const {
        // Safe to cast away const; the const_iterator will still enforce
        // it. Same for the const begin() below.
        return const_iterator(const_cast<SortByValueMap*>(this));
    }
    reverse_iterator rbegin() {
        return reverse_iterator(end());
    }
    reverse_iterator rend() {
        return reverse_iterator(begin());
    }
    const_reverse_iterator rbegin() const {
        return const_reverse_iterator(end());
    }
    const_reverse_iterator rend() const {
        return const_reverse_iterator(begin());
    }

    iterator find(const T_Key& k) {
        typename Key2Val::iterator kvit = m_keys.find(k);
        if (kvit == m_keys.end()) return end();

        typename Val2Keys::iterator valIt = m_vals.find(kvit->second);
        typename KeySet::iterator keyIt = valIt->second.find(k);
        return iterator(valIt, keyIt, this);
    }
    const_iterator find(const T_Key& k) const {
        SortByValueMap* mutp = const_cast<SortByValueMap*>(this);
        typename Key2Val::iterator kvit = mutp->m_keys.find(k);
        if (kvit == mutp->m_keys.end()) return end();

        typename Val2Keys::iterator valIt = mutp->m_vals.find(kvit->second);
        typename KeySet::iterator keyIt = valIt->second.find(k);
        return const_iterator(valIt, keyIt, mutp);
    }
    void set(const T_Key& k, const T_Value& v) {
        typename Key2Val::iterator kvit = m_keys.find(k);
        if (kvit != m_keys.end()) {
            if (kvit->second == v) {
                return;  // Same value already present; stop.
            }
            // Must remove element from m_vals[oldValue]
            removeKeyFromOldVal(k, kvit->second);
        }
        m_keys[k] = v;
        m_vals[v].insert(k);
    }
    size_t erase(const T_Key& k) {
        typename Key2Val::iterator kvit = m_keys.find(k);
        if (kvit == m_keys.end()) return 0;
        removeKeyFromOldVal(k, kvit->second);
        m_keys.erase(kvit);
        return 1;
    }
    void erase(const iterator& it) {
        m_keys.erase(it.key());
        removeKeyFromOldVal(it);
    }
    void erase(const reverse_iterator& it) {
        erase(*it);  // Dereferencing returns a copy of the forward iterator
    }
    bool has(const T_Key& k) const {
        return (m_keys.find(k) != m_keys.end());
    }
    bool empty() const {
        return m_keys.empty();
    }
    // Look up a value. Returns a reference for efficiency. Note this must
    // be a const reference, otherwise the client could corrupt the sorted
    // order of m_byValue by reaching through and changing the value.
    const T_Value& at(const T_Key& k) const {
        typename Key2Val::const_iterator kvit = m_keys.find(k);
        UASSERT(kvit != m_keys.end(), "at() lookup key not found");
        return kvit->second;
    }

private:
    VL_UNCOPYABLE(SortByValueMap);
};

//######################################################################

/// V3Scoreboard takes a set of Elem*'s, each having some score.
/// Scores are assigned by a user-supplied scoring function.
///
/// At any time, the V3Scoreboard can return the elem with the "best" score
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

template <typename T_Elem,
          typename T_Score,
          class T_ElemCompare = std::less<T_Elem> >
class V3Scoreboard {
private:
    // TYPES
    typedef vl_unordered_set<const T_Elem*> NeedRescoreSet;
    class CmpElems {
    public:
        bool operator() (const T_Elem* const& ap, const T_Elem* const& bp) const {
            T_ElemCompare cmp;
            return cmp.operator()(*ap, *bp);
        }
    };
    typedef SortByValueMap<const T_Elem*, T_Score, CmpElems> SortedMap;
    typedef T_Score (*UserScoreFnp)(const T_Elem*);

    // MEMBERS
    NeedRescoreSet m_unknown;  // Elements with unknown scores
    SortedMap m_sorted;  // Set of elements with known scores
    UserScoreFnp m_scoreFnp;  // Scoring function
    bool m_slowAsserts;  // Do some asserts that require extra lookups

public:
    // CONSTRUCTORS
    explicit V3Scoreboard(UserScoreFnp scoreFnp, bool slowAsserts)
        : m_scoreFnp(scoreFnp)
        , m_slowAsserts(slowAsserts) {}
    ~V3Scoreboard() {}

    // METHODS

    // Add an element to the scoreboard.
    // Element begins in needs-rescore state; it won't be returned by
    // bestp() until after the next rescore().
    void addElem(const T_Elem* elp) {
        if (m_slowAsserts) {
            UASSERT(!contains(elp),
                    "Adding element to scoreboard that was already in scoreboard");
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
    // elements whose scores are known. Returns NULL if no elements with
    // known scores exist.
    //
    // Note: This does not automatically rescore. Client must call
    // rescore() periodically to ensure all elems in the scoreboard are
    // reflected in the result of bestp(). Otherwise, bestp() only
    // considers elements that aren't pending rescore.
    const T_Elem* bestp() {
        typename SortedMap::iterator result = m_sorted.begin();
        if (VL_UNLIKELY(result == m_sorted.end())) return NULL;
        return (*result).key();
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
    bool needsRescore(const T_Elem* elp) {
        return (m_unknown.find(elp) != m_unknown.end());
    }
    // Retrieve the last known score for an element.
    T_Score cachedScore(const T_Elem* elp) {
        typename SortedMap::iterator result = m_sorted.find(elp);
        UASSERT(result != m_sorted.end(),
                "V3Scoreboard::cachedScore() failed to find element");
        return (*result).value();
    }
    // For each element whose score is unknown to V3Scoreboard,
    // call the client's scoring function to get a new score,
    // and sort all elements by their current score.
    void rescore() {
        for (typename NeedRescoreSet::iterator it = m_unknown.begin();
             it != m_unknown.end(); ++it) {
            const T_Elem* elp = *it;
            T_Score sortScore = m_scoreFnp(elp);
            m_sorted.set(elp, sortScore);
        }
        m_unknown.clear();
    }

private:
    VL_UNCOPYABLE(V3Scoreboard);
};

//######################################################################

namespace V3ScoreboardBase {
    void selfTest();
}

#endif  // Guard
