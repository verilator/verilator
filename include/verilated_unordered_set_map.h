// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: pre-C++11 replacements for std::unordered_set
//                         and std::unordered_map.
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

//*************************************************************************
// This file has clones of the std::unordered_set and std::unordered_map
// hash table types. They are here so that Verilator can use hash tables
// in pre-C++11 compilers, and the same client code can link against the
// std:: types when they are available.
//
// The implementations in this file do not implement the complete APIs
// of the std:: types. Nor are they correct in every detail,
// notably, the const_iterators do not enforce constness. We can extend
// these implementations to cover more of the std API as needed.
//
// TODO: In the future, when Verilator requires C++11 to compile,
//       remove this entire file and switch to the std:: types.
//
//*************************************************************************

#ifndef _V3_UNORDERED_SET_MAP_H_
#define _V3_UNORDERED_SET_MAP_H_

#include "verilatedos.h"

#include <list>
#include <stdexcept>
#include <string>

// Abstract 'vl_hash' and 'vl_equal_to' templates.
template <typename T> struct vl_hash {
    size_t operator()(const T& k) const;
};

template <typename T> struct vl_equal_to {
    bool operator()(const T& a, const T& b) const;
};

// Specializations of 'vl_hash' and 'vl_equal_to'.
inline size_t vl_hash_bytes(const void* vbufp, size_t nbytes) {
    const vluint8_t* bufp = static_cast<const vluint8_t*>(vbufp);
    size_t hash = 0;
    for (size_t i = 0; i < nbytes; i++) {
        hash = bufp[i] + 31u * hash;  // the K&R classic!
    }
    return hash;
}

template <> inline size_t
vl_hash<unsigned int>::operator()(const unsigned int& k) const {
    return k;
}

template <> inline bool
vl_equal_to<unsigned int>::operator()(const unsigned int& a,
                                      const unsigned int& b) const {
    return a == b;
}

template <> inline size_t
vl_hash<std::string>::operator()(const std::string& k) const {
    return vl_hash_bytes(k.data(), k.size());
}

template <> inline bool
vl_equal_to<std::string>::operator()(const std::string& a,
                                     const std::string& b) const {
    // Don't scan the strings if the sizes are different.
    if (a.size() != b.size()) {
        return false;
    }
    return (0 == a.compare(b));  // Must scan.
}

template <typename T> struct vl_hash<T*> {
    size_t operator()(T* kp) const {
        return ((sizeof(size_t) == sizeof(kp))
                ? reinterpret_cast<size_t>(kp)
                : vl_hash_bytes(&kp, sizeof(kp)));
    }
};

template <typename T> struct vl_equal_to<T*> {
    bool operator()(T* ap, T* bp) const {
        return ap == bp;
    }
};

//===================================================================
//
/// Functional clone of the std::unordered_set hash table.
template <class T_Key,
          class T_Hash = vl_hash<T_Key>,
          class T_Equal = vl_equal_to<T_Key> >
class vl_unordered_set {
public:
    // TYPES
    typedef std::list<T_Key> Bucket;
    enum RehashType { GROW, SHRINK };

    template <class KK, class VV,
              class HH, class EQ> friend class vl_unordered_map;

    class iterator {
    protected:
        // MEMBERS
        size_t m_bucketIdx;  //  Bucket this iterator points into
        typename Bucket::iterator m_bit;  // Bucket-local iterator
        const vl_unordered_set* m_setp;  // The containing set

    public:
        // CONSTRUCTORS
        iterator(size_t bucketIdx, typename Bucket::iterator bit,
                 const vl_unordered_set* setp)
            : m_bucketIdx(bucketIdx), m_bit(bit), m_setp(setp) {}

        // METHODS
        const T_Key& operator*() const {
            return *m_bit;
        }
        // This should really be 'const T_Key*' type for unordered_set,
        // however this iterator is shared with unordered_map whose
        // operator-> returns a non-const ValueType*, so keep this
        // non-const to avoid having to define a whole separate iterator
        // for unordered_map.
        T_Key* operator->() const {
            return &(*m_bit);
        }
        bool operator==(const iterator& other) const {
            return ((m_bucketIdx == other.m_bucketIdx)
                    && (m_bit == other.m_bit));
        }
        bool operator!=(const iterator& other) const {
            return (!this->operator==(other));
        }
        void advanceUntilValid() {
            while (1) {
                if (m_bit != m_setp->m_bucketsp[m_bucketIdx].end()) {
                    // Valid iterator in this bucket; we're done.
                    return;
                }

                // Try the next bucket?
                m_bucketIdx++;
                if (m_bucketIdx == m_setp->numBuckets()) {
                    // Ran past the end of buckets, set to end().
                    *this = m_setp->end();
                    return;
                }
                m_bit = m_setp->m_bucketsp[m_bucketIdx].begin();
            }
        }
        void operator++() {
            ++m_bit;
            advanceUntilValid();
        }

        typename Bucket::iterator bit() const { return m_bit; }
    };

    // TODO: there's no real const enforcement on the 'const_iterator'.
    typedef iterator const_iterator;

private:
    // MEMBERS
    size_t m_numElements;       //  Number of entries present.
    size_t m_log2Buckets;       //  Log-base-2 of the number of buckets.
    mutable Bucket* m_bucketsp; //  Hash table buckets. May be NULL;
    //                          //   we'll allocate it on the fly when
    //                          //   the first entries are created.
    Bucket m_emptyBucket;       //  A fake bucket, used to construct end().
    T_Hash m_hash;              //  Hash function provider.
    T_Equal m_equal;            //  Equal-to function provider.

public:
    // CONSTRUCTORS
    vl_unordered_set()
        : m_numElements(0)
        , m_log2Buckets(initLog2Buckets())
        , m_bucketsp(NULL)
        , m_hash()
        , m_equal() {}

    vl_unordered_set(const vl_unordered_set& other)
        : m_numElements(other.m_numElements)
        , m_log2Buckets(other.m_log2Buckets)
        , m_bucketsp(NULL)
        , m_hash()
        , m_equal() {
        if (other.m_bucketsp) {
            m_bucketsp = new Bucket[numBuckets()];
            for (size_t i = 0; i < numBuckets(); i++) {
                m_bucketsp[i] = other.m_bucketsp[i];
            }
        }
    }
    ~vl_unordered_set() {
        VL_DO_DANGLING(delete [] m_bucketsp, m_bucketsp);
    }

    vl_unordered_set& operator=(const vl_unordered_set& other) {
        if (this != &other) {
            clear();
            delete [] m_bucketsp;
            m_numElements = other.m_numElements;
            m_log2Buckets = other.m_log2Buckets;
            if (other.m_bucketsp) {
                m_bucketsp = new Bucket[numBuckets()];
                for (size_t i = 0; i < numBuckets(); i++) {
                    m_bucketsp[i] = other.m_bucketsp[i];
                }
            } else {
                m_bucketsp = NULL;
            }
        }
        return *this;
    }

    // METHODS
    static size_t initLog2Buckets() { return 4; }

    iterator begin() {
        if (m_numElements) {
            initBuckets();
            iterator result = iterator(0, m_bucketsp[0].begin(), this);
            result.advanceUntilValid();
            return result;
        }
        return end();
    }
    const_iterator begin() const {
        if (m_numElements) {
            initBuckets();
            const_iterator result = iterator(0, m_bucketsp[0].begin(), this);
            result.advanceUntilValid();
            return result;
        }
        return end();
    }
    const_iterator end() const {
        return iterator(VL_ULL(0xFFFFFFFFFFFFFFFF),
                        const_cast<Bucket&>(m_emptyBucket).begin(), this);
    }

    bool empty() const { return m_numElements == 0; }

    size_t size() const { return m_numElements; }

    size_t count(const T_Key& key) const {
        return (find(key) == end()) ? 0 : 1;
    }

    size_t hashToBucket(size_t hashVal) const {
        return hashToBucket(hashVal, m_log2Buckets);
    }
    static size_t hashToBucket(size_t hashVal, unsigned log2Buckets) {
        // Fibonacci hashing
        // See https://probablydance.com/2018/06/16/fibonacci-hashing-the-optimization-that-the-world-forgot-or-a-better-alternative-to-integer-modulo/
        //
        // * The magic numbers below are UINT_MAX/phi where phi is the
        //   golden ratio number (1.618...)  for either 64- or 32-bit
        //   values of UINT_MAX.
        //
        // * Fibonacci hashing mixes the result of the client's hash
        //   function further. This permits the use of very fast client
        //   hash funcs (like just returning the int or pointer value as
        //   is!) and tolerates crappy client hash functions pretty well.
        size_t mult = hashVal * ((sizeof(size_t) == 8)
                                 ? VL_ULL(11400714819323198485)
                                 : 2654435769lu);
        size_t result = (mult >> (((sizeof(size_t) == 8)
                                   ? 64 : 32) - log2Buckets));
        return result;
    }

    iterator find_internal(const T_Key& key, size_t& bucketIdxOut) {
        size_t hash = m_hash.operator()(key);
        bucketIdxOut = hashToBucket(hash);
        initBuckets();
        Bucket* bucketp = &m_bucketsp[bucketIdxOut];

        for (typename Bucket::iterator it = bucketp->begin();
             it != bucketp->end(); ++it) {
            if (m_equal.operator()(*it, key)) {
                return iterator(bucketIdxOut, it, this);
            }
        }
        return end();
    }

    const_iterator find(const T_Key& key) const {
        size_t bucketIdx;
        return const_cast<vl_unordered_set*>(this)->find_internal(key,
                                                                  bucketIdx);
    }

    iterator find(const T_Key& key) {
        size_t bucketIdx;
        return find_internal(key, bucketIdx);
    }

    std::pair<iterator, bool> insert(const T_Key& val) {
        size_t bucketIdx;
        iterator existIt = find_internal(val, bucketIdx);
        if (existIt != end()) {
            // Collision with existing element.
            //
            // An element may be inserted only if it is not
            // equal to an existing element. So fail.
            return std::pair<iterator, bool>(end(), false);
        }

        // No collision, so insert it.
        m_numElements++;

        m_bucketsp[bucketIdx].push_front(val);

        // Compute result iterator. This pointer will be valid
        // if we don't rehash:
        iterator result_it(bucketIdx, m_bucketsp[bucketIdx].begin(), this);

        if (needToRehash(GROW)) {
            rehash(GROW);
            // ... since we rehashed, do a lookup to get the result iterator.
            result_it = find(val);
        }

        return std::pair<iterator, bool>(result_it, true);
    }

    iterator erase(iterator it) {
        iterator next_it = it;
        ++next_it;
        erase(*it);
        return next_it;
    }

    size_t erase(const T_Key& key) {
        size_t bucketIdx;
        iterator it = find_internal(key, bucketIdx);
        if (it != end()) {
            m_bucketsp[bucketIdx].erase(it.bit());
            m_numElements--;
            // Rehashing to handle a shrinking data set is important
            // for the Scoreboard in V3Partition, which begins tracking
            // a huge number of vertices and then tracks a successively
            // smaller number over time.
            if (needToRehash(SHRINK)) {
                rehash(SHRINK);
            }
            return 1;
        }
        return 0;
    }

    void clear() {
        if (m_bucketsp) {
            delete[] m_bucketsp;
            m_bucketsp = NULL;
        }
        m_numElements = 0;
        m_log2Buckets = initLog2Buckets();
    }

private:
    size_t numBuckets() const { return (VL_ULL(1) << m_log2Buckets); }

    Bucket* getBucket(size_t idx) {
        initBuckets();
        return &m_bucketsp[idx];
    }

    void initBuckets() const {
        if (!m_bucketsp) m_bucketsp = new Bucket[numBuckets()];
    }

    bool needToRehash(RehashType rt) const {
        if (rt == GROW) {
            return ((4 * numBuckets()) < m_numElements);
        } else {
            return (numBuckets() > (4 * m_numElements));
        }
    }

    void rehash(RehashType rt) {
        size_t new_log2Buckets;
        if (rt == GROW) {
            new_log2Buckets = m_log2Buckets + 2;
        } else {
            if (m_log2Buckets <= 4) {
                // On shrink, saturate m_log2Buckets at its
                // initial size of 2^4 == 16 buckets. Don't risk
                // underflowing!
                return;
            }
            new_log2Buckets = m_log2Buckets - 2;
        }

        size_t new_num_buckets = VL_ULL(1) << new_log2Buckets;
        Bucket* new_bucketsp = new Bucket[new_num_buckets];

        for (size_t i = 0; i < numBuckets(); i++) {
            while (!m_bucketsp[i].empty()) {
                typename Bucket::iterator bit = m_bucketsp[i].begin();
                size_t hash = m_hash.operator()(*bit);
                size_t new_idx = hashToBucket(hash, new_log2Buckets);
                // Avoid mallocing one list elem and freeing another;
                // splice just moves it over.
                new_bucketsp[new_idx].splice(new_bucketsp[new_idx].begin(),
                                             m_bucketsp[i], bit);
            }
        }

        delete[] m_bucketsp;
        m_bucketsp = new_bucketsp;
        m_log2Buckets = new_log2Buckets;
    }
};

//===================================================================
//
/// Functional clone of the std::unordered_map hash table.
template <class T_Key,
          class T_Value,
          class T_Hash = vl_hash<T_Key>,
          class T_Equal = vl_equal_to<T_Key> >
class vl_unordered_map {
private:
    // TYPES
    typedef std::pair<T_Key, T_Value> KeyValPair;

    class KeyHash {
    private:
        T_Hash key_hash;
    public:
        KeyHash() {}
        size_t operator()(const KeyValPair& kv_pair) const {
            return key_hash.operator()(kv_pair.first);
        }
    };

    class KeyEqual {
    private:
        T_Equal key_eq;
    public:
        KeyEqual() {}
        bool operator()(const KeyValPair& kv_a, const KeyValPair& kv_b) const {
            return key_eq.operator()(kv_a.first, kv_b.first);
        }
    };

    // MEMBERS
    typedef vl_unordered_set<KeyValPair, KeyHash, KeyEqual> MapSet;
    MapSet m_set;  // Wrap this vl_unordered_set which holds all state.

public:
    // CONSTRUCTORS
    vl_unordered_map() {}
    ~vl_unordered_map() {}

    typedef typename MapSet::iterator iterator;
    typedef typename MapSet::const_iterator const_iterator;

    // METHODS
    iterator begin() { return m_set.begin(); }
    const_iterator begin() const { return m_set.begin(); }
    const_iterator end() const { return m_set.end(); }
    bool empty() const { return m_set.empty(); }
    iterator find(const T_Key& k) {
        // We can't assume that T_Value() is defined.
        // ie, this does not work:
        //    return m_set.find(std::make_pair(k, T_Value()));

        // So, do this instead:
        T_Hash mapHash;
        T_Equal mapEq;
        size_t hash = mapHash.operator()(k);
        size_t bucketIdxOut = m_set.hashToBucket(hash);
        typename MapSet::Bucket* bucketp = m_set.getBucket(bucketIdxOut);

        for (typename MapSet::Bucket::iterator it = bucketp->begin();
             it != bucketp->end(); ++it) {
            if (mapEq.operator()(it->first, k)) {
                return iterator(bucketIdxOut, it, &m_set);
            }
        }
        return end();
    }
    const_iterator find(const T_Key& k) const {
        return const_cast<vl_unordered_map*>(this)->find(k);
    }
    std::pair<iterator, bool> insert(const KeyValPair& val) {
        return m_set.insert(val);
    }
    iterator erase(iterator it) { return m_set.erase(it); }
    size_t erase(const T_Key& k) {
        iterator it = find(k);
        if (it == end()) { return 0; }
        m_set.erase(it);
        return 1;
    }
    T_Value& operator[](const T_Key& k) {
        // Here we can assume T_Value() is defined, as
        // std::unordered_map::operator[] relies on it too.
        KeyValPair dummy = std::make_pair(k, T_Value());
        iterator it = m_set.find(dummy);
        if (it == m_set.end()) {
            it = m_set.insert(dummy).first;
        }
        // For the 'set', it's generally not safe to modify
        // the value after deref. For the 'map' though, we know
        // it's safe to modify the value field and we can allow it:
        return it->second;
    }
    T_Value& at(const T_Key& k) {
        iterator it = find(k);
        if (it == end()) { throw std::out_of_range("sorry"); }
        return it->second;
    }
    const T_Value& at(const T_Key& k) const {
        iterator it = find(k);
        if (it == end()) { throw std::out_of_range("sorry"); }
        return it->second;
    }
    void clear() { m_set.clear(); }
    size_t size() const { return m_set.size(); }
};

#endif
