// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: pre-C++11 replacements for std::unordered_set
//                         and std::unordered_map.
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2018 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
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

#include "verilated_config.h"
#include "verilatedos.h"

#include <list>
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
    return vl_hash_bytes(&k, sizeof(k));
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
        return vl_hash_bytes(&kp, sizeof(kp));
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
template <class Key,
          class Hash = vl_hash<Key>,
          class Equal = vl_equal_to<Key> > class vl_unordered_set {
public:
    // TYPES
    typedef std::list<Key> Bucket;
    typedef vluint64_t size_type;

    template <class KK, class VV,
              class HH, class EQ> friend class vl_unordered_map;

    class iterator {
    protected:
        // MEMBERS
        size_type m_bucketIdx; //  Bucket this iterator points into.
        typename Bucket::iterator m_bit; //  Bucket-local iterator.
        const vl_unordered_set* m_setp;  //  The containing set.

    public:
        // CONSTRUCTORS
        iterator(size_type bucketIdx, typename Bucket::iterator bit,
                 const vl_unordered_set* setp)
            : m_bucketIdx(bucketIdx), m_bit(bit), m_setp(setp) {}

        // METHODS
        const Key& operator*() const {
            return *m_bit;
        }
        // This should really be 'const Key*' type for unordered_set,
        // however this iterator is shared with unordered_map whose
        // operator-> returns a non-const value_type*, so keep this
        // non-const to avoid having to define a whole separate iterator
        // for unordered_map.
        Key* operator->() const {
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
    size_type m_numElements;    //  Number of entries present.
    size_type m_log2Buckets;    //  Log-base-2 of the number of buckets.
    mutable Bucket* m_bucketsp; //  Hash table buckets. May be NULL;
    //                          //   we'll allocate it on the fly when
    //                          //   the first entries are created.
    Bucket m_emptyBucket;       //  A fake bucket, used to construct end().
    Hash m_hash;                //  Hash function provider.
    Equal m_equal;              //  Equal-to function provider.

public:
    // CONSTRUCTORS
    vl_unordered_set()
        : m_numElements(0)
        , m_log2Buckets(4)
        , m_bucketsp(NULL) { }

    vl_unordered_set(const vl_unordered_set& other)
        : m_numElements(other.m_numElements)
        , m_log2Buckets(other.m_log2Buckets)
        , m_bucketsp(NULL) {
        if (other.m_bucketsp) {
            m_bucketsp = new Bucket[numBuckets()];
            for (size_type i = 0; i < numBuckets(); i++) {
                m_bucketsp[i] = other.m_bucketsp[i];
            }
        }
    }

    vl_unordered_set& operator=(const vl_unordered_set& other) {
        if (this != &other) {
            clear();
            delete [] m_bucketsp;
            m_numElements = other.m_numElements;
            m_log2Buckets = other.m_log2Buckets;
            if (other.m_bucketsp) {
                m_bucketsp = new Bucket[numBuckets()];
                for (size_type i = 0; i < numBuckets(); i++) {
                    m_bucketsp[i] = other.m_bucketsp[i];
                }
            } else {
                m_bucketsp = NULL;
            }
        }
        return *this;
    }

    ~vl_unordered_set() {
        delete [] m_bucketsp;  VL_DANGLING(m_bucketsp);
    }

    // METHODS
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

    size_type size() const { return m_numElements; }

    size_type count(const Key& key) const {
        return (find(key) == end()) ? 0 : 1;
    }

    iterator find_internal(const Key& key, size_type& bucketIdxOut) {
        size_type hash = m_hash.operator()(key);
        bucketIdxOut = hash & ((VL_ULL(1) << m_log2Buckets) - 1);
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

    const_iterator find(const Key& key) const {
        size_type bucketIdx;
        return const_cast<vl_unordered_set*>(this)->find_internal(key,
                                                                  bucketIdx);
    }

    iterator find(const Key& key) {
        size_type bucketIdx;
        return find_internal(key, bucketIdx);
    }

    std::pair<iterator, bool> insert(const Key &val) {
        size_type bucketIdx;
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

        if (needToRehash()) {
            rehash();
            // ... since we rehashed, do a lookup to get the
            // result iterator.
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

    size_type erase(const Key &key) {
        size_type bucketIdx;
        iterator it = find_internal(key, bucketIdx);
        if (it != end()) {
            m_bucketsp[bucketIdx].erase(it.bit());
            m_numElements--;
            return 1;
        }
        return 0;
    }

    void clear() {
        if (m_bucketsp) {
            for (size_type i = 0; i < numBuckets(); i++) {
                m_bucketsp[i].clear();
            }
        }
        m_numElements = 0;
    }

private:
    size_type numBuckets() const { return (VL_ULL(1) << m_log2Buckets); }

    Bucket* getBucket(size_type idx) {
        initBuckets();
        return &m_bucketsp[idx];
    }

    void initBuckets() const {
        if (!m_bucketsp) m_bucketsp = new Bucket[numBuckets()];
    }

    bool needToRehash() const { return ((4 * numBuckets()) < m_numElements); }

    void rehash() {
        size_type new_log2Buckets = m_log2Buckets + 2;
        size_type new_num_buckets = VL_ULL(1) << new_log2Buckets;
        Bucket* new_bucketsp = new Bucket[new_num_buckets];

        for (size_type i=0; i<numBuckets(); i++) {
            while (!m_bucketsp[i].empty()) {
                typename Bucket::iterator bit = m_bucketsp[i].begin();
                size_type hash = m_hash.operator()(*bit);
                size_type new_idx = hash & ((VL_ULL(1) << new_log2Buckets) - 1);
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
template <class Key,
          class Value,
          class Hash = vl_hash<Key>,
          class Equal = vl_equal_to<Key> > class vl_unordered_map {
 private:
    // TYPES
    typedef vluint64_t size_type;
    typedef std::pair<Key, Value> value_type;

    class KeyHash {
    private:
        Hash key_hash;
    public:
        KeyHash() {}
        size_t operator()(const value_type& kv_pair) const {
            return key_hash.operator()(kv_pair.first);
        }
    };

    class KeyEqual {
    private:
        Equal key_eq;
    public:
        KeyEqual() {}
        bool operator()(const value_type& kv_a, const value_type& kv_b) const {
            return key_eq.operator()(kv_a.first, kv_b.first);
        }
    };

    // MEMBERS
    typedef vl_unordered_set<value_type, KeyHash, KeyEqual> MapSet;
    MapSet m_set;   //  Wrap this vl_unordered_set which holds all state.

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
    iterator find(const Key& k) {
        // We can't assume that Value() is defined.
        // ie, this does not work:
        //    return m_set.find(std::make_pair(k, Value()));

        // So, do this instead:
        Hash mapHash;
        Equal mapEq;
        size_type hash = mapHash.operator()(k);
        size_type bucketIdxOut = hash & (m_set.numBuckets() - 1);
        typename MapSet::Bucket* bucketp = m_set.getBucket(bucketIdxOut);

        for (typename MapSet::Bucket::iterator it = bucketp->begin();
            it != bucketp->end(); ++it) {
            if (mapEq.operator()(it->first, k)) {
                return iterator(bucketIdxOut, it, &m_set);
            }
        }
        return end();
    }
    const_iterator find(const Key& k) const {
        return const_cast<vl_unordered_map*>(this)->find(k);
    }
    std::pair<iterator, bool> insert(const value_type& val) {
        return m_set.insert(val);
    }
    iterator erase(iterator it) { return m_set.erase(it); }
    size_type erase(const Key& k) {
        iterator it = find(k);
        if (it == end()) { return 0; }
        m_set.erase(it);
        return 1;
    }
    Value& operator[](const Key& k) {
        // Here we can assume Value() is defined, as
        // std::unordered_map::operator[] relies on it too.
        value_type dummy = std::make_pair(k, Value());
        iterator it = m_set.find(dummy);
        if (it == m_set.end()) {
            it = m_set.insert(dummy).first;
        }
        // For the 'set', it's generally not safe to modify
        // the value after deref. For the 'map' though, we know
        // it's safe to modify the value field and we can allow it:
        return const_cast<Value&>(it->second);
    }
    void clear() { m_set.clear(); }
    size_type size() const { return m_set.size(); }
};

#endif
