// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Open addressing hash set and hash map
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// An open addressing, linear probing hash table, with backward shift deletion.
// Usable as V3HashSet or V3HashMap. The benefit of these over
// std::unordered_set and std::unordered_map is far better memory locality
// during lookup, and fewer dynamic memory allocations (which also means less
// heap fragmentation). Consider using these if profiling shows that the
// unordered STL collections contribute a significant cost to an algorithm.
//
// Four types tell the table what it holds: the entry, a hash, an equality, and
// a key extractor yielding the lookup key of an entry. The extractor is what
// lets one table serve both roles: a set's entry is its own key, a map's is a
// pair keyed by its first. The hash and equality hence only ever see keys,
// never entries. V3HashSet and V3HashMap at the bottom of this file derive
// from the table, pairing it with the extractor that suits each.
//
// Those two work on keys via Hash and Equal functors as in std::unordered_set
// or std::unordered_map, but lookup is always heterogeneous, with no
// is_transparent to opt in like in the STL, and a lookup key can be spelled as
// several arguments, being the parts a key is made of. An entry can hence be
// looked up without one at hand, as when it is only created on a miss. The
// functors must provide call operators as const members, for the key of an
// entry and for every lookup key spelling used:
//
//   size_t Hash::operator()(const T_Key&) const
//   size_t Hash::operator()(<lookup keys>...) const
//   bool Equal::operator()(const T_Key&, const T_Key&) const
//   bool Equal::operator()(const T_Key&, <lookup keys>...) const
//
// with equal keys hashing equal, as usual, and consistently across the
// spellings.
//
// As only entries are stored, a slot is just a hash and an entry, so probing
// touches few cache lines. The table is doubled when an insertion would take
// it over the maximum load factor, or sized up front with 'reserve', to keep
// the probe runs short.
//
// Entries are referred to by iterators, as in the STL containers, but unlike
// STL containers, the mapped value in a V3HashMap is not mutable through an
// iterator. Iterators and entry addresses stay valid until the table grows or
// an entry is erased; either invalidates all of them.
//
// Erasure uses backward shift deletion: entries following the hole are moved
// back over it where their probe run ran through it (no tombstones).
//
//*************************************************************************

#ifndef VERILATOR_V3HASHTABLE_H_
#define VERILATOR_V3HASHTABLE_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3StdFuture.h"

#include <functional>
#include <memory>
#include <new>
#include <tuple>
#include <type_traits>
#include <utility>

namespace V3HashTableInternals {

constexpr size_t MIN_CAPACITY = 16;  // Smallest table allocated
constexpr size_t LOAD_FACTOR_NUM = 3;  // Numerator of the maximum load factor
constexpr size_t LOAD_FACTOR_DEN = 4;  // Denominator of the maximum load factor

// Key extractor for a table whose entries are their own keys, that is, a set
template <typename T_Key>
struct V3HashTableKeyIsEntry final {
    using Key = T_Key;  // What it yields, so the table need not deduce it
    const T_Key& operator()(const T_Key& entry) const { return entry; }
};

// Key extractor for a table whose entries are pairs keyed by the first, that is, a map
template <typename T_Key, typename T_Val>
struct V3HashTableKeyIsFirst final {
    using Key = T_Key;  // What it yields, so the table need not deduce it
    const T_Key& operator()(const std::pair<T_Key, T_Val>& entry) const { return entry.first; }
};

void selfTest();

}  // namespace V3HashTableInternals

// V3HashTable, see the file header
//  T_Entry  The entries (STL calls this value_type)
//  T_Hash   Hashes a lookup key
//  T_Equal  Compares a key to a lookup key
//  T_KeyOf  Yields the key of an entry
template <typename T_Entry, typename T_Hash, typename T_Equal, typename T_KeyOf>
class V3HashTable VL_NOT_FINAL {
public:
    // TYPES
    using Entry = T_Entry;  // What is stored
    using Key = typename T_KeyOf::Key;  // What entries are looked up by

private:
    // TYPES
    // Holds if the hash accepts a lookup key spelled as the given arguments
    template <typename... T_Args>
    using ValidHash = vlstd::is_invocable_r<size_t, const T_Hash&, const T_Args&...>;

    // Holds if the equality accepts a key and such a lookup key
    template <typename... T_Args>
    using ValidEqual = vlstd::is_invocable_r<bool, const T_Equal&, const Key&, const T_Args&...>;

    // The Key must itself be a valid lookup key, as every lookup ends in comparing one
    // against a stored entry. Asserted separately, so the failure names the functor.
    static_assert(ValidHash<Key>::value, "The 'Hash' functor must accept the 'Key'");
    static_assert(ValidEqual<Key>::value, "The 'Equal' functor must accept two 'Key's");

    // A table slot
    struct Slot final {
        // The entry comes first, so it starts the slot whatever its alignment.
        // It is a union so it is alive only while the slot is occupied.
        union {
            Entry m_entry;
        };
        size_t m_hash = 0;  // Hash of the entry, or zero when the slot is free

        Slot() {}  // Leaves 'm_entry' uninitialized, as the slot is free
        ~Slot() {
            if (!isFree()) destroy();
        }
        Slot(const Slot&) = delete;
        Slot(Slot&&) = delete;
        const Slot& operator=(const Slot&) = delete;
        Slot& operator=(Slot&& that) {
            UDEBUGONLY(UASSERT(this != &that, "Moving a slot onto itself"););
            UDEBUGONLY(UASSERT(!that.isFree(), "Moving from a free slot"););
            UDEBUGONLY(UASSERT(isFree(), "Moving into an occupied slot"););
            new (&m_entry) Entry{std::move(that.m_entry)};
            m_hash = that.m_hash;
            that.destroy();
            return *this;
        }

        bool isFree() const { return !m_hash; }

        // Construct the entry of this free slot from the given entry
        void construct(size_t hash, Entry&& entry) {
            UDEBUGONLY(UASSERT(isFree(), "Constructing the entry of an occupied slot"););
            new (&m_entry) Entry{std::move(entry)};
            m_hash = hash;
        }
        // Destroy the entry of this occupied slot, leaving it free
        void destroy() {
            UDEBUGONLY(UASSERT(!isFree(), "Destroying the entry of a free slot"););
            m_entry.~Entry();
            m_hash = 0;
        }
    };

public:
    // Iterator over the entries, see the file header on invalidation
    class iterator final {
        friend class V3HashTable;

        Slot* m_slotp = nullptr;  // The slot iterated, or the end of the table
        Slot* m_endp = nullptr;  // One past the last slot

        iterator(Slot* slotp, Slot* endp)
            : m_slotp{slotp}
            , m_endp{endp} {}

    public:
        iterator() = default;
        // As opposed to the STL, this always returns a const reference so the
        // collection is not mutable through an iterator alone. This is
        // required because entries must be movable, hence can't be const, but
        // the key of a map must not be modified.
        const Entry& operator*() const { return m_slotp->m_entry; }
        const Entry* operator->() const { return &m_slotp->m_entry; }
        // Pre-increment, skipping the free slots
        iterator& operator++() {
            while (++m_slotp != m_endp && m_slotp->isFree()) {}
            return *this;
        }
        bool operator==(const iterator& that) const { return m_slotp == that.m_slotp; }
        bool operator!=(const iterator& that) const { return m_slotp != that.m_slotp; }
    };

private:
    // STATE
    std::unique_ptr<Slot[]> m_table;  // The table, null when unallocated
    size_t m_capacity = 0;  // Number of slots in the table, a power of two, or zero
    size_t m_size = 0;  // Number of occupied slots
    VL_NO_UNIQUE_ADDRESS_CXX20 T_Hash m_hash;  // Hashes a lookup key
    VL_NO_UNIQUE_ADDRESS_CXX20 T_Equal m_equal;  // Compares a key to a lookup key
    VL_NO_UNIQUE_ADDRESS_CXX20 T_KeyOf m_keyOf;  // Yields the lookup key of an entry

    // METHODS

    // The hash of the given entry or lookup key, as stored in a slot
    template <typename... T_Args>
    size_t hashOf(const T_Args&... args) const {
        // A free slot is one with a zero hash, so force the high bit into every hash.
        constexpr size_t USED_BIT = size_t{1} << (sizeof(size_t) * 8 - 1);
        return static_cast<size_t>(m_hash(args...)) | USED_BIT;
    }

    // Index of the free slot the given hash probes to. There must always be one.
    size_t freeSlot(size_t hash) const {
        const size_t mask = m_capacity - 1;
        size_t i = hash & mask;
        while (!m_table[i].isFree()) i = (i + 1) & mask;
        return i;
    }

    // Resize to the given number of slots, which must fit all entries
    void resize(size_t count) {
        UDEBUGONLY(UASSERT(count && !(count & (count - 1)), "Capacity not a power of 2"););
        const std::unique_ptr<Slot[]> oldTable{std::move(m_table)};
        const size_t oldCapacity = m_capacity;
        m_table = std::make_unique<Slot[]>(count);
        m_capacity = count;
        // Reinsert the entries. 'freeSlot' appends to the probe run of each, so the runs
        // come out contiguous whatever order this visits the old slots in.
        for (size_t i = 0; i < oldCapacity; ++i) {
            Slot& slot = oldTable[i];
            if (!slot.isFree()) m_table[freeSlot(slot.m_hash)] = std::move(slot);
        }
    }

    // Index of the slot holding the entry equal to the given key, or of the free slot its
    // probe sequence ends at. The table must not be empty.
    template <typename... T_Args>
    size_t probe(size_t hash, const T_Args&... args) const {
        UDEBUGONLY(UASSERT(m_table, "Table must be allocated"););
        const size_t mask = m_capacity - 1;
        size_t i = hash & mask;
        while (!m_table[i].isFree()) {
            const Slot& slot = m_table[i];
            if (slot.m_hash == hash && m_equal(m_keyOf(slot.m_entry), args...)) break;
            i = (i + 1) & mask;
        }
        return i;
    }

    // Implementation of 'insertLazy' below. 'all' holds the key arguments, followed by
    // the callable that creates the entry, so 'N_Key' indexes the key.
    template <size_t... N_Key, typename T_All>
    std::pair<iterator, bool> insertLazyImpl(std::index_sequence<N_Key...>, T_All&& all) {
        static_assert(ValidHash<std::tuple_element_t<N_Key, T_All>...>::value,
                      "The 'Hash' functor does not accept a lookup key spelled like this");
        static_assert(ValidEqual<std::tuple_element_t<N_Key, T_All>...>::value,
                      "The 'Equal' functor does not accept a lookup key spelled like this");
        const size_t hash = hashOf(std::get<N_Key>(all)...);
        // Allocate on the first insertion
        if (VL_UNLIKELY(!m_capacity)) resize(V3HashTableInternals::MIN_CAPACITY);
        // Find the slot for the entry
        Slot* slotp = m_table.get() + probe(hash, std::get<N_Key>(all)...);
        // If occupied, it's the equivalent, and we are done
        if (!slotp->isFree()) return {iterator{slotp, m_table.get() + m_capacity}, false};
        // Table is growing
        ++m_size;
        // Increase if necessary by load factor
        if (VL_UNLIKELY(m_size * V3HashTableInternals::LOAD_FACTOR_DEN
                        > m_capacity * V3HashTableInternals::LOAD_FACTOR_NUM)) {
            resize(m_capacity * 2);
            slotp = m_table.get() + freeSlot(hash);
        }
        // Construct the entry via the user provided callable (last item in 'all')
        slotp->construct(hash, std::get<sizeof...(N_Key)>(all)());
        // The key of the created entry must both hash and compare as the key looked up
#ifdef VL_DEBUG
        const Key& key = m_keyOf(slotp->m_entry);
        UASSERT(hashOf(key) == hash,
                "Created entry does not hash as the key it was looked up with");
        UASSERT(m_equal(key, std::get<N_Key>(all)...),
                "Created entry does not match the key it was looked up with");
#endif
        // Return newly create entry
        return {iterator{slotp, m_table.get() + m_capacity}, true};
    }

protected:
    // CONSTRUCTORS
    V3HashTable() = default;
    V3HashTable(T_Hash hash, T_Equal equal)
        : m_hash{std::move(hash)}
        , m_equal{std::move(equal)} {}
    ~V3HashTable() = default;
    VL_UNCOPYABLE(V3HashTable);
    // Movable, as the table is just a pointer. The source is left empty rather than
    // merely unspecified, so it remains a usable, empty table.
    V3HashTable(V3HashTable&& that)
        : m_table{std::move(that.m_table)}
        , m_capacity{that.m_capacity}
        , m_size{that.m_size}
        , m_hash{std::move(that.m_hash)}
        , m_equal{std::move(that.m_equal)}
        , m_keyOf{std::move(that.m_keyOf)} {
        that.m_capacity = 0;
        that.m_size = 0;
    }
    V3HashTable& operator=(V3HashTable&& that) {
        m_table = std::move(that.m_table);  // Frees the table this held, if any
        m_capacity = that.m_capacity;
        m_size = that.m_size;
        m_hash = std::move(that.m_hash);
        m_equal = std::move(that.m_equal);
        m_keyOf = std::move(that.m_keyOf);
        that.m_capacity = 0;
        that.m_size = 0;
        return *this;
    }

public:
    // METHODS
    size_t size() const { return m_size; }
    bool empty() const { return !m_size; }

    iterator begin() const {
        Slot* const endp = m_table.get() + m_capacity;
        Slot* slotp = m_table.get();
        while (slotp != endp && slotp->isFree()) ++slotp;
        return iterator{slotp, endp};
    }
    iterator end() const {
        Slot* const endp = m_table.get() + m_capacity;
        return iterator{endp, endp};
    }

    // Make room for the given number of entries, so inserting that many will not resize
    void reserve(size_t count) {
        size_t capacity = V3HashTableInternals::MIN_CAPACITY;
        while (capacity * V3HashTableInternals::LOAD_FACTOR_NUM
               < count * V3HashTableInternals::LOAD_FACTOR_DEN)
            capacity *= 2;
        if (capacity > m_capacity) resize(capacity);
    }

    // Return iterator to the entry equal to the given key, or 'end()' if there
    // is none. The key is whatever T_Hash and T_Equal accept, spelled as any
    // number of arguments. Same as STL containers.
    template <typename... T_Args>
    iterator find(const T_Args&... args) const {
        static_assert(ValidHash<T_Args...>::value,
                      "The 'Hash' functor does not accept a lookup key spelled like this");
        static_assert(ValidEqual<T_Args...>::value,
                      "The 'Equal' functor does not accept a lookup key spelled like this");
        if (!m_size) return end();  // Nothing to find, and this also covers there being no table
        Slot* const slotp = m_table.get() + probe(hashOf(args...), args...);
        return slotp->isFree() ? end() : iterator{slotp, m_table.get() + m_capacity};
    }

    // Add the given entry, unless an equal one is in the table already. Return
    // iterator to the entry and true if insertion happened. Same as STL containers.
    std::pair<iterator, bool> insert(const Entry& entry) {
        static_assert(std::is_copy_constructible<Entry>::value,
                      "'Entry' must be copy constructible to use 'insert'");
        return insertLazy(m_keyOf(entry), [&entry]() -> Entry { return entry; });
    }

    // As 'insert', but the entry is only made when needed: all but the last argument spell
    // the key, and the last is a callable to create the entry on a miss. Note the created entry
    // must hash and compare equal to the key, and the call must not touch the container, as this
    // holds the slot the entry will go in.
    template <typename... T_Args>
    std::pair<iterator, bool> insertLazy(T_Args&&... args) {
        static_assert(sizeof...(T_Args) >= 2,
                      "'insertLazy' needs a lookup key, then a callable to create the entry");
        using Callable = std::tuple_element_t<sizeof...(T_Args) - 1, std::tuple<T_Args...>>;
        static_assert(vlstd::is_invocable_r<Entry, Callable>::value,
                      "The last argument of 'insertLazy' must be a callable that takes no "
                      "arguments and returns an 'Entry'");
        return insertLazyImpl(std::make_index_sequence<sizeof...(T_Args) - 1>{},
                              std::forward_as_tuple(std::forward<T_Args>(args)...));
    }

    // Whether an entry equal to the given key is in the table. The key is spelled as for 'find'.
    template <typename... T_Args>
    bool contains(const T_Args&... args) const {
        return find(args...) != end();
    }

    // Remove the entry equal to the given key, and return whether there was one.
    template <typename... T_Args>
    bool erase(const T_Args&... args) {
        const iterator it = find(args...);
        if (it == end()) return false;
        erase(it);
        return true;
    }

    // Remove the entry the given iterator refers to, which must not be 'end()'. Note that
    // unlike STL erase this returns nothing, as every iterator is invalidated on deletion.
    void erase(iterator it) {
        UDEBUGONLY(UASSERT(it != end() && !it.m_slotp->isFree(), "Erasing a bad iterator"););
        const size_t mask = m_capacity - 1;
        size_t i = static_cast<size_t>(it.m_slotp - m_table.get());
        // Destroy the entry
        m_table[i].destroy();
        // The entry is gone, so slot 'i' is now a hole
        --m_size;
        // Backward shift deletion: move back the entries whose probing the hole breaks
        size_t j = i;
        while (true) {
            j = (j + 1) & mask;
            Slot& slot = m_table[j];
            if (slot.isFree()) break;
            // Move back if its home position does not lie in the cyclic range (i, j]
            if (((j - (slot.m_hash & mask)) & mask) >= ((j - i) & mask)) {
                m_table[i] = std::move(slot);  // Frees 'slot', which is then the hole
                i = j;
            }
        }
    }
};

template <typename T_Key, typename T_Hash = std::hash<T_Key>,
          typename T_Equal = std::equal_to<T_Key>>
class V3HashSet final : public V3HashTable<T_Key, T_Hash, T_Equal,
                                           V3HashTableInternals::V3HashTableKeyIsEntry<T_Key>> {
    using Super
        = V3HashTable<T_Key, T_Hash, T_Equal, V3HashTableInternals::V3HashTableKeyIsEntry<T_Key>>;

    // Entries are only ever moved. Note 'insert' additionally needs copy construction.
    static_assert(std::is_move_constructible<T_Key>::value, "'T_Key' must be move constructible");
    static_assert(std::is_destructible<T_Key>::value, "'T_Key' must be destructible");

public:
    // CONSTRUCTORS
    V3HashSet() = default;
    V3HashSet(T_Hash hash, T_Equal equal)
        : Super{std::move(hash), std::move(equal)} {}
};

template <typename T_Key, typename T_Val, typename T_Hash = std::hash<T_Key>,
          typename T_Equal = std::equal_to<T_Key>>
class V3HashMap final
    : public V3HashTable<std::pair<T_Key, T_Val>, T_Hash, T_Equal,
                         V3HashTableInternals::V3HashTableKeyIsFirst<T_Key, T_Val>> {
    using Super = V3HashTable<std::pair<T_Key, T_Val>, T_Hash, T_Equal,
                              V3HashTableInternals::V3HashTableKeyIsFirst<T_Key, T_Val>>;

    // Entries are only ever moved. Note 'insert' additionally needs copy construction.
    // Asserted separately, so the failure names the one at fault.
    static_assert(std::is_move_constructible<T_Key>::value, "'T_Key' must be move constructible");
    static_assert(std::is_destructible<T_Key>::value, "'T_Key' must be destructible");
    static_assert(std::is_move_constructible<T_Val>::value, "'T_Val' must be move constructible");
    static_assert(std::is_destructible<T_Val>::value, "'T_Val' must be destructible");

public:
    // TYPES
    using Value = T_Val;  // What a key maps to

    // CONSTRUCTORS
    V3HashMap() = default;
    V3HashMap(T_Hash hash, T_Equal equal)
        : Super{std::move(hash), std::move(equal)} {}
};

#endif  // Guard
