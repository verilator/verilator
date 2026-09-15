// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Tests for V3HashTable.h
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

#include "V3HashTable.h"

#include "V3Error.h"

#include <array>
#include <functional>
#include <map>
#include <set>
#include <string>
#include <type_traits>
#include <utility>

namespace V3HashTableInternals {

// Entries that fill a table of the given capacity to its maximum load, so one more grows it
constexpr size_t maxLoad(size_t capacity) { return capacity * LOAD_FACTOR_NUM / LOAD_FACTOR_DEN; }

// Enough entries to grow the smallest table twice, that is, to fill four times the minimum
constexpr size_t GROWS_TWICE = maxLoad(4 * MIN_CAPACITY);
static_assert(GROWS_TWICE > maxLoad(2 * MIN_CAPACITY),
              "SelfTest: 'GROWS_TWICE' must overflow a table twice the minimum");

//######################################################################
// Set key by value

void testValueKeys() {
    struct Value final {
        size_t m_hash = 0;  // Hash of this entry
        size_t m_id = 0;  // Id of this entry
    };

    struct Hash final {
        size_t operator()(const Value& value) const { return operator()(value.m_hash, 0); }
        size_t operator()(size_t hash, size_t) const { return hash; }
    };

    struct Equal final {
        bool operator()(const Value& a, const Value& b) const {
            return operator()(a, b.m_hash, b.m_id);
        }
        bool operator()(const Value& value, size_t hash, size_t id) const {
            return value.m_hash == hash && value.m_id == id;
        }
    };

    using Set = V3HashSet<Value, Hash, Equal>;

    // Entries that are added are found, entries that are not are not
    {
        const Value value{1, 0};
        const Value equal{1, 0};  // Equal to 'value', and hashes the same
        Set set;
        UASSERT_SELFTEST(set.empty(), true);  // Starts empty
        UASSERT_SELFTEST(set.begin() == set.end(), true);  // So iterates nothing
        UASSERT_SELFTEST(set.find(value) == set.end(), true);  // And finds nothing
        const std::pair<Set::iterator, bool> added = set.insert(value);
        UASSERT_SELFTEST(added.second, true);  // Added, as it was absent
        UASSERT_SELFTEST(added.first->m_id, value.m_id);  // The iterator is at the entry
        UASSERT_SELFTEST(&*added.first != &value, true);  // Which is a copy of the argument
        UASSERT_SELFTEST(set.size(), 1);  // And is the only one
        UASSERT_SELFTEST(set.empty(), false);  // So the set is no longer empty
        {
            const Set::iterator it = set.find(value);
            UASSERT_SELFTEST(it != set.end(), true);  // Found by itself
            UASSERT_SELFTEST(&*it, &*added.first);  // At the entry held
        }
        {
            const Set::iterator it = set.find(equal);
            UASSERT_SELFTEST(it != set.end(), true);  // And by an equal entry
            UASSERT_SELFTEST(&*it, &*added.first);  // At that same entry
        }
        {
            const Set::iterator it = set.find(1, size_t{0});
            UASSERT_SELFTEST(it != set.end(), true);  // And by its parts
            UASSERT_SELFTEST(&*it, &*added.first);  // At that same entry again
        }
        UASSERT_SELFTEST(set.find(1, size_t{1}) == set.end(), true);  // Hash same, id not
        UASSERT_SELFTEST(set.find(2, size_t{0}) == set.end(), true);  // Id same, hash not
        // Adding an equal entry returns the one in the set, and does not add
        const std::pair<Set::iterator, bool> again = set.insert(equal);
        UASSERT_SELFTEST(again.second, false);  // Not added, as an equal is present
        UASSERT_SELFTEST(&*again.first, &*added.first);  // At the entry already held
        UASSERT_SELFTEST(set.size(), 1);  // Still just the one entry
        // Erasing through an iterator removes the entry it is at
        {
            const Set::iterator it = set.find(value);
            UASSERT_SELFTEST(it != set.end(), true);  // Present before the erase
            set.erase(it);
        }
        UASSERT_SELFTEST(set.empty(), true);  // Empty again
        UASSERT_SELFTEST(set.find(value) == set.end(), true);  // So the entry is gone
        UASSERT_SELFTEST(set.contains(value), false);  // As 'contains' agrees
        // Erase by key removes whatever that key finds
        UASSERT_SELFTEST(set.erase(value), false);  // Nothing to erase, so says so
        set.insert(value);
        UASSERT_SELFTEST(set.erase(equal), true);  // An equal key erases the entry held
        UASSERT_SELFTEST(set.empty(), true);  // Which leaves the set empty
        // And by a key spelled as the parts of an entry
        set.insert(value);
        UASSERT_SELFTEST(set.erase(1, size_t{0}), true);  // Those parts find and erase it
        UASSERT_SELFTEST(set.empty(), true);  // Empty once more
    }

    // Colliding entries are all kept and stay reachable, including after the table grows
    {
        constexpr size_t N = GROWS_TWICE;
        Set set;
        for (size_t i = 0; i < N; ++i) {
            const std::pair<Set::iterator, bool> added = set.insert(Value{7, i});
            UASSERT_SELFTEST(added.second, true);  // Ids differ, so each is added
        }
        UASSERT_SELFTEST(set.size(), N);  // All of them, in the one probe run
        for (size_t i = 0; i < N; ++i) {
            const Set::iterator it = set.find(size_t{7}, i);
            UASSERT_SELFTEST(it != set.end(), true);  // The growth lost nothing
            UASSERT_SELFTEST(it->m_id, i);  // And is the entry asked for
        }
        // Iterating visits every entry exactly once
        std::array<bool, N> seen{};
        size_t n = 0;
        for (const Value& entry : set) {
            UASSERT_SELFTEST(entry.m_hash, size_t{7});  // Only entries added
            UASSERT_SELFTEST(seen[entry.m_id], false);  // Each of them exactly once
            seen[entry.m_id] = true;
            ++n;
        }
        UASSERT_SELFTEST(n, N);  // And every one of them
    }
}

//######################################################################
// Set key by pointer

void testPointerKeys() {
    struct Value final {
        size_t m_hash = 0;  // Hash of this entry
        size_t m_id = 0;  // Id of this entry
    };

    struct Hash final {
        size_t operator()(const Value* valuep) const { return operator()(valuep->m_hash, 0); }
        size_t operator()(size_t hash, size_t) const { return hash; }
    };

    struct Equal final {
        bool operator()(const Value* ap, const Value* bp) const {
            return operator()(ap, bp->m_hash, bp->m_id);
        }
        bool operator()(const Value* valuep, size_t hash, size_t id) const {
            return valuep->m_hash == hash && valuep->m_id == id;
        }
    };

    using Set = V3HashSet<Value*, Hash, Equal>;

    // Entries that are added are found, entries that are not are not
    {
        Value value{1, 0};
        Value equal{1, 0};  // Equal to 'value', and hashes the same
        Set set;
        UASSERT_SELFTEST(set.empty(), true);  // Starts empty
        UASSERT_SELFTEST(set.begin() == set.end(), true);  // So iterates nothing
        UASSERT_SELFTEST(set.find(&value) == set.end(), true);  // And finds nothing
        const std::pair<Set::iterator, bool> added = set.insert(&value);
        UASSERT_SELFTEST(added.second, true);  // Added, as it was absent
        UASSERT_SELFTEST(*added.first, &value);  // The iterator is at the new entry
        UASSERT_SELFTEST(set.size(), 1);  // Which is the only one
        UASSERT_SELFTEST(set.empty(), false);  // So the set is no longer empty
        {
            const Set::iterator it = set.find(&value);
            UASSERT_SELFTEST(it != set.end(), true);  // Found by itself
            UASSERT_SELFTEST(*it, &value);  // At the entry held
        }
        {
            const Set::iterator it = set.find(&equal);
            UASSERT_SELFTEST(it != set.end(), true);  // And by an equal entry
            UASSERT_SELFTEST(*it, &value);  // At that same entry
        }
        {
            const Set::iterator it = set.find(1, size_t{0});
            UASSERT_SELFTEST(it != set.end(), true);  // And by its parts
            UASSERT_SELFTEST(*it, &value);  // At that same entry again
        }
        UASSERT_SELFTEST(set.find(1, size_t{1}) == set.end(), true);  // Hash same, id not
        UASSERT_SELFTEST(set.find(2, size_t{0}) == set.end(), true);  // Id same, hash not
        // Adding an equal entry returns the one in the set, and does not add
        const std::pair<Set::iterator, bool> again = set.insert(&equal);
        UASSERT_SELFTEST(again.second, false);  // Not added, as an equal is present
        UASSERT_SELFTEST(*again.first, &value);  // The iterator is at the stored one
        UASSERT_SELFTEST(set.size(), 1);  // Still just the one entry
        // Given the distinct but equal '&equal', 'find' still yields the stored '&value'
        {
            const Set::iterator it = set.find(&equal);
            UASSERT_SELFTEST(it != set.end(), true);  // Found, as they compare equal
            UASSERT_SELFTEST(*it, &value);  // But it is the stored one
            UASSERT_SELFTEST(*it == &equal, false);  // Not the one asked for
        }
        {
            const Set::iterator it = set.find(&value);
            UASSERT_SELFTEST(it != set.end(), true);  // The entry is still there
            UASSERT_SELFTEST(*it, &value);  // And is the one stored
        }
        // Erasing the very entry held does remove it
        {
            const Set::iterator it = set.find(&value);
            UASSERT_SELFTEST(it != set.end(), true);  // Present before the erase
            UASSERT_SELFTEST(*it, &value);  // And is the object asked for
            set.erase(it);
        }
        UASSERT_SELFTEST(set.empty(), true);  // Empty again
        UASSERT_SELFTEST(set.find(&value) == set.end(), true);  // So the entry is gone
        UASSERT_SELFTEST(set.contains(&value), false);  // As 'contains' agrees
        UASSERT_SELFTEST(set.empty(), true);  // And no lookup added anything
        // Erase by key makes no such check, so it removes whatever the key finds, here
        // the stored '&value' when given the equal '&equal'
        UASSERT_SELFTEST(set.erase(&value), false);  // Nothing to erase, so says so
        set.insert(&value);
        UASSERT_SELFTEST(set.erase(&equal), true);  // The equal key erases the stored one
        UASSERT_SELFTEST(set.empty(), true);  // Which leaves the set empty
        UASSERT_SELFTEST(set.find(&value) == set.end(), true);  // And unreachable
        // And by a key spelled as the parts of an entry
        set.insert(&value);
        UASSERT_SELFTEST(set.erase(1, size_t{0}), true);  // Those parts find and erase it
        UASSERT_SELFTEST(set.empty(), true);  // Empty once more
    }

    // Erasing leaves the other entries reachable, whichever is erased, including when
    // entries with equal hashes are all in the one probe run
    for (size_t erase = 0; erase < 4; ++erase) {
        for (const size_t hash : {size_t{0}, size_t{7}, ~size_t{0}}) {  // Wraps too
            std::array<Value, 4> values{Value{hash, 0}, Value{hash, 1},  //
                                        Value{hash, 2}, Value{hash, 3}};
            Set set;
            for (Value& value : values) set.insert(&value);
            UASSERT_SELFTEST(set.size(), 4);  // All distinct, so all added
            {
                const Set::iterator it = set.find(&values[erase]);
                UASSERT_SELFTEST(it != set.end(), true);  // The one to erase is present
                UASSERT_SELFTEST(*it, &values[erase]);  // And is the object held
                set.erase(it);
            }
            UASSERT_SELFTEST(set.size(), 3);  // Exactly one was erased
            UASSERT_SELFTEST(set.find(&values[erase]) == set.end(), true);  // That one
            for (size_t i = 0; i < values.size(); ++i) {
                if (i == erase) continue;
                const Set::iterator it = set.find(hash, i);
                UASSERT_SELFTEST(it != set.end(), true);  // The others are all there
                UASSERT_SELFTEST(*it, &values[i]);  // Each at the entry inserted
            }
        }
    }

    // Growing leaves all entries reachable, including when their run wraps around the end
    // of the table. Note this needs enough entries to actually grow, so do not reserve here.
    for (const size_t hash : {size_t{0}, size_t{7}, ~size_t{0}}) {
        std::array<Value, GROWS_TWICE> many{};
        Set set;
        for (size_t i = 0; i < many.size(); ++i) {
            many[i] = Value{hash, i};
            set.insert(&many[i]);
        }
        UASSERT_SELFTEST(set.size(), many.size());  // All of them were added
        for (size_t i = 0; i < many.size(); ++i) {
            const Set::iterator it = set.find(hash, i);
            UASSERT_SELFTEST(it != set.end(), true);  // And all survived the growth
            UASSERT_SELFTEST(*it, &many[i]);  // Each at the entry inserted
        }
    }

    // Entries that collide but are not equal are both kept, and erase removes only the one
    {
        Value value{1, 0};
        Value other{1, 1};  // Not equal to 'value', but lands on the same slot
        Set set;
        set.reserve(2);
        set.insert(&value);
        set.insert(&other);
        UASSERT_SELFTEST(set.size(), 2);  // Both kept, despite the collision
        {
            const Set::iterator it = set.find(&value);
            UASSERT_SELFTEST(it != set.end(), true);  // The first of the run is there
            UASSERT_SELFTEST(*it, &value);  // And is that entry
        }
        {
            const Set::iterator it = set.find(&other);
            UASSERT_SELFTEST(it != set.end(), true);  // As is the one behind it
            UASSERT_SELFTEST(*it, &other);  // Which probing reached past the first
        }
        {
            const Set::iterator it = set.find(&value);
            UASSERT_SELFTEST(it != set.end(), true);  // Present before the erase
            UASSERT_SELFTEST(*it, &value);  // And is the object held
            set.erase(it);
        }
        UASSERT_SELFTEST(set.size(), 1);  // Only one was erased
        UASSERT_SELFTEST(set.find(&value) == set.end(), true);  // Namely that one
        {
            const Set::iterator it = set.find(&other);
            UASSERT_SELFTEST(it != set.end(), true);  // The collider stays
            UASSERT_SELFTEST(*it, &other);  // Shifted back over the hole left
        }
    }

    // Reserving avoids growing, and all entries survive either way
    for (const bool doReserve : {false, true}) {
        std::array<Value, 8> values{};
        Set set;
        if (doReserve) set.reserve(values.size());
        for (size_t i = 0; i < values.size(); ++i) {
            values[i] = Value{static_cast<size_t>(i * 1234567), i};
            set.insert(&values[i]);
        }
        for (Value& value : values) {
            const Set::iterator it = set.find(&value);
            UASSERT_SELFTEST(it != set.end(), true);  // Each entry survives
            UASSERT_SELFTEST(*it, &value);  // And is the one inserted
        }
        UASSERT_SELFTEST(set.size(), values.size());  // And none was added twice
    }

    // 'insertLazy' creates only on a miss, including when that grows the table
    {
        constexpr size_t N = GROWS_TWICE;
        std::array<Value, N> values{};
        Set set;
        for (size_t i = 0; i < N; ++i) {
            values[i] = Value{7, i};  // All of them hash the same
            const std::pair<Set::iterator, bool> pair
                = set.insertLazy(size_t{7}, i, [&]() -> Value* { return &values[i]; });
            UASSERT_SELFTEST(pair.second, true);  // Created, as it was absent
            UASSERT_SELFTEST(*pair.first, &values[i]);  // And is what the factory made
        }
        UASSERT_SELFTEST(set.size(), N);  // All of them were added
        // They are all present now, so nothing is created
        for (size_t i = 0; i < N; ++i) {
            bool created = false;
            const std::pair<Set::iterator, bool> pair
                = set.insertLazy(size_t{7}, i, [&]() -> Value* {
                      created = true;  // LCOV_EXCL_START
                      return &values[i];  // LCOV_EXCL_STOP
                  });
            UASSERT_SELFTEST(created, false);  // The factory was never called
            UASSERT_SELFTEST(pair.second, false);  // As the lookup hit
            UASSERT_SELFTEST(*pair.first, &values[i]);  // On the stored entry
        }
        UASSERT_SELFTEST(set.size(), N);  // And the set is unchanged
    }

    // Iterating visits every entry exactly once
    {
        std::array<Value, 20> values{};
        std::array<bool, 20> seen{};
        Set set;
        for (size_t i = 0; i < values.size(); ++i) {
            values[i] = Value{i / 2, i};  // Pairs of them collide
            set.insert(&values[i]);
        }
        size_t n = 0;
        for (Value* const valuep : set) {
            UASSERT_SELFTEST(valuep->m_id < seen.size(), true);  // Only entries added
            UASSERT_SELFTEST(seen[valuep->m_id], false);  // Each of them exactly once
            seen[valuep->m_id] = true;
            ++n;
        }
        UASSERT_SELFTEST(n, values.size());  // And every one of them
    }
}

//######################################################################
// Entries held by value, which are constructed and destroyed in step with the slots

void testEntryLifetime() {
    size_t alive = 0;  // Number of live entries, which the entries themselves count

    // A test entry that is not default constructible, nor assignable, and that counts how
    // many are alive. A move makes another live entry, so the count tracks the occupied
    // slots however the container shuffles them about.
    class NoDefault final {
        size_t* m_alivep;  // Where the live entries are counted
        size_t m_hash;  // Hash of this entry
        size_t m_id;  // Entries with equal ids are equal

    public:
        NoDefault(size_t* alivep, size_t hash, size_t id)
            : m_alivep{alivep}
            , m_hash{hash}
            , m_id{id} {
            ++*m_alivep;
        }
        NoDefault(const NoDefault& that)
            : m_alivep{that.m_alivep}
            , m_hash{that.m_hash}
            , m_id{that.m_id} {
            ++*m_alivep;
        }
        NoDefault(NoDefault&& that)
            : m_alivep{that.m_alivep}
            , m_hash{that.m_hash}
            , m_id{that.m_id} {
            ++*m_alivep;
        }
        ~NoDefault() { --*m_alivep; }
        NoDefault& operator=(const NoDefault&) = delete;
        NoDefault& operator=(NoDefault&&) = delete;

        size_t hash() const { return m_hash; }
        size_t id() const { return m_id; }
        bool operator==(const NoDefault& that) const { return m_id == that.m_id; }
    };

    static_assert(!std::is_default_constructible<NoDefault>::value,
                  "SelfTest: 'NoDefault' must not be default constructible");
    static_assert(!std::is_copy_assignable<NoDefault>::value,
                  "SelfTest: 'NoDefault' must not be copy assignable");
    static_assert(!std::is_move_assignable<NoDefault>::value,
                  "SelfTest: 'NoDefault' must not be move assignable");
    static_assert(std::is_move_constructible<NoDefault>::value,
                  "SelfTest: 'NoDefault' must be move constructible, to exercise moving");

    struct Hash final {
        size_t operator()(const NoDefault& value) const { return value.hash(); }
        size_t operator()(size_t hash, size_t) const { return hash; }
    };

    struct Equal final {
        bool operator()(const NoDefault& a, const NoDefault& b) const {
            return operator()(a, b.hash(), b.id());
        }
        bool operator()(const NoDefault& a, size_t, size_t id) const { return a.id() == id; }
    };

    using Set = V3HashSet<NoDefault, Hash, Equal>;

    constexpr size_t N = GROWS_TWICE;
    UASSERT_SELFTEST(alive, 0);  // Nothing built yet
    {
        Set set;
        for (size_t i = 0; i < N; ++i) {
            const std::pair<Set::iterator, bool> added = set.insert(NoDefault{&alive, 7, i});
            UASSERT_SELFTEST(added.second, true);  // Ids differ, so each is added
        }
        UASSERT_SELFTEST(set.size(), N);  // All of them are in
        UASSERT_SELFTEST(alive, N);  // Held by exactly that many slots
        // All of them hash the same, so they are all in the one probe run
        for (size_t i = 0; i < N; ++i) {
            const Set::iterator it = set.find(size_t{7}, i);
            UASSERT_SELFTEST(it != set.end(), true);  // Reachable through the run
            UASSERT_SELFTEST(it->id(), i);  // And is the entry asked for
        }
        // A rejected insert constructs no entry: the argument is only copied on a miss
        {
            const std::pair<Set::iterator, bool> dup = set.insert(NoDefault{&alive, 7, 0});
            UASSERT_SELFTEST(dup.second, false);  // Not added, as an equal is present
            UASSERT_SELFTEST(dup.first->id(), 0);  // The iterator is at the stored one
        }
        UASSERT_SELFTEST(set.size(), N);  // Nothing was added
        UASSERT_SELFTEST(alive, N);  // And no copy of the argument was kept
        {
            const Set::iterator it = set.find(size_t{7}, size_t{0});
            UASSERT_SELFTEST(it != set.end(), true);  // Present before the erase
            UASSERT_SELFTEST(it->id(), size_t{0});  // And is the entry asked for
            set.erase(it);
        }
        UASSERT_SELFTEST(set.size(), N - 1);  // One fewer entry
        UASSERT_SELFTEST(alive, N - 1);  // And one fewer live object
        UASSERT_SELFTEST(set.contains(size_t{7}, size_t{0}), false);  // Namely that one
        // Erasing the rest keeps the live entries in step with the slots, all the way down.
        // They all collide, so every erase shifts entries back over the hole.
        for (size_t i = 1; i < N; ++i) {
            {
                const Set::iterator it = set.find(size_t{7}, i);
                UASSERT_SELFTEST(it != set.end(), true);  // Still reachable
                UASSERT_SELFTEST(it->id(), i);  // And is the entry asked for
                set.erase(it);
            }
            UASSERT_SELFTEST(set.size(), N - 1 - i);  // The count follows the erases
            UASSERT_SELFTEST(alive, N - 1 - i);  // As do the live entries
            for (size_t j = i + 1; j < N; ++j) {
                UASSERT_SELFTEST(set.contains(size_t{7}, j), true);  // Shifted, not lost
            }
        }
        UASSERT_SELFTEST(set.begin() == set.end(), true);  // Erased down to empty
        UASSERT_SELFTEST(alive, 0);  // With every entry destroyed
        // Leave entries in the set, so its destructor has some to destroy
        for (size_t i = 0; i < N; ++i) set.insert(NoDefault{&alive, 7, i});
        UASSERT_SELFTEST(alive, N);  // Live as the set goes out of scope
    }
    // The set is gone, so every entry it still held has been destroyed
    UASSERT_SELFTEST(alive, 0);  // Leaking none of them
}

//######################################################################
// A table can be moved, handing over the entries and leaving an empty table behind

void testMove() {
    size_t alive = 0;  // Number of live entries, which the entries themselves count

    // A test entry that counts the live ones, so a move that copied an entry, dropped
    // one, or destroyed one twice, shows up in the count
    struct Counted final {
        size_t* m_alivep;  // Where the live entries are counted
        size_t m_id;  // Entries with equal ids are equal

        Counted(size_t* alivep, size_t id)
            : m_alivep{alivep}
            , m_id{id} {
            ++*m_alivep;
        }
        Counted(const Counted& that)
            : Counted{that.m_alivep, that.m_id} {}
        Counted(Counted&& that)
            : Counted{that.m_alivep, that.m_id} {}
        ~Counted() { --*m_alivep; }
        Counted& operator=(const Counted&) = delete;
        Counted& operator=(Counted&&) = delete;
    };

    struct Hash final {
        size_t operator()(const Counted& entry) const { return operator()(entry.m_id); }
        size_t operator()(size_t id) const { return id; }
    };

    struct Equal final {
        bool operator()(const Counted& a, const Counted& b) const { return operator()(a, b.m_id); }
        bool operator()(const Counted& a, size_t id) const { return a.m_id == id; }
    };

    using Set = V3HashSet<Counted, Hash, Equal>;

    constexpr size_t N = GROWS_TWICE;
    {
        Set set;
        for (size_t i = 0; i < N; ++i) set.insert(Counted{&alive, i});
        UASSERT_SELFTEST(set.size(), N);  // All of them are in
        UASSERT_SELFTEST(alive, N);  // Held by exactly that many slots

        // Move construction takes the entries, making and destroying none
        Set moved{std::move(set)};
        UASSERT_SELFTEST(moved.size(), N);  // Which the target now holds
        UASSERT_SELFTEST(alive, N);  // With no entry made or destroyed
        UASSERT_SELFTEST(set.empty(), true);  // And the source no longer holds them
        UASSERT_SELFTEST(set.begin() == set.end(), true);  // So it iterates nothing
        for (size_t i = 0; i < N; ++i) {
            UASSERT_SELFTEST(moved.contains(i), true);  // Every entry came across
            UASSERT_SELFTEST(set.contains(i), false);  // And none stayed behind
        }

        // The moved from table is empty rather than broken, so it can be filled again
        UASSERT_SELFTEST(set.insert(Counted{&alive, N}).second, true);  // It took an entry
        UASSERT_SELFTEST(set.size(), 1);  // Which is all it holds
        UASSERT_SELFTEST(set.empty(), false);  // So it is no longer empty
        UASSERT_SELFTEST(alive, N + 1);  // And is one more live entry

        // Move assignment destroys what the target held, then takes the source's
        set = std::move(moved);
        UASSERT_SELFTEST(set.size(), N);  // The target holds the moved entries
        UASSERT_SELFTEST(alive, N);  // The entry it held itself was destroyed
        UASSERT_SELFTEST(set.contains(N), false);  // Namely that one
        UASSERT_SELFTEST(moved.empty(), true);  // And the source is empty again
        for (size_t i = 0; i < N; ++i) UASSERT_SELFTEST(set.contains(i), true);  // The rest moved
    }
    // Both tables are gone, so every entry either still held has been destroyed
    UASSERT_SELFTEST(alive, 0);  // Leaking none of them
}

//######################################################################
// Entries that cannot be copied, only moved

void testMoveOnlyEntries() {
    // Only 'insertLazy' can add one of these, as 'insert' would copy it, and any copy the
    // container made of an entry would stop this compiling.
    class MoveOnly final {
        size_t m_id;  // Entries with equal ids are equal

    public:
        explicit MoveOnly(size_t id)
            : m_id{id} {}
        MoveOnly(MoveOnly&&) = default;
        MoveOnly(const MoveOnly&) = delete;
        MoveOnly& operator=(const MoveOnly&) = delete;
        MoveOnly& operator=(MoveOnly&&) = delete;
        ~MoveOnly() = default;

        size_t id() const { return m_id; }
    };

    static_assert(!std::is_copy_constructible<MoveOnly>::value,
                  "SelfTest: 'MoveOnly' must not be copy constructible");
    static_assert(std::is_move_constructible<MoveOnly>::value,
                  "SelfTest: 'MoveOnly' must be move constructible");

    struct Hash final {
        // Every entry hashes the same, so they all end up in the one probe run
        size_t operator()(const MoveOnly& value) const { return operator()(value.id()); }
        size_t operator()(size_t) const { return 7; }
    };

    struct Equal final {
        bool operator()(const MoveOnly& a, const MoveOnly& b) const {
            return operator()(a, b.id());
        }
        bool operator()(const MoveOnly& a, size_t id) const { return a.id() == id; }
    };

    using Set = V3HashSet<MoveOnly, Hash, Equal>;

    constexpr size_t N = GROWS_TWICE;
    Set set;
    for (size_t i = 0; i < N; ++i) {
        const std::pair<Set::iterator, bool> added
            = set.insertLazy(i, [i] { return MoveOnly{i}; });
        UASSERT_SELFTEST(added.second, true);  // Ids differ, so each is added
        UASSERT_SELFTEST(added.first->id(), i);  // Moved into the slot, never copied
    }
    UASSERT_SELFTEST(set.size(), N);  // All of them are in
    // They all collide, so erasing every other one shifts the rest back over the holes
    for (size_t i = 0; i < N; i += 2) {
        const Set::iterator it = set.find(i);
        UASSERT_SELFTEST(it != set.end(), true);  // Present before the erase
        set.erase(it);
    }
    UASSERT_SELFTEST(set.size(), N / 2);  // Half of them are gone
    for (size_t i = 0; i < N; ++i) {
        const bool erased = (i % 2) == 0;
        UASSERT_SELFTEST(set.contains(i), !erased);  // And it is the right half
    }
}

//######################################################################
// Stateful functors, which the two argument constructor moves in

void testStatefulFunctors() {
    // Hashing and comparison that both depend on a mask the functor holds, so the set only
    // works if it keeps the instances it was handed
    class Hash final {
        size_t m_mask;  // Only these bits of an entry matter

    public:
        explicit Hash(size_t mask)
            : m_mask{mask} {}
        size_t operator()(size_t value) const { return value & m_mask; }
    };

    class Equal final {
        size_t m_mask;  // Only these bits of an entry matter

    public:
        explicit Equal(size_t mask)
            : m_mask{mask} {}
        bool operator()(size_t a, size_t b) const { return (a & m_mask) == (b & m_mask); }
    };

    // Neither is default constructible, so the set cannot make its own
    static_assert(!std::is_default_constructible<Hash>::value,
                  "SelfTest: 'Hash' must not be default constructible");
    static_assert(!std::is_default_constructible<Equal>::value,
                  "SelfTest: 'Equal' must not be default constructible");

    // Only the low two bits matter, so the 16 entries fall into 4 classes
    V3HashSet<size_t, Hash, Equal> set{Hash{3}, Equal{3}};
    for (size_t i = 0; i < 16; ++i) set.insert(i);
    UASSERT_SELFTEST(set.size(), 4);  // So the set kept the functors it was given
    // Every entry finds the first one added of its class, which is the class itself
    for (size_t i = 0; i < 16; ++i) {
        const V3HashSet<size_t, Hash, Equal>::iterator it = set.find(i);
        UASSERT_SELFTEST(it != set.end(), true);  // Its class is present
        UASSERT_SELFTEST(*it, (i & 3));  // Represented by the first one added
    }
}

//######################################################################
// Backward shift deletion moves back exactly the entries whose probe run crosses the
// hole: an entry standing at its home position past the hole must stay put

void testBackwardShiftDeletion() {
    // A test entry with an explicit hash, so probe runs can be laid out at will
    struct Value final {
        size_t m_hash = 0;  // Hash of this entry
        size_t m_id = 0;  // Entries with equal ids are equal
    };

    struct Hash final {
        size_t operator()(const Value* valuep) const { return operator()(valuep->m_hash, 0); }
        size_t operator()(size_t hash, size_t) const { return hash; }
    };

    struct Equal final {
        bool operator()(const Value* ap, const Value* bp) const {
            return operator()(ap, bp->m_hash, bp->m_id);
        }
        bool operator()(const Value* valuep, size_t hash, size_t id) const {
            return valuep->m_hash == hash && valuep->m_id == id;
        }
    };

    using Set = V3HashSet<Value*, Hash, Equal>;

    // One probe run of four entries with alternating home positions 'h' and 'h + 1',
    // occupying four adjacent slots. Erasing the first leaves a hole: the second sits
    // at its own home and must not be moved into it, while the third and fourth have
    // their runs broken by the hole and must be moved back.
    for (const size_t h : {size_t{0}, size_t{5}, ~size_t{0}}) {  // Wraps too
        std::array<Value, 4> values{Value{h, 0}, Value{h + 1, 1},  //
                                    Value{h, 2}, Value{h + 1, 3}};
        Set set;
        for (Value& value : values) set.insert(&value);
        UASSERT_SELFTEST(set.size(), 4);  // The run holds all four

        // Erase the entry at the head of the run
        {
            const Set::iterator it = set.find(h, size_t{0});
            UASSERT_SELFTEST(it != set.end(), true);  // Present before the erase
            set.erase(it);
        }
        UASSERT_SELFTEST(set.size(), 3);  // One fewer entry
        UASSERT_SELFTEST(set.contains(h, size_t{0}), false);  // Namely that one
        // Whether moved back or left in place, every entry must remain reachable
        for (size_t i = 1; i < values.size(); ++i) {
            const Set::iterator it = set.find(values[i].m_hash, i);
            UASSERT_SELFTEST(it != set.end(), true);  // The shift lost nothing
            UASSERT_SELFTEST(*it, &values[i]);  // And moved back the right entries
        }

        // Erase the entry that stayed at its home position, shifting the last one again
        {
            const Set::iterator it = set.find(h + 1, size_t{1});
            UASSERT_SELFTEST(it != set.end(), true);  // Left where the first erase found it
            set.erase(it);
        }
        UASSERT_SELFTEST(set.size(), 2);  // Two are left
        for (size_t i = 2; i < values.size(); ++i) {
            const Set::iterator it = set.find(values[i].m_hash, i);
            UASSERT_SELFTEST(it != set.end(), true);  // Both still reachable
            UASSERT_SELFTEST(*it, &values[i]);  // And are the entries they were
        }
        // Iterating visits exactly the remaining entries
        std::array<bool, 4> seen{};
        for (const Value* const valuep : set) {
            UASSERT_SELFTEST(seen[valuep->m_id], false);  // Each entry once
            seen[valuep->m_id] = true;
        }
        UASSERT_SELFTEST(seen[0], false);  // Erased first
        UASSERT_SELFTEST(seen[1], false);  // Erased second
        UASSERT_SELFTEST(seen[2], true);  // Moved back over the first hole
        UASSERT_SELFTEST(seen[3], true);  // And back again over the second
    }
}

//######################################################################
// Entries stay in place unless the table grows or an entry is erased, as only those
// two invalidate iterators

void testReferenceStability() {
    struct Value final {
        size_t m_hash = 0;  // Hash of this entry
        size_t m_id = 0;  // Id of this entry
    };

    struct Hash final {
        size_t operator()(const Value* valuep) const { return operator()(valuep->m_hash, 0); }
        size_t operator()(size_t hash, size_t) const { return hash; }
    };

    struct Equal final {
        bool operator()(const Value* ap, const Value* bp) const {
            return operator()(ap, bp->m_hash, bp->m_id);
        }
        bool operator()(const Value* valuep, size_t hash, size_t id) const {
            return valuep->m_hash == hash && valuep->m_id == id;
        }
    };

    using Set = V3HashSet<Value*, Hash, Equal>;

    // A reserved but still empty set finds nothing and iterates nothing
    {
        Set set;
        set.reserve(8);
        UASSERT_SELFTEST(set.contains(size_t{7}, size_t{0}), false);  // Room, but no entry
        UASSERT_SELFTEST(set.begin() == set.end(), true);  // So iterates nothing
        UASSERT_SELFTEST(set.empty(), true);  // And holds nothing
    }

    // 'N' is exactly what the reservation must hold, so this also checks the boundary
    // arithmetic of 'reserve' against that of the growth check. It is more than an
    // unreserved table holds without growing, so the reservation is doing the work.
    constexpr size_t N = maxLoad(2 * MIN_CAPACITY);
    static_assert(N > maxLoad(MIN_CAPACITY), "SelfTest: 'N' must need more than a new table");
    std::array<Value, N> values{};
    std::array<Value* const*, N> entrypps{};  // Where each entry is stored, as inserted
    Set set;
    set.reserve(N);
    // All entries collide, so every insertion probes through the whole existing run
    for (size_t i = 0; i < N; ++i) {
        values[i] = Value{7, i};
        const std::pair<Set::iterator, bool> pair = set.insert(&values[i]);
        UASSERT_SELFTEST(pair.second, true);  // Ids differ, so each is added
        entrypps[i] = &*pair.first;
    }
    // The set was reserved, so no insertion grew the table, and no entry has moved
    for (size_t i = 0; i < N; ++i) {
        const Set::iterator it = set.find(size_t{7}, i);
        UASSERT_SELFTEST(it != set.end(), true);  // Every entry is still there
        UASSERT_SELFTEST(&*it, entrypps[i]);  // In the slot it was put in
    }
    // Inserting entries that are present adds nothing and moves nothing
    for (size_t i = 0; i < N; ++i) {
        const std::pair<Set::iterator, bool> pair = set.insert(&values[i]);
        UASSERT_SELFTEST(pair.second, false);  // Rejected, as it is present
        UASSERT_SELFTEST(&*pair.first, entrypps[i]);  // And nothing moved
    }
    UASSERT_SELFTEST(set.size(), N);  // No duplicate was added
    // Growing an occupied set through 'reserve' keeps every entry
    set.reserve(8 * N);
    UASSERT_SELFTEST(set.size(), N);  // Rehashing dropped nothing
    std::array<Value* const*, N> grownpps{};  // Where each entry is after the growth
    for (size_t i = 0; i < N; ++i) {
        const Set::iterator it = set.find(size_t{7}, i);
        UASSERT_SELFTEST(it != set.end(), true);  // And left every entry reachable
        grownpps[i] = &*it;
    }
    // Reserving room that is there already leaves the table alone, so nothing moves
    set.reserve(N);
    UASSERT_SELFTEST(set.size(), N);  // The smaller request changed nothing
    for (size_t i = 0; i < N; ++i) {
        const Set::iterator it = set.find(size_t{7}, i);
        UASSERT_SELFTEST(it != set.end(), true);  // Every entry is still there
        UASSERT_SELFTEST(&*it, grownpps[i]);  // In the slot the growth left it in
    }
}

//######################################################################
// A pseudo random workload checked against std::set or std::map as the reference model

// Only a few distinct hashes, so probe runs are long and every erase shifts entries
struct ClusteredHash final {
    size_t operator()(size_t value) const { return value & 0x7; }
};

// Hashes spread by a large odd multiplier, so most probe runs are short
struct SpreadHash final {
    size_t operator()(size_t value) const {
        return static_cast<size_t>(value * 0x9e3779b97f4a7c15ULL);
    }
};

// Drive a set through a deterministic pseudo random workload of insertions, erasures,
// and lookups, checking every step against a std::set holding the same entries
template <typename T_Hash>
void testSetAgainstModel() {
    struct Equal final {
        bool operator()(size_t a, size_t b) const { return a == b; }
    };

    using Set = V3HashSet<size_t, T_Hash, Equal>;

    constexpr size_t UNIVERSE = 64;  // Entries drawn from a small range, so lookups hit
    constexpr size_t STEPS = 10000;  // Number of operations applied

    // A simple linear congruential generator, with a fixed seed so failures reproduce
    uint64_t state = 0x123456789abcdef0ULL;
    const auto nextRand = [&state]() -> size_t {
        state = state * 6364136223846793005ULL + 1442695040888963407ULL;
        return static_cast<size_t>(state >> 32);
    };

    Set set;
    std::set<size_t> model;

    for (size_t step = 0; step < STEPS; ++step) {
        const size_t id = nextRand() % UNIVERSE;
        switch (nextRand() % 4) {
        case 0: {  // Insert a copy
            const std::pair<typename Set::iterator, bool> pair = set.insert(id);
            UASSERT_SELFTEST(pair.second, model.insert(id).second);  // As the model
            UASSERT_SELFTEST(*pair.first, id);  // At the entry asked for
            break;
        }
        case 1: {  // Insert lazily, which must create only on a miss
            bool created = false;
            const std::pair<typename Set::iterator, bool> pair
                = set.insertLazy(id, [&]() -> size_t {
                      created = true;
                      return id;
                  });
            UASSERT_SELFTEST(pair.second, created);  // Created only on a miss
            UASSERT_SELFTEST(pair.second, model.insert(id).second);  // As the model
            UASSERT_SELFTEST(*pair.first, id);  // At the entry asked for
            break;
        }
        case 2: {  // Erase, if present
            const typename Set::iterator it = set.find(id);
            UASSERT_SELFTEST(it != set.end(), model.count(id) != 0);  // As the model
            if (it != set.end()) {
                set.erase(it);
                model.erase(id);
            }
            break;
        }
        default: {  // Look up only
            const typename Set::iterator it = set.find(id);
            UASSERT_SELFTEST(it != set.end(), model.count(id) != 0);  // As the model
            if (it != set.end()) UASSERT_SELFTEST(*it, id);  // And is the entry
            break;
        }
        }
        UASSERT_SELFTEST(set.size(), model.size());  // Every step, not just at the end
    }

    // Check the final content exhaustively
    for (size_t id = 0; id < UNIVERSE; ++id) {
        UASSERT_SELFTEST(set.contains(id), model.count(id) != 0);  // Present iff modelled
    }
    // And that iterating visits exactly the model content, each entry once
    std::array<bool, UNIVERSE> seen{};
    size_t n = 0;
    for (const size_t entry : set) {
        UASSERT_SELFTEST(entry < UNIVERSE, true);  // Nothing out of thin air
        UASSERT_SELFTEST(model.count(entry) != 0, true);  // Only what was inserted
        UASSERT_SELFTEST(seen[entry], false);  // Each entry once
        seen[entry] = true;
        ++n;
    }
    UASSERT_SELFTEST(n, model.size());  // And all of them
}

//######################################################################
// A hash table used as a map, whose entries are plain key and value pairs

void testMap() {
    // The key extractor means the hash and equality see only keys, never entries, so
    // the standard functors do, and they are what V3HashMap defaults to
    using Map = V3HashMap<std::string, int>;
    using Entry = Map::Entry;

    // A map entry is a plain pair, so a caller never meets an internal type
    static_assert(std::is_same<Entry, std::pair<std::string, int>>::value,
                  "SelfTest: a map entry must be a plain pair");

    constexpr size_t N = GROWS_TWICE;
    Map map;
    for (size_t i = 0; i < N; ++i) {
        const std::string key = "key" + std::to_string(i);
        // 'insertLazy' calls the factory only on a miss, so a hit builds no entry
        const std::pair<Map::iterator, bool> pair
            = map.insertLazy(key, [&]() -> Entry { return {key, static_cast<int>(i)}; });
        UASSERT_SELFTEST(pair.second, true);  // Keys differ, so each is added
    }
    UASSERT_SELFTEST(map.size(), N);  // All of them are in

    // A bare key finds the entry, with no Entry built to look it up
    for (size_t i = 0; i < N; ++i) {
        const Map::iterator it = map.find("key" + std::to_string(i));
        UASSERT_SELFTEST(it != map.end(), true);  // The key alone finds it
        UASSERT_SELFTEST(it->second, static_cast<int>(i));  // With the value given
    }

    // A value is changed by erasing the entry and inserting it again, as an iterator
    // yields a const entry
    for (size_t i = 0; i < N; ++i) {
        const std::string key = "key" + std::to_string(i);
        map.erase(map.find(key));
        UASSERT_SELFTEST(map.insert({key, static_cast<int>(i) + 100}).second, true);  // Anew
    }
    UASSERT_SELFTEST(map.size(), N);  // The same keys, so the map has not grown
    for (size_t i = 0; i < N; ++i) {
        const Map::iterator it = map.find("key" + std::to_string(i));
        UASSERT_SELFTEST(it != map.end(), true);  // Each key is still there
        UASSERT_SELFTEST(it->second, static_cast<int>(i) + 100);  // With its new value
    }

    // Adding a key that is present changes nothing
    {
        const std::string key = "key0";
        bool created = false;
        const std::pair<Map::iterator, bool> pair = map.insertLazy(key, [&]() -> Entry {
            created = true;  // LCOV_EXCL_START
            return {key, 0};  // LCOV_EXCL_STOP
        });
        UASSERT_SELFTEST(created, false);  // The factory was never called
        UASSERT_SELFTEST(pair.second, false);  // As the key is present
        UASSERT_SELFTEST(pair.first->second, 100);  // Holding its old value
    }
    UASSERT_SELFTEST(map.size(), N);  // And nothing was added

    // 'insert' adds a key and a value as a plain pair, as std::unordered_map::insert does
    {
        const std::pair<Map::iterator, bool> added = map.insert({std::string{"fresh"}, 5});
        UASSERT_SELFTEST(added.second, true);  // Added, as the key is new
        UASSERT_SELFTEST(added.first->second, 5);  // With the value given
        const std::pair<Map::iterator, bool> again = map.insert({std::string{"fresh"}, 6});
        UASSERT_SELFTEST(again.second, false);  // Rejected, as the key is present
        UASSERT_SELFTEST(again.first->second, 5);  // And the value is untouched
    }
    UASSERT_SELFTEST(map.size(), N + 1);  // Just the one entry was added
    {
        const Map::iterator it = map.find(std::string{"fresh"});
        UASSERT_SELFTEST(it != map.end(), true);  // Present before the erase
        UASSERT_SELFTEST(it->second, 5);  // Still holding the first value
        map.erase(it);
    }
    UASSERT_SELFTEST(map.size(), N);  // Back to the earlier content

    // Erasing by key removes just that entry, and says whether it did
    UASSERT_SELFTEST(map.erase(std::string{"absent"}), false);  // No such key
    UASSERT_SELFTEST(map.size(), N);  // So nothing was erased
    UASSERT_SELFTEST(map.erase(std::string{"key0"}), true);  // That key is present
    UASSERT_SELFTEST(map.size(), N - 1);  // And just the one entry went
    UASSERT_SELFTEST(map.contains(std::string{"key0"}), false);  // Namely that one
    for (size_t i = 1; i < N; ++i) {
        UASSERT_SELFTEST(map.contains("key" + std::to_string(i)), true);  // Others intact
    }
}

//######################################################################
// The pseudo random workload again, run against a map and checked against std::map

// Drive a map through a deterministic pseudo random workload of insertions, erasures,
// value changes and lookups, checking every step against a std::map holding the same
template <typename T_Hash>
void testMapAgainstModel() {
    struct Equal final {
        bool operator()(size_t a, size_t b) const { return a == b; }
    };

    using Map = V3HashMap<size_t, size_t, T_Hash, Equal>;
    using Entry = typename Map::Entry;

    constexpr size_t UNIVERSE = 64;  // Keys drawn from a small range, so lookups hit
    constexpr size_t STEPS = 10000;  // Number of operations applied

    // A simple linear congruential generator, with a fixed seed so failures reproduce
    uint64_t state = 0x0fedcba987654321ULL;
    const auto nextRand = [&state]() -> size_t {
        state = state * 6364136223846793005ULL + 1442695040888963407ULL;
        return static_cast<size_t>(state >> 32);
    };

    Map map;
    std::map<size_t, size_t> model;

    for (size_t step = 0; step < STEPS; ++step) {
        const size_t key = nextRand() % UNIVERSE;
        const size_t val = step;  // Distinct every step, so a stale value is visible
        switch (nextRand() % 5) {
        case 0: {  // Insert a whole entry
            const std::pair<typename Map::iterator, bool> pair = map.insert({key, val});
            UASSERT_SELFTEST(pair.second, model.insert({key, val}).second);  // Ditto
            UASSERT_SELFTEST(pair.first->first, key);  // At the key asked for
            break;
        }
        case 1: {  // Insert lazily, which must create only on a miss
            bool created = false;
            const std::pair<typename Map::iterator, bool> pair
                = map.insertLazy(key, [&]() -> Entry {
                      created = true;
                      return {key, val};
                  });
            UASSERT_SELFTEST(pair.second, created);  // Created only on a miss
            UASSERT_SELFTEST(pair.second, model.insert({key, val}).second);  // Ditto
            UASSERT_SELFTEST(pair.first->first, key);  // At the key asked for
            break;
        }
        case 2: {  // Erase by key, if present
            UASSERT_SELFTEST(map.erase(key), model.erase(key) != 0);  // As model
            break;
        }
        case 3: {  // Change a value, which is erasing the entry and inserting it again
            const typename Map::iterator it = map.find(key);
            if (it != map.end()) {
                map.erase(it);
                UASSERT_SELFTEST(map.insert({key, val}).second, true);  // The key is free
                model[key] = val;
            }
            break;
        }
        default: {  // Look up only
            const typename Map::iterator it = map.find(key);
            UASSERT_SELFTEST(it != map.end(), model.count(key) != 0);  // As the model
            if (it != map.end()) {
                UASSERT_SELFTEST(it->first, key);  // At the key asked for
                UASSERT_SELFTEST(it->second, model.at(key));  // With its value
            }
            break;
        }
        }
        UASSERT_SELFTEST(map.size(), model.size());  // Every step, not just at the end
    }

    // Check the final content exhaustively, values included
    for (size_t key = 0; key < UNIVERSE; ++key) {
        const typename Map::iterator it = map.find(key);
        UASSERT_SELFTEST(it != map.end(), model.count(key) != 0);  // Present iff modelled
        if (it != map.end()) {
            UASSERT_SELFTEST(it->second, model.at(key));  // With the right value
        }
    }
    // And that iterating visits exactly the model content, each entry once
    std::array<bool, UNIVERSE> seen{};
    size_t n = 0;
    for (const Entry& entry : map) {
        UASSERT_SELFTEST(entry.first < UNIVERSE, true);  // Nothing out of thin air
        UASSERT_SELFTEST(model.count(entry.first) != 0, true);  // Only what was inserted
        UASSERT_SELFTEST(entry.second, model.at(entry.first));  // With the right value
        UASSERT_SELFTEST(seen[entry.first], false);  // Each entry once
        seen[entry.first] = true;
        ++n;
    }
    UASSERT_SELFTEST(n, model.size());  // And all of them
}

void selfTest() {
    testValueKeys();
    testPointerKeys();
    testEntryLifetime();
    testMove();
    testMoveOnlyEntries();
    testStatefulFunctors();
    testBackwardShiftDeletion();
    testReferenceStability();
    testSetAgainstModel<ClusteredHash>();
    testSetAgainstModel<SpreadHash>();
    testMap();
    testMapAgainstModel<ClusteredHash>();
    testMapAgainstModel<SpreadHash>();
}

}  // namespace V3HashTableInternals
