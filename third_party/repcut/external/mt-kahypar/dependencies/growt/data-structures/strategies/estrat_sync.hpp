/*******************************************************************************
 * data-structures/strategy/estrat_sync.h
 *
 * see below
 *
 * Part of Project growt - https://github.com/TooBiased/growt.git
 *
 * Copyright (C) 2015-2016 Tobias Maier <t.maier@kit.edu>
 *
 * All rights reserved. Published under the BSD-2 license in the LICENSE file.
 ******************************************************************************/
#pragma once

#include <atomic>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>

#include "../../utils/mark_pointer.hpp"
namespace mark = utils_tm::mark;

#include "../../utils/debug.hpp"
namespace dtm = utils_tm::debug_tm;

/*******************************************************************************
 *
 * This is a exclusion strategy for our growtable.
 *
 * Every exclusion strategy has to implement the following
 *  - subclass: global_data_t      (is stored at the growtable object)
 *     - THIS OBJECT STORES THE ACTUAL HASH TABLE (AT LEAST THE POINTER)
 *           (This is important, because the exclusion strategy dictates,
 *            if reference counting is necessary.)
 *  - subclass: local_data_t       (is stored at each handle)
 *     - init()
 *     - deinit()
 *     - get_table()   (gets current table and protects it from destruction)
 *     - rls_table()   (stops protecting the table)
 *     - grow()       (creates a new table and initiates a growing step)
 *     - help_grow()   (called when an operation is unsuccessful,
 *                     because the table is growing)
 *     - migrate()    (called by the worker strategy to execute the migration.
 *                     Done here to ensure the table is not concurrently freed.)
 *
 * This specific strategy uses a synchronized growing approach, where table
 * updates and growing steps cannot coexist to do this some flags are used
 * (they are stored in the blobal data object). They will be set during each
 * operation on the table. Since the growing is synchronized, storing
 * the table is easy (using some atomic pointers).
 *
 ******************************************************************************/

namespace growt
{

template <class table_type>
size_t blockwise_migrate(table_type source, table_type target);


template <class Parent> class estrat_sync
{
  public:
    static constexpr int max_sim_threads = 256;

    using base_table_type = typename Parent::base_table_type;
    using worker_strat_local_data =
        typename Parent::worker_strat::local_data_type;
    using hash_ptr           = std::atomic<base_table_type*>;
    using hash_ptr_reference = base_table_type*;

    static constexpr size_t migration_block_size = 4096;

  private:
    using mapper_type = typename base_table_type::mapper_type;
    class growable_table_type : public base_table_type
    {
      public:
        growable_table_type(size_t cap)
            : base_table_type(cap), _next_table(nullptr)
        {
        }
        growable_table_type(mapper_type mapper, size_t version)
            : base_table_type(mapper, version), _next_table(nullptr)
        {
        }

        std::atomic<growable_table_type*> _next_table;
    };

    static constexpr size_t   growing_flag = 0;
    static constexpr uint64_t unused_flags = 1;
    using intern_table_type                = growable_table_type;
    using intern_table_ptr                 = growable_table_type*;
    using atomic_table_ptr                 = std::atomic<growable_table_type*>;

    class flags_type
    {
      public:
        std::atomic<bool> used;
        atomic_table_ptr  ops_protect;
        atomic_table_ptr  mig_protect;
        flags_type() : used(false), ops_protect(nullptr), mig_protect(nullptr)
        {
        }
        bool is_unused() { return !used.load(std::memory_order_acquire); }
        bool reserve()
        {
            return !used.exchange(true, std::memory_order_acq_rel);
        }
    };

  public:
    class local_data_type;

    // STORED AT THE GLOBAL OBJECT
    //  - ATOMIC POINTERS TO BOTH CURRENT AND TARGET TABLE
    //  - FLAGS FOR ALL HANDLES (currently in critical section?/growing step?)
    class global_data_type
    {
      public:
        global_data_type(size_t size_);
        global_data_type(const global_data_type& source) = delete;
        global_data_type& operator=(const global_data_type& source) = delete;
        ~global_data_type();

      private:
        friend local_data_type;

        // prevents false sharing between handlespecific flags
        // essential for good performance

        // align to cache line
        std::atomic_int  _last_handle_id;
        std::atomic_int  _epoch;
        atomic_table_ptr _table;
        alignas(128) flags_type _handle_flags[max_sim_threads];

        size_t register_handle();
    };

    // STORED AT EACH HANDLE
    //  - REFERENCE TO THE OWNED FLAGS
    class local_data_type
    {
      public:
        local_data_type(Parent& parent, worker_strat_local_data& wstrat);
        local_data_type(const local_data_type& source) = delete;
        local_data_type& operator=(const local_data_type& source) = delete;

        local_data_type(local_data_type&& source);
        local_data_type& operator=(local_data_type&& source);
        ~local_data_type();

        inline void init() {}
        inline void deinit() {}

      private:
        Parent&                  _parent;
        global_data_type&        _global;
        worker_strat_local_data& _worker_strat;

        size_t      _id;
        flags_type& _own_flags;

      public:
        inline hash_ptr_reference get_table();
        inline void               rls_table();
        void                      grow(int version);
        inline void               help_grow(int version, bool external = true);
        inline size_t             migrate();

      private:
        size_t
        blockwise_migrate(base_table_type& source, base_table_type& target);
        // template<bool ErrorMsg = true>
        // inline bool change_stage(size_t& stage, size_t next);
        inline void wait_for_table_op(growable_table_type* current);
        inline void wait_for_migration();
    };

    static std::string name() { return "e_sync_new"; }
};





template <class P>
estrat_sync<P>::global_data_type::global_data_type(size_t size_)
    : _last_handle_id(0), _epoch(-1)
{
    auto temp = new growable_table_type(size_);
    _table.store(temp, std::memory_order_relaxed);
}

template <class P> estrat_sync<P>::global_data_type::~global_data_type()
{
    delete _table.load(std::memory_order_relaxed);
}

template <class P> size_t estrat_sync<P>::global_data_type::register_handle()
{
    for (int i = 0; i < max_sim_threads; ++i)
    {
        if (_handle_flags[i].is_unused())
        {
            if (_handle_flags[i].reserve())
            {
                int tempi = _last_handle_id.load(std::memory_order_acquire);
                while (tempi <= i)
                {
                    _last_handle_id.compare_exchange_weak(
                        tempi, i + 1, std::memory_order_acq_rel);
                }
                return i;
            }
            else
                --i;
        }
    }
    throw std::length_error("Exceeded predefined maximum of simultaneously "
                            "registered threads (256)!");
    // unreachable
    return -1;
}


template <class P>
estrat_sync<P>::local_data_type::local_data_type(
    P& parent, worker_strat_local_data& wstrat)
    : _parent(parent), _global(parent._global_exclusion), _worker_strat(wstrat),
      _id(_global.register_handle()), _own_flags(_global._handle_flags[_id])
{
}

template <class P>
estrat_sync<P>::local_data_type::local_data_type(local_data_type&& source)
    : _parent(source._parent), _global(source._global),
      _worker_strat(source._worker_strat), _id(source._id),
      _own_flags(source._own_flags)
{
    source._id = std::numeric_limits<size_t>::max();
    dtm::if_debug("handle used during a move",
                  _own_flags.ops_protect.load(std::memory_order_acquire) ||
                      _own_flags.mig_protect.load(std::memory_order_acquire));
}

template <class P>
typename estrat_sync<P>::local_data_type&
estrat_sync<P>::local_data_type::operator=(local_data_type&& source)
{
    if (this == &source) return *this;
    this->~local_data_type();
    new (this) local_data_type(std::move(source));
    return *this;
}

template <class P> estrat_sync<P>::local_data_type::~local_data_type()
{
    if (_id == std::numeric_limits<size_t>::max()) return;
    _own_flags.used.store(false);
}

template <class P>
typename estrat_sync<P>::hash_ptr_reference
estrat_sync<P>::local_data_type::get_table()
{
    auto temp = _global._table.load(std::memory_order_acquire);

    while (!temp) { temp = _global._table.load(std::memory_order_acquire); }
    if (mark::get_mark<growing_flag>(temp))
    {
        help_grow(0, false);
        return get_table();
    }

    // Attention in the pool variant this could overwrite the marked protection
    // from the pool thread !but only if the growing step has been completed in
    // the mean time! growable_table_type* should_be_null = nullptr; if (!
    // _own_flags.compare_exchange_strong(should_be_null, temp,
    //                                        std::memory_order_acq_rel))
    // { help_grow(0, false); return get_table(); }
    _own_flags.ops_protect.store(temp, std::memory_order_release);

    auto temp2 = _global._table.load(std::memory_order_acquire);
    if (temp == temp2) { return temp; }
    else
    {
        // in theory, the pool thread could already use the slot
        _own_flags.ops_protect.store(nullptr, std::memory_order_release);
        return get_table();
    }
}

template <class P> void estrat_sync<P>::local_data_type::rls_table()
{
    _own_flags.ops_protect.store(nullptr, std::memory_order_release);
}

template <class P> void estrat_sync<P>::local_data_type::grow(int version)
{
    // STAGE 1 GENERATE TABLE AND SWAP IT SIZE_TO NEXT
    // we are the only done who is growing the ds
    auto epoch = _global._epoch.load(std::memory_order_acquire);
    dtm::if_debug("strange epoch in grow(int) function", epoch < version - 1);
    if (epoch >= version || !_global._epoch.compare_exchange_strong(
                                epoch, version, std::memory_order_acq_rel))
    {
        // no idea what happened somebody must have triggered growing before us
        // continue operations
        return;
    }

    // this thread exclusively grows the table -> no protection needed
    auto temp = _global._table.load(std::memory_order_acquire);
    dtm::if_debug("current table version does not match grow()'s input",
                  int(temp->_version) != version);

    if (mark::get_mark<growing_flag>(temp))
    {
        dtm::if_debug("strange in grow should be exclusive");
        return;
    }

    if (!mark::atomic_mark<growing_flag>(_global._table, temp))
    {
        // this should not be possible due to the epoch thing above
        // continue operations
        return;
    }

    auto next = new growable_table_type(
        temp->_mapper.resize(_parent._elements.load(std::memory_order_acquire),
                             _parent._dummies.load(std::memory_order_acquire)),
        temp->_version + 1);

    wait_for_table_op(temp);


    // STAGE 2 ALL THREADS CAN ENTER THE MIGRATION
    auto should_be_null = temp->_next_table.exchange(next);
    dtm::if_debug("Error: _next_table pointer != nullptr in grow()",
                  should_be_null);

    // _protect.store(mark::mark<growing_flag>(temp),
    // std::memory_order_release);

    _worker_strat.execute_migration(*this, temp->_version);

    // STAGE 3 WAIT FOR ALL THREADS, THEN CHANGE CURRENT TABLE

    auto rem_dummies = _parent._dummies.load();
    _parent._elements.fetch_sub(rem_dummies);
    _parent._dummies.fetch_sub(rem_dummies);

    // STAGE 4ISH THREADS MAY CONTINUE MASTER WILL DELETE THE OLD TABLE
    auto should_be_marked_temp = _global._table.exchange(nullptr);
    dtm::if_debug("Error: _table has changed since marking it",
                  should_be_marked_temp != mark::mark<growing_flag>(temp));

    wait_for_migration();

    should_be_null = _global._table.exchange(next);
    dtm::if_debug("Error: _table has changed since replacing it with nullptr",
                  should_be_marked_temp != mark::mark<growing_flag>(temp));


    delete temp;
}

template <class P>
void estrat_sync<P>::local_data_type::help_grow([[maybe_unused]] int version,
                                                bool                 external)
{
    dtm::if_debug("in help_grow, got here from external (how?)", external);
    // wait till migration is safe

    _worker_strat.execute_migration(
        *this, _global._epoch.load(std::memory_order_acquire));

    // wait till growmaster replaced the current table
    auto temp = _global._table.load(std::memory_order_acquire);
    while (mark::get_mark<growing_flag>(temp) || !temp)
    {
        temp = _global._table.load(std::memory_order_acquire);
    }
}

template <class P> size_t estrat_sync<P>::local_data_type::migrate()
{
    // enter_migration();
    // while (_protect.load(std::memory_order_acquire) != nullptr)
    // {
    //     // this should basically only happen with pool threads
    //     // a pool thread cannot migrate while its partner still
    //     // operates on the table
    // }

    auto temp = _global._table.load(std::memory_order_acquire);
    if (!temp || !mark::get_mark<growing_flag>(temp))
    {
        return _global._epoch.load(std::memory_order_relaxed) + 1;
    }

    // once _protect was 0 for a short time it should not become non-zero
    _own_flags.mig_protect.store(temp, std::memory_order_release);

    if (!temp || !mark::get_mark<growing_flag>(temp))
    {
        // the migration could have been finished + in the pool variant the main
        // thread of this note could be protecting something already
        _own_flags.mig_protect.store(nullptr, std::memory_order_release);
        return _global._epoch.load(std::memory_order_acquire) + 1;
    }

    auto curr = mark::clear(temp);
    auto next = curr->_next_table.load(std::memory_order_acquire);
    while (!next) { next = curr->_next_table.load(std::memory_order_acquire); }

    blockwise_migrate(*curr, *next);

    auto version = next->_version;
    _own_flags.mig_protect.store(nullptr, std::memory_order_release);

    return version;
}



template <class P>
size_t
estrat_sync<P>::local_data_type::blockwise_migrate(base_table_type& source,
                                                   base_table_type& target)
{
    size_t n = 0;

    // get block + while block legal migrate and get new block
    size_t temp = source._current_copy_block.fetch_add(migration_block_size);
    while (temp < source._mapper.addressable_slots())
    {
        n += source.migrate(target, temp,
                            std::min(static_cast<unsigned int>(temp + migration_block_size),
                                     static_cast<unsigned int>(source._mapper.addressable_slots())));
        temp = source._current_copy_block.fetch_add(migration_block_size);
    }
    return n;
}

// template <class P> template<bool EM>
// bool
// estrat_sync<P>::local_data_type::change_stage(size_t& stage, size_t next)
// {
//     // auto result = _global._currently_growing
//     //     .compare_exchange_strong(stage, next,
//     //                              std::memory_order_acq_rel);
//     // if (result)
//     // {
//     //     stage = next;
//     // }
//     // else if (EM)
//     // {
//     //     std::logic_error("Unexpected result during changeState!");
//     // }
//     // return result;
// }

template <class P>
void estrat_sync<P>::local_data_type::wait_for_table_op(
    growable_table_type* current)
{

    auto end = _global._last_handle_id.load(std::memory_order_acquire);
    for (int i = 0; i < end; ++i)
    {
        auto temp = _global._handle_flags[i].ops_protect.load(
            std::memory_order_acquire);
        while (temp == current)
        {
            temp = _global._handle_flags[i].ops_protect.load(
                std::memory_order_acquire);
            // if (temp == nullptr) break;
            // if (temp == unused_flags) break;
            // if (mark::is_marked<growing_flag>(temp)) break;
        }
    }
}

template <class P> void estrat_sync<P>::local_data_type::wait_for_migration()
{
    auto end = _global._last_handle_id.load(std::memory_order_acquire);
    for (int i = 0; i < end; ++i)
    {
        auto temp = _global._handle_flags[i].mig_protect.load(
            std::memory_order_acquire);
        while (temp != nullptr)
        {
            temp = _global._handle_flags[i].mig_protect.load(
                std::memory_order_acquire);
            // if (temp == nullptr) break;
            // if (temp == unused_flags) break;
            // if (mark::is_marked<growing_flag>(temp)) break;
        }
    }
}


} // namespace growt
