/*******************************************************************************
 * data-structures/strategy/estrat_async.h
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
#include <memory>
#include <mutex>
#include <string>

#include "../../utils/debug.hpp"
namespace dtm = utils_tm::debug_tm;
#include "../../utils/memory_reclamation/counting_reclamation.hpp"
namespace rtm = utils_tm::reclamation_tm;

/*******************************************************************************
 *
 * This is a exclusion strategy for our growtable.
 *
 * Every exclusion strategy has to implement the following
 *  - subclass: global_data_type     (is stored at the growtable object)
 *     - THIS OBJECT STORES THE ACTUAL HASH TABLE (AT LEAST THE POINTER)
 *           (This is important, because the exclusion strategy dictates,
 *            if reference counting is necessary.)
 *  - subclass: local_data_type      (is stored at each handle)
 *     - init()
 *     - deinit()
 *     - getTable()   (gets current table and protects it from destruction)
 *     - rlsTable()   (stops protecting the table)
 *     - grow()       (creates a new table and initiates a growing step)
 *     - helpGrow()   (called when an operation is unsuccessful,
 *                     because the table is growing)
 *     - migrate()    (called by the worker strategy to execute the migration.
 *                     Done here to ensure the table is not concurrently freed.)
 *
 * This specific strategy uses a fully asynchronous growing approach,
 * Any thread might begin a growing step, afterwards threads can join
 * to help with table migration. Meanwhile updates can change the table,
 * but not change elements that have already been copied. This has to be
 * ensured through marking copied elements.
 *
 ******************************************************************************/

namespace growt
{

template <class table_type>
size_t blockwise_migrate(table_type source, table_type target);


template <class Parent>
class estrat_async
{
  private:
    using this_type   = estrat_async<Parent>;
    using parent_type = Parent;

  public:
    using base_table_type    = typename Parent::base_table_type;
    using hash_ptr_reference = base_table_type*;
    using hash_ptr           = base_table_type*;

    static_assert(base_table_type::slot_config::allows_marking,
                  "Asynchroneous migration can only be chosen with a "
                  "markable element!!!");

  private:
    using mapper_type = typename base_table_type::mapper_type;
    class _growable_table_type : public base_table_type
    {
      public:
        _growable_table_type(size_t cap)
            : base_table_type(cap), next_table(nullptr)
        {
        }
        _growable_table_type(mapper_type mapper, size_t version)
            : base_table_type(mapper, version), next_table(nullptr)
        {
        }

        std::atomic<_growable_table_type*> next_table;
    };

    using rec_manager_type    = rtm::counting_manager<_growable_table_type>;
    using rec_handle_type     = typename rec_manager_type::handle_type;
    using atomic_pointer_type = typename rec_manager_type::atomic_pointer_type;
    using pointer_type        = typename rec_manager_type::pointer_type;

  public:
    static constexpr size_t migration_block_size = 4096;

    class local_data_type;

    // STORED AT THE GLOBAL OBJECT
    //  - SHARED POINTERS TO BOTH THE CURRENT AND THE TARGET TABLE
    //  - VERSION COUNTERS
    //  - MUTEX FOR SAVE CHANGING OF SHARED POINTERS
    class global_data_type
    {
      public:
        global_data_type(size_t capacity)
            : _epoch(0), _table(nullptr), _n_helper(0), _rec_manager()
        {
            auto temp_rec_handle = _rec_manager.get_handle();
            auto temp_ptr        = temp_rec_handle.create_pointer(capacity);
            _table.store(temp_ptr, std::memory_order_relaxed);
        }
        global_data_type(const global_data_type& source) = delete;
        global_data_type& operator=(const global_data_type& source) = delete;
        ~global_data_type()
        {
            // base tables have slot cleanup disabled
            // (otherwise slots would be removed during migration)
            // we have to do this here
            if constexpr (base_table_type::slot_config::needs_cleanup)
                _table.load()->slot_cleanup();

            // this is an unsafe deletion of a protected thing it should work
            // fine
            auto temp_rec_handle = _rec_manager.get_handle();
            auto temp_ptr        = _table.exchange(nullptr);
            temp_rec_handle.delete_raw(temp_ptr);
        }

      private:
        friend local_data_type;

        std::atomic_size_t  _epoch;
        atomic_pointer_type _table;
        std::atomic_size_t  _n_helper;
        rec_manager_type    _rec_manager;
    };

    // STORED AT EACH HANDLE
    //  - CACHED TABLE (SHARED PTR) AND VERSION NUMBER
    //  - CONNECTIONS TO THE  WORKER STRATEGY AND THE GLOBAL TABLE
    class local_data_type
    {
      private:
        using worker_strat_local =
            typename Parent::worker_strat::local_data_type;

      public:
        local_data_type(Parent& parent, worker_strat_local& wstrat)
            : _parent(parent), _global(parent._global_exclusion),
              _worker_strat(wstrat), _epoch(0), _table(nullptr),
              _rec_handle(_global._rec_manager.get_handle())
        {
        }

        local_data_type(const local_data_type& source) = delete;
        local_data_type& operator=(const local_data_type& source) = delete;

        local_data_type(local_data_type&& source) = default;
        local_data_type& operator=(local_data_type&& source) = default;
        ~local_data_type()                                   = default;

        inline void init();
        inline void deinit() {}

      private:
        Parent&             _parent;
        global_data_type&   _global;
        worker_strat_local& _worker_strat;
        size_t              _epoch;
        pointer_type        _table;
        rec_handle_type     _rec_handle;


      public:
        inline hash_ptr_reference get_table();
        inline void               rls_table() {}

        void          grow(int version);
        void          help_grow(int version);
        inline size_t migrate();

      private:
        size_t
        blockwise_migrate(base_table_type* source, base_table_type* target);
        inline void load();
        inline void end_grow();
    };

    static std::string name() { return "e_async"; }
};


template <class P>
void estrat_async<P>::local_data_type::init()
{
    _table = _rec_handle.protect(_global._table);
    while (_table->_version != _global._epoch.load(std::memory_order_relaxed))
    { /* wait */
    }
    _epoch = _table->_version;
}

template <class P>
typename estrat_async<P>::hash_ptr_reference
estrat_async<P>::local_data_type::get_table()
{
    size_t t_epoch = _global._epoch.load(std::memory_order_acquire);
    if (t_epoch > _epoch) { load(); }
    return static_cast<hash_ptr_reference>(_table);
}

template <class P>
void estrat_async<P>::local_data_type::grow([[maybe_unused]] int version)
{
    dtm::if_debug("in grow expected version is weird!",
                  int(_table->_version) != version);

    auto new_table = _rec_handle.create_pointer(
        _table->_mapper.resize(
            _parent._elements.load(std::memory_order_acquire),
            _parent._dummies.load(std::memory_order_acquire)),
        _table->_version + 1);

    _growable_table_type* nu_ll = nullptr;
    if (!_table->next_table.compare_exchange_strong(nu_ll, new_table))
    {
        // another thread triggered the growing
        _rec_handle.delete_raw(new_table);
    }

    _worker_strat.execute_migration(*this, _epoch);
    end_grow();
}


template <class P>
void estrat_async<P>::local_data_type::help_grow(int version)
{
    _worker_strat.execute_migration(*this, version); //_epoch);
    end_grow();
}

template <class P>
size_t estrat_async<P>::local_data_type::migrate()
{
    // enter_migration(): nhelper ++
    _global._n_helper.fetch_add(1, std::memory_order_acq_rel);

    // curr is protected (buffered counting pointer) + but we protect it again
    // in case of pool bla
    // auto curr = _table;
    auto curr = _rec_handle.protect(_global._table);

    // *star*
    // next is not actually protected properly (i.e. the next pointer of old
    // tables could already be deleted) but this can only happen if the
    // migration from curr is finished. If this is the case, next will never be
    // accessed.
    if (!curr->next_table.load(std::memory_order_acquire))
    {
        _global._n_helper.fetch_sub(1, std::memory_order_acq_rel);
        auto ver = curr->_version;
        _rec_handle.unprotect(curr);
        return ver;
    }
    auto next = _rec_handle.protect(curr->next_table);

    dtm::if_debug("in migrate, next is not curr+1",
                  next->_version != curr->_version + 1);

    //     //global.g_count.fetch_add(
    blockwise_migrate(curr, next); //,
                                   //     //std::memory_order_acq_rel);

    // leave_migration(): nhelper --
    _global._n_helper.fetch_sub(1, std::memory_order_release);

    auto ver = next->_version;

    _rec_handle.unprotect(curr);
    _rec_handle.unprotect(next);

    return ver;
}

template <class P>
size_t
estrat_async<P>::local_data_type::blockwise_migrate(base_table_type* source,
                                                    base_table_type* target)
{
    size_t n = 0;

    // get block + while block legal migrate and get new block
    size_t temp = source->_current_copy_block.fetch_add(migration_block_size);
    while (temp < source->_mapper.addressable_slots())
    {
        n += source->migrate(
            *target, temp,
            std::min(static_cast<unsigned int>(temp + migration_block_size),
                     static_cast<unsigned int>(source->_mapper.addressable_slots())));
        temp = source->_current_copy_block.fetch_add(migration_block_size);
    }
    return n;
}

template <class P>
void estrat_async<P>::local_data_type::load()
{
    if (_table) _rec_handle.unprotect(_table);
    _table = _rec_handle.protect(_global._table);
    while (_table->_version != _global._epoch.load(std::memory_order_relaxed))
    { /* wait */
    }
    _epoch = _table->_version;
}

template <class P>
void estrat_async<P>::local_data_type::end_grow()
{
    // wait for other helpers
    while (_global._n_helper.load(std::memory_order_acquire)) {}

    // here we don't protect curr because this cannot be a pool thread
    auto curr = _table;
    // next is unprotected here but we do not access it if we
    auto next = curr->next_table.load();

    if (_global._table.compare_exchange_strong(curr, next,
                                               std::memory_order_acq_rel))
    {
        // now we are responsible for some stuff

        // updates to the number of elements can have minor race conditions but
        // the overall number will be right
        auto temp = _parent._dummies.exchange(0, std::memory_order_acq_rel);
        _parent._elements.fetch_sub(temp, std::memory_order_release);

        // before this, no further operations can be done
        // thus next is safe because nothing could be inserted
        _global._epoch.store(next->_version, std::memory_order_release);

        _rec_handle.safe_delete(_table);
    }

    load();
}


} // namespace growt
