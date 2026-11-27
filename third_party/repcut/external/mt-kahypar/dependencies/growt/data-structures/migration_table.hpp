/*******************************************************************************
 * data-structures/grow_table.h
 *
 * Defines the growatble architecture:
 *   grow_table       - the global facade of our table
 *   grow_table_data   - the actual global object (immovable core)
 *   grow_table_handle - local handles on the global object (thread specific)
 * The behavior of grow_table can be specified using the Worker- and Exclusion-
 * strategies. They have significant influence esp. on how the table is grown.
 *
 * Part of Project growt - https://github.com/TooBiased/growt.git
 *
 * Copyright (C) 2015-2016 Tobias Maier <t.maier@kit.edu>
 *
 * All rights reserved. Published under the BSD-2 license in the LICENSE file.
 ******************************************************************************/

#pragma once

#include <algorithm>
#include <atomic>
#include <iostream>
#include <memory>
#include <sstream>
#include <string>


#include "../data-structures/migration_table_iterator.hpp"
#include "../data-structures/returnelement.hpp"
#include "../example/update_fcts.hpp"

namespace growt
{

// FORWARD DECLARATION OF THE HANDLE CLASS
template <class>
class migration_table_handle;
// AND THE STATIONARY DATA OBJECT (GLOBAL OBJECT ON HEAP)
template <class>
class migration_table_data;

template <class HashTable,
          template <class>
          class WorkerStrat,
          template <class>
          class ExclusionStrat>
class migration_table
{
  private:
    using this_type = migration_table<HashTable, WorkerStrat, ExclusionStrat>;

  protected:
    using migration_table_data_type = migration_table_data<this_type>;
    using base_table_type           = HashTable;
    using slot_config               = typename base_table_type::slot_config;
    using worker_strat              = WorkerStrat<migration_table_data_type>;
    using exclusion_strat           = ExclusionStrat<migration_table_data_type>;
    friend migration_table_data_type;

    std::unique_ptr<migration_table_data_type> _mt_data;

  public:
    static constexpr bool allows_deletions = base_table_type::allows_deletions;
    static constexpr bool allows_atomic_updates =
        base_table_type::allows_atomic_updates;
    static constexpr bool allows_updates = base_table_type::allows_updates;
    static constexpr bool allows_referential_integrity =
        base_table_type::allows_referential_integrity;

    using handle_type = migration_table_handle<migration_table_data_type>;
    friend handle_type;

    migration_table(size_t size) : _mt_data(new migration_table_data_type(size))
    {
    }

    migration_table(const migration_table& source) = delete;
    migration_table& operator=(const migration_table& source) = delete;

    migration_table(migration_table&& source) = default;
    migration_table& operator=(migration_table&& source) = default;

    ~migration_table() = default;

    handle_type get_handle() { return handle_type(*_mt_data); }

    static std::string name()
    {
        std::stringstream name;
        name << "migration_table<" << base_table_type::name() << ","
             << worker_strat::name() << "," << exclusion_strat::name() << ">";
        return name.str();
    }
};





// GLOBAL TABLE OBJECT (THIS CANNOT BE USED WITHOUT CREATING A HANDLE)
template <typename Parent>
class migration_table_data
{
  protected:
    // TYPEDEFS
    using parent_type     = Parent;
    using base_table_type = typename Parent::base_table_type;
    using slot_config     = typename base_table_type::slot_config;
    using worker_strat    = typename Parent::worker_strat;
    using exclusion_strat = typename Parent::exclusion_strat;

    friend worker_strat;
    friend exclusion_strat;

  public:
    using size_type   = size_t;
    using handle_type = typename Parent::handle_type;
    friend handle_type;



    migration_table_data(size_type size_)
        : _global_exclusion(std::max(size_, size_type(1) << 15)),
          _global_worker(), // handle_ptr(64),
          _elements(0), _dummies(0), _grow_count(0)
    {
    }

    migration_table_data(const migration_table_data& source) = delete;
    migration_table_data&
    operator=(const migration_table_data& source) = delete;
    migration_table_data(migration_table_data&&)  = delete;
    migration_table_data& operator=(migration_table_data&&) = delete;
    ~migration_table_data()                                 = default;

    size_type element_count_approx()
    {
        return _elements.load() - _dummies.load();
    }

  protected:
    // DATA+FUNCTIONS FOR MIGRATION STRATEGIES
    mutable typename exclusion_strat::global_data_type _global_exclusion;
    mutable typename worker_strat::global_data_type    _global_worker;

    // APPROXIMATE COUNTS
    alignas(64) std::atomic_int _elements;
    alignas(64) std::atomic_int _dummies;
    alignas(64) std::atomic_int _grow_count;
};




// HANDLE OBJECTS EVERY THREAD HAS TO CREATE ONE HANDLE (THEY CANNOT BE SHARED)
template <class migration_table_data>
class migration_table_handle
{
  private:
    using this_type = migration_table_handle<migration_table_data>;

  protected:
    using parent_type = typename migration_table_data::parent_type;

  public:
    using base_table_type = typename migration_table_data::base_table_type;

  protected:
    using worker_strat    = typename migration_table_data::worker_strat;
    using exclusion_strat = typename migration_table_data::exclusion_strat;
    friend migration_table_data;

  public:
    using hash_ptr_reference = typename exclusion_strat::hash_ptr_reference;
    using slot_config        = typename base_table_type::slot_config;
    using slot_type          = typename slot_config::slot_type;

    static constexpr bool allows_deletions = base_table_type::allows_deletions;
    static constexpr bool allows_atomic_updates =
        base_table_type::allows_atomic_updates;
    static constexpr bool allows_updates = base_table_type::allows_updates;
    static constexpr bool allows_referential_integrity =
        base_table_type::allows_referential_integrity;

    using key_type         = typename base_table_type::key_type;
    using mapped_type      = typename base_table_type::mapped_type;
    using value_type       = typename std::pair<const key_type, mapped_type>;
    using iterator         = migration_table_iterator<this_type, false>;
    using const_iterator   = migration_table_iterator<this_type, true>;
    using size_type        = size_t;
    using difference_type  = std::ptrdiff_t;
    using reference        = typename iterator::reference;
    using const_reference  = typename const_iterator::reference;
    using mapped_reference = typename iterator::mapped_reference;
    using const_mapped_reference = typename const_iterator::mapped_reference;
    using insert_return_type     = std::pair<iterator, bool>;

    using local_iterator       = void;
    using const_local_iterator = void;
    using node_type            = void;

  protected:
    using base_table_iterator = typename base_table_type::iterator;
    using base_table_insert_return_type =
        typename base_table_type::insert_return_intern;
    using base_table_citerator = typename base_table_type::const_iterator;

    friend iterator;
    friend reference;
    friend const_iterator;
    friend const_reference;
    friend mapped_reference;
    friend const_mapped_reference;

  public:
    migration_table_handle() = delete;
    migration_table_handle(migration_table_data& data);
    migration_table_handle(parent_type& parent);

    migration_table_handle(const migration_table_handle& source) = delete;
    migration_table_handle&
    operator=(const migration_table_handle& source) = delete;

    migration_table_handle(migration_table_handle&& source) noexcept;
    migration_table_handle& operator=(migration_table_handle&& source) noexcept;

    ~migration_table_handle();

    iterator       begin();
    iterator       end();
    const_iterator cbegin() const;
    const_iterator cend() const;
    const_iterator begin() const { return cbegin(); }
    const_iterator end() const { return cend(); }

    insert_return_type insert(const key_type& k, const mapped_type& d);
    insert_return_type insert(const value_type& e);
    template <class... Args>
    insert_return_type emplace(Args&&... args);
    size_type          erase(const key_type& k);
    iterator           find(const key_type& k);
    const_iterator     find(const key_type& k) const;

    insert_return_type insert_or_assign(const key_type& k, const mapped_type& d)
    {
        return insert_or_update(k, d, example::Overwrite(), d);
    }

    mapped_reference operator[](const key_type& k)
    {
        auto temp = insert(k, mapped_type());
        // if ((*temp.first).first != k)
        //     std::cout << "key is wrong on operator[] access" << std::endl;
        // dtm::if_debug("insert unsuccessful on operator[] access", temp.first
        // == end());
        return (*temp.first).second;
    }

    template <class F, class... Types>
    insert_return_type update(const key_type& k, F f, Types&&... args);

    template <class F, class B, class... Types>
    insert_return_type
    update_with_backoff(const key_type& k, F f, B b, Types&&... args);


    template <class F, class... Types>
    insert_return_type update_unsafe(const key_type& k, F f, Types&&... args);


    template <class F, class... Types>
    insert_return_type insert_or_update(const key_type&    k,
                                        const mapped_type& d,
                                        F                  f,
                                        Types&&... args);

    template <class F, class... Types>
    insert_return_type
    emplace_or_update(key_type&& k, mapped_type&& d, F f, Types&&... args);

    template <class F, class... Types>
    insert_return_type insert_or_update_unsafe(const key_type&    k,
                                               const mapped_type& d,
                                               F                  f,
                                               Types&&... args);

    template <class F, class... Types>
    insert_return_type emplace_or_update_unsafe(key_type&&    k,
                                                mapped_type&& d,
                                                F             f,
                                                Types&&... args);

    size_type erase_if(const key_type& k, const mapped_type& d);

    size_type element_count_approx() { return _mt_data.element_count_approx(); }

  protected:
    // DATA+FUNCTIONS FOR MIGRATION STRATEGIES
    migration_table_data&                             _mt_data;
    size_type                                         _handle_id;
    mutable typename worker_strat::local_data_type    _local_worker;
    mutable typename exclusion_strat::local_data_type _local_exclusion;


    inline insert_return_type insert_intern(slot_type& slot);
    template <class F, class... Types>

    inline insert_return_type
    insert_or_update_intern(slot_type& slot, F f, Types&&... args);
    template <class F, class... Types>

    inline insert_return_type
    insert_or_update_unsafe_intern(slot_type& slot, F f, Types&&... args);

    inline void grow(int version) const { _local_exclusion.grow(version); }

    inline void help_grow(int version) const
    {
        _local_exclusion.help_grow(version);
    }
    inline void rls_table() const { _local_exclusion.rls_table(); }
    inline hash_ptr_reference get_table() const
    {
        return _local_exclusion.get_table();
    }

  protected:
    template <typename Functor, typename... Types>
    inline
        typename std::invoke_result<Functor, hash_ptr_reference, Types&&...>::type
        execute(Functor f, Types&&... param)
    {
        hash_ptr_reference temp = _local_exclusion.get_table();
        auto               result =
            std::forward<Functor>(f)(temp, std::forward<Types>(param)...);
        rls_table();
        return result;
    }

    template <typename Functor, typename... Types>
    inline
        typename std::invoke_result<Functor, hash_ptr_reference, Types&&...>::type
        cexecute(Functor f, Types&&... param) const
    {
        hash_ptr_reference temp = _local_exclusion.get_table();
        auto               result =
            std::forward<Functor>(f)(temp, std::forward<Types>(param)...);
        rls_table();
        return result;
    }

    inline iterator
    make_iterator(const base_table_iterator& bit, size_t version)
    {
        return iterator(bit, version, *this);
    }
    inline iterator
    make_citerator(const base_table_citerator& bcit, size_t version)
    {
        return const_iterator(bcit, version, *this);
    }

    inline insert_return_type make_insert_ret(const base_table_iterator& bit,
                                              size_t version,
                                              bool   inserted)
    {
        return std::make_pair(iterator(bit, version, *this), inserted);
    }
    inline base_table_iterator bend()
    {
        return base_table_iterator(slot_config::get_empty(), nullptr, nullptr);
    }
    inline base_table_iterator bcend()
    {
        return base_table_citerator(slot_config::get_empty(), nullptr, nullptr);
    }

    static constexpr double _max_fill_factor = 0.666;

    // LOCAL COUNTERS FOR SIZE ESTIMATION WITH SOME PADDING FOR
    // REDUCING CACHE EFFECTS
  public:
    void update_numbers();

  protected:
    void inc_inserted();
    void inc_deleted();

    class alignas(64) local_count
    {
      public:
        int _updates;
        int _inserted;
        int _deleted;
        local_count() : _updates(0), _inserted(0), _deleted(0) {}

        local_count(local_count&& rhs)
            : _updates(rhs._updates), _inserted(rhs._inserted),
              _deleted(rhs._deleted)
        {
            rhs._updates  = 0;
            rhs._inserted = 0;
            rhs._deleted  = 0;
        }

        local_count& operator=(local_count&& rhs)
        {
            _updates      = rhs._updates;
            _inserted     = rhs._inserted;
            _deleted      = rhs._deleted;
            rhs._updates  = 0;
            rhs._inserted = 0;
            rhs._deleted  = 0;
            return *this;
        }

        void set(int upd, int in, int del)
        {
            _updates  = upd;
            _inserted = in;
            _deleted  = del;
        }

        local_count(const local_count&) = delete;
        local_count& operator=(const local_count&) = delete;
    };
    local_count _counts;

  public:
    using range_iterator       = typename base_table_type::range_iterator;
    using const_range_iterator = typename base_table_type::const_range_iterator;

    /* size has to divide capacity */
    range_iterator range(size_t rstart, size_t rend)
    {
        range_iterator result = execute([rstart, rend](hash_ptr_reference tab) {
            return tab->range(rstart, rend);
        });
        return result;
    }
    const_range_iterator crange(size_t rstart, size_t rend)
    {
        const_range_iterator result =
            cexecute([rstart, rend](hash_ptr_reference tab) {
                return tab->crange(rstart, rend);
            });
        return result;
    }
    range_iterator       range_end() { return bend(); }
    const_range_iterator range_cend() const { return bcend(); }
    size_t               capacity() const
    {
        size_t cap =
            cexecute([](hash_ptr_reference tab) { return tab->capacity(); });
        return cap;
    }
};







// CONSTRUCTORS AND ASSIGNMENTS ************************************************

template <class migration_table_data>
migration_table_handle<migration_table_data>::migration_table_handle(
    migration_table_data& data)
    : _mt_data(data), _local_worker(data),
      _local_exclusion(data, _local_worker), _counts()
{
    // handle_id = _mt_data.handle_ptr.push_back(this);

    // INITIALIZE STRATEGY DEPENDENT DATA MEMBERS
    _local_exclusion.init();
    _local_worker.init(_local_exclusion);
}

template <class migration_table_data>
migration_table_handle<migration_table_data>::migration_table_handle(
    parent_type& parent)
    : _mt_data(*(parent._mt_data)), _local_worker(*(parent._mt_data)),
      _local_exclusion(*(parent._mt_data), _local_worker), _counts()
{
    // handle_id = _mt_data.handle_ptr.push_back(this);

    // INITIALIZE STRATEGY DEPENDENT DATA MEMBERS
    _local_exclusion.init();
    _local_worker.init(_local_exclusion);
}



template <class migration_table_data>
migration_table_handle<migration_table_data>::migration_table_handle(
    migration_table_handle&& source) noexcept
    : _mt_data(source._mt_data), _handle_id(source._handle_id),
      _local_worker(std::move(source._local_worker)),
      _local_exclusion(std::move(source._local_exclusion)),
      _counts(std::move(source._counts))
{
    source._counts = local_count();
    //_mt_data.handle_ptr.update(_handle_id, this);
    // source._handle_id = std::numeric_limits<size_t>::max();
}

template <class migration_table_data>
migration_table_handle<migration_table_data>&
migration_table_handle<migration_table_data>::operator=(
    migration_table_handle&& source) noexcept
{
    if (this == &source) return *this;

    this->~migration_table_handle();
    new (this) migration_table_handle(std::move(source));
    return *this;
}



template <class migration_table_data>
migration_table_handle<migration_table_data>::~migration_table_handle()
{

    // if (_handle_id < std::numeric_limits<size_t>::max())
    // {
    //     _mt_data.handle_ptr.remove(_handle_id);
    // }

    // if (_counts._version >= 0)
    {
        update_numbers();
    }

    _local_worker.deinit();
    _local_exclusion.deinit();
}








// MAIN HASH TABLE FUNCTIONALITY ***********************************************

template <class migration_table_data>
inline typename migration_table_handle<migration_table_data>::insert_return_type
migration_table_handle<migration_table_data>::insert(const key_type&    k,
                                                     const mapped_type& d)
{
    auto slot   = slot_type(k, d);
    auto result = insert_intern(slot);
    if constexpr (slot_config::needs_cleanup)
    {
        if (!result.second) slot.cleanup();
    }
    return result;
}

template <class migration_table_data>
inline typename migration_table_handle<migration_table_data>::insert_return_type
migration_table_handle<migration_table_data>::insert(const value_type& e)
{
    auto slot   = slot_type(e);
    auto result = insert_intern(slot);
    if constexpr (slot_config::needs_cleanup)
    {
        if (!result.second) slot.cleanup();
    }
    return result;
}

template <class migration_table_data>
template <class... Args>
inline typename migration_table_handle<migration_table_data>::insert_return_type
migration_table_handle<migration_table_data>::emplace(Args&&... args)
{
    auto slot   = slot_type(std::forward<Args>(args)...);
    auto result = insert_intern(slot);
    if constexpr (slot_config::needs_cleanup)
    {
        if (!result.second) slot.cleanup();
    }
    return result;
}

template <class migration_table_data>
inline typename migration_table_handle<migration_table_data>::insert_return_type
migration_table_handle<migration_table_data>::insert_intern(slot_type& slot)
{
    int                           v = -1;
    base_table_insert_return_type result =
        std::make_pair(bend(), ReturnCode::ERROR);
    std::tie(v, result) = execute(
        [](hash_ptr_reference t,
           slot_type&         slot)                              //
        -> std::pair<int, base_table_insert_return_type> //
        {
            auto hash = t->h(slot.get_key_ref());
            slot.set_fingerprint(hash);
            std::pair<int, base_table_insert_return_type> result =
                std::make_pair(t->_version, t->insert_intern(slot, hash));
            return result;
        },
        slot);

    switch (result.second)
    {
    case ReturnCode::SUCCESS_IN:
    case ReturnCode::TSX_SUCCESS_IN:
        inc_inserted();
        return make_insert_ret(result.first, v, true);
    case ReturnCode::UNSUCCESS_ALREADY_USED:
    case ReturnCode::TSX_UNSUCCESS_ALREADY_USED:
        return make_insert_ret(result.first, v, false);
    case ReturnCode::UNSUCCESS_FULL:
    case ReturnCode::TSX_UNSUCCESS_FULL:
        grow(v);
        return insert_intern(slot);
    case ReturnCode::UNSUCCESS_INVALID:
    case ReturnCode::TSX_UNSUCCESS_INVALID:
        help_grow(v);
        return insert_intern(slot);
    default:
        return make_insert_ret(bend(), v, false);
    }
}

template <class migration_table_data>
template <class F, class... Types>
inline typename migration_table_handle<migration_table_data>::insert_return_type
migration_table_handle<migration_table_data>::update(const key_type& k,
                                                     F               f,
                                                     Types&&... args)
{
    int                           v = -1;
    base_table_insert_return_type result =
        std::make_pair(bend(), ReturnCode::ERROR);

    std::tie(v, result) = execute(
        [](hash_ptr_reference t, const key_type& k, F f,
           Types&&... args) -> std::pair<int, base_table_insert_return_type> {
            std::pair<int, base_table_insert_return_type> result =
                std::make_pair(
                    t->_version,
                    t->update_intern(k, f, std::forward<Types>(args)...));
            return result;
        },
        k, f, std::forward<Types>(args)...);

    switch (result.second)
    {
    case ReturnCode::SUCCESS_UP:
    case ReturnCode::TSX_SUCCESS_UP:
        return make_insert_ret(result.first, v, true);
    case ReturnCode::UNSUCCESS_NOT_FOUND:
    case ReturnCode::TSX_UNSUCCESS_NOT_FOUND:
        // std::cout << "!" << std::flush;
        return make_insert_ret(result.first, v, false);
    case ReturnCode::UNSUCCESS_FULL:
    case ReturnCode::TSX_UNSUCCESS_FULL:
        grow(v); // usually impossible as this collides with NOT_FOUND
        return update(k, f, std::forward<Types>(args)...);
    case ReturnCode::UNSUCCESS_INVALID:
    case ReturnCode::TSX_UNSUCCESS_INVALID:
        help_grow(v);
        return update(k, f, std::forward<Types>(args)...);
    default:
        return make_insert_ret(bend(), v, false);
    }
}

template <class migration_table_data>
template <class F, class B, class... Types>
inline typename migration_table_handle<migration_table_data>::insert_return_type
migration_table_handle<migration_table_data>::update_with_backoff(
    const key_type& k, F f, B b, Types&&... args)
{
    int                           v = -1;
    base_table_insert_return_type result =
        std::make_pair(bend(), ReturnCode::ERROR);

    std::tie(v, result) = execute(
        [](hash_ptr_reference t, const key_type& k, F f, B b,
           Types&&... args)                              //
        -> std::pair<int, base_table_insert_return_type> //
        {
            std::pair<int, base_table_insert_return_type> result =
                std::make_pair(t->_version,
                               t->update_with_backoff_intern(
                                   k, f, b, std::forward<Types>(args)...));
            return result;
        },
        k, f, b, std::forward<Types>(args)...);

    switch (result.second)
    {
    case ReturnCode::SUCCESS_UP:
    case ReturnCode::TSX_SUCCESS_UP:
        return make_insert_ret(result.first, v, true);
    case ReturnCode::UNSUCCESS_NOT_FOUND:
    case ReturnCode::TSX_UNSUCCESS_NOT_FOUND:
        // std::cout << "!" << std::flush;
        return make_insert_ret(result.first, v, false);
    case ReturnCode::UNSUCCESS_BACKOFF:
        return make_insert_ret(result.first, v, successful(result.second));
    case ReturnCode::UNSUCCESS_FULL:
    case ReturnCode::TSX_UNSUCCESS_FULL:
        grow(v); // usually impossible as this collides with NOT_FOUND
        return update_with_backoff(k, f, b, std::forward<Types>(args)...);
    case ReturnCode::UNSUCCESS_INVALID:
    case ReturnCode::TSX_UNSUCCESS_INVALID:
        help_grow(v);
        return update_with_backoff(k, f, b, std::forward<Types>(args)...);
    default:
        return make_insert_ret(bend(), v, false);
    }
}

template <class migration_table_data>
template <class F, class... Types>
inline typename migration_table_handle<migration_table_data>::insert_return_type
migration_table_handle<migration_table_data>::update_unsafe(const key_type& k,
                                                            F               f,
                                                            Types&&... args)
{
    int                           v = -1;
    base_table_insert_return_type result =
        std::make_pair(bend(), ReturnCode::ERROR);

    std::tie(v, result) = execute(
        [](hash_ptr_reference t, const key_type& k, F f,
           Types&&... args) -> std::pair<int, base_table_insert_return_type> {
            std::pair<int, base_table_insert_return_type> result =
                std::make_pair(t->_version,
                               t->update_unsafe_intern(
                                   k, f, std::forward<Types>(args)...));
            return result;
        },
        k, f, std::forward<Types>(args)...);

    switch (result.second)
    {
    case ReturnCode::SUCCESS_UP:
    case ReturnCode::TSX_SUCCESS_UP:
        return make_insert_ret(result.first, v, true);
    case ReturnCode::UNSUCCESS_NOT_FOUND:
    case ReturnCode::TSX_UNSUCCESS_NOT_FOUND:
        return make_insert_ret(result.first, v, false);
    case ReturnCode::UNSUCCESS_FULL:
    case ReturnCode::TSX_UNSUCCESS_FULL:
        grow(v);
        return update_unsafe(k, f, std::forward<Types>(args)...);
    case ReturnCode::UNSUCCESS_INVALID:
    case ReturnCode::TSX_UNSUCCESS_INVALID:
        help_grow(v);
        return update_unsafe(k, f, std::forward<Types>(args)...);
    default:
        return make_insert_ret(bend(), v, false);
    }
}

template <class migration_table_data>
template <class F, class... Types>
inline typename migration_table_handle<migration_table_data>::insert_return_type
migration_table_handle<migration_table_data>::insert_or_update(
    const key_type& k, const mapped_type& d, F f, Types&&... args)
{
    auto slot = slot_type(k, d);
    auto result =
        insert_or_update_intern(slot, f, std::forward<Types>(args)...);
    if constexpr (slot_config::needs_cleanup)
    {
        if (!result.second) slot.cleanup();
    }
    return result;
}

template <class migration_table_data>
template <class F, class... Types>
inline typename migration_table_handle<migration_table_data>::insert_return_type
migration_table_handle<migration_table_data>::emplace_or_update(key_type&&    k,
                                                                mapped_type&& d,
                                                                F             f,
                                                                Types&&... args)
{
    auto slot = slot_type(std::move(k), std::move(d));
    auto result =
        insert_or_update_intern(slot, f, std::forward<Types>(args)...);
    if constexpr (slot_config::needs_cleanup)
    {
        if (!result.second) slot.cleanup();
    }
    return result;
}

template <class migration_table_data>
template <class F, class... Types>
inline typename migration_table_handle<migration_table_data>::insert_return_type
migration_table_handle<migration_table_data>::insert_or_update_intern(
    slot_type& slot, F f, Types&&... args)
{
    int                           v = -1;
    base_table_insert_return_type result =
        std::make_pair(bend(), ReturnCode::ERROR);

    std::tie(v, result) = execute(
        [](hash_ptr_reference t, slot_type& slot, F f,
           Types&&... args) -> std::pair<int, base_table_insert_return_type> {
            auto hash = t->h(slot.get_key_ref());
            slot.set_fingerprint(hash);
            std::pair<int, base_table_insert_return_type> result =
                std::make_pair(t->_version, t->insert_or_update_intern(
                                                slot, hash, f,
                                                std::forward<Types>(args)...));
            return result;
        },
        slot, f, std::forward<Types>(args)...);

    switch (result.second)
    {
    case ReturnCode::SUCCESS_IN:
    case ReturnCode::TSX_SUCCESS_IN:
        inc_inserted();
        return make_insert_ret(result.first, v, true);
    case ReturnCode::SUCCESS_UP:
    case ReturnCode::TSX_SUCCESS_UP:
        return make_insert_ret(result.first, v, false);
    case ReturnCode::UNSUCCESS_FULL:
    case ReturnCode::TSX_UNSUCCESS_FULL:
        grow(v);
        return insert_or_update_intern(slot, f, std::forward<Types>(args)...);
    case ReturnCode::UNSUCCESS_INVALID:
    case ReturnCode::TSX_UNSUCCESS_INVALID:
        help_grow(v);
        return insert_or_update_intern(slot, f, std::forward<Types>(args)...);
    default:
        return make_insert_ret(bend(), v, false);
    }
}

template <class migration_table_data>
template <class F, class... Types>
inline typename migration_table_handle<migration_table_data>::insert_return_type
migration_table_handle<migration_table_data>::insert_or_update_unsafe(
    const key_type& k, const mapped_type& d, F f, Types&&... args)
{
    auto slot = slot_type(k, d);
    auto result =
        insert_or_update_unsafe_intern(slot, f, std::forward<Types>(args)...);
    if constexpr (slot_config::needs_cleanup)
    {
        if (!result.second) slot.cleanup();
    }
    return result;
}

template <class migration_table_data>
template <class F, class... Types>
inline typename migration_table_handle<migration_table_data>::insert_return_type
migration_table_handle<migration_table_data>::emplace_or_update_unsafe(
    key_type&& k, mapped_type&& d, F f, Types&&... args)
{
    auto slot = slot_type(std::move(k), std::move(d));
    auto result =
        insert_or_update_unsafe_intern(slot, f, std::forward<Types>(args)...);
    if constexpr (slot_config::needs_cleanup)
    {
        if (!result.second) slot.cleanup();
    }
    return result;
}

template <class migration_table_data>
template <class F, class... Types>
inline typename migration_table_handle<migration_table_data>::insert_return_type
migration_table_handle<migration_table_data>::insert_or_update_unsafe_intern(
    slot_type& slot, F f, Types&&... args)
{
    int                           v = -1;
    base_table_insert_return_type result =
        std::make_pair(bend(), ReturnCode::ERROR);

    std::tie(v, result) = execute(
        [](hash_ptr_reference t, slot_type& slot, F f,
           Types&&... args) -> std::pair<int, base_table_insert_return_type> {
            auto hash = t->h(slot.get_key_ref());
            slot.set_fingerprint(hash);
            std::pair<int, base_table_insert_return_type> result =
                std::make_pair(t->_version, t->insert_or_update_unsafe_intern(
                                                slot, hash, f,
                                                std::forward<Types>(args)...));
            return result;
        },
        slot, f, std::forward<Types>(args)...);

    switch (result.second)
    {
    case ReturnCode::SUCCESS_IN:
    case ReturnCode::TSX_SUCCESS_IN:
        inc_inserted();
        return make_insert_ret(result.first, v, true);
    case ReturnCode::SUCCESS_UP:
    case ReturnCode::TSX_SUCCESS_UP:
        return make_insert_ret(result.first, v, false);
    case ReturnCode::UNSUCCESS_FULL:
    case ReturnCode::TSX_UNSUCCESS_FULL:
        grow(v);
        return insert_or_update_unsafe_intern(slot, f,
                                              std::forward<Types>(args)...);
    case ReturnCode::UNSUCCESS_INVALID:
    case ReturnCode::TSX_UNSUCCESS_INVALID:
        help_grow(v);
        return insert_or_update_unsafe_intern(slot, f,
                                              std::forward<Types>(args)...);
    default:
        return make_insert_ret(bend(), v, false);
    }
}

template <class migration_table_data>
inline typename migration_table_handle<migration_table_data>::iterator
migration_table_handle<migration_table_data>::find(const key_type& k)
{
    int                 v   = -1;
    base_table_iterator bit = bend();
    std::tie(v, bit)        = execute(
        [](hash_ptr_reference t,
           const key_type&    k) -> std::pair<int, base_table_iterator> {
            return std::make_pair<int, base_table_iterator>(t->_version,
                                                            t->find(k));
        },
        k);
    return make_iterator(bit, v);
}

template <class migration_table_data>
inline typename migration_table_handle<migration_table_data>::const_iterator
migration_table_handle<migration_table_data>::find(const key_type& k) const
{
    int                  v   = -1;
    base_table_citerator bit = bcend();
    std::tie(v, bit)         = cexecute(
        [](hash_ptr_reference t,
           const key_type&    k) -> std::pair<int, base_table_citerator> {
            return std::make_pair<int, base_table_iterator>(t->_version,
                                                            t->find(k));
        },
        k);
    return make_citerator(bit, v);
}

template <class migration_table_data>
inline typename migration_table_handle<migration_table_data>::size_type
migration_table_handle<migration_table_data>::erase(const key_type& k)
{
    int        v        = -1;
    ReturnCode result   = ReturnCode::ERROR;
    std::tie(v, result) = execute(
        [](hash_ptr_reference t,
           const key_type&    k) -> std::pair<int, ReturnCode> {
            std::pair<int, ReturnCode> result =
                std::make_pair(t->_version, t->erase_intern(k));
            return result;
        },
        k);

    switch (result)
    {
    case ReturnCode::SUCCESS_DEL:
        inc_deleted();
        return 1;
    case ReturnCode::TSX_SUCCESS_DEL:
        inc_deleted(); // TSX DELETION COULD BE USED TO AVOID DUMMIES =>
                       // dec_inserted()
        return 1;
    case ReturnCode::UNSUCCESS_INVALID:
    case ReturnCode::TSX_UNSUCCESS_INVALID:
        help_grow(v);
        return erase(k);
    case ReturnCode::UNSUCCESS_NOT_FOUND:
    case ReturnCode::TSX_UNSUCCESS_NOT_FOUND:
        return 0;
    default:
        return 0;
    }
}

template <class migration_table_data>
inline typename migration_table_handle<migration_table_data>::size_type
migration_table_handle<migration_table_data>::erase_if(const key_type&    k,
                                                       const mapped_type& d)
{
    int        v        = -1;
    ReturnCode result   = ReturnCode::ERROR;
    std::tie(v, result) = execute(
        [](hash_ptr_reference t, const key_type& k,
           const mapped_type& d) -> std::pair<int, ReturnCode> {
            std::pair<int, ReturnCode> result =
                std::make_pair(t->_version, t->erase_if_intern(k, d));
            return result;
        },
        k, d);

    switch (result)
    {
    case ReturnCode::SUCCESS_DEL:
        inc_deleted();
        return 1;
    case ReturnCode::TSX_SUCCESS_DEL:
        inc_deleted(); // TSX DELETION COULD BE USED TO AVOID DUMMIES =>
                       // dec_inserted()
        return 1;
    case ReturnCode::UNSUCCESS_INVALID:
    case ReturnCode::TSX_UNSUCCESS_INVALID:
        help_grow(v);
        return erase_if(k, d);
    case ReturnCode::UNSUCCESS_NOT_FOUND:
    case ReturnCode::TSX_UNSUCCESS_NOT_FOUND:
        return 0;
    default:
        return 0;
    }
}






// ITERATOR FUNCTIONALITY ******************************************************

template <class migration_table_data>
inline typename migration_table_handle<migration_table_data>::iterator
migration_table_handle<migration_table_data>::begin()
{
    return execute(
        [](hash_ptr_reference t, migration_table_handle& gt) -> iterator {
            return iterator(t->begin(), t->_version, gt);
        },
        *this);
}
template <class migration_table_data>
inline typename migration_table_handle<migration_table_data>::iterator
migration_table_handle<migration_table_data>::end()
{
    return iterator(
        base_table_iterator(slot_config::get_empty(), nullptr, nullptr), 0,
        *this);
}

template <class migration_table_data>
inline typename migration_table_handle<migration_table_data>::const_iterator
migration_table_handle<migration_table_data>::cbegin() const
{
    // return begin();
    return cexecute(
        [](hash_ptr_reference            t,
           const migration_table_handle& gt) -> const_iterator {
            return const_iterator(t->cbegin(), t->_version, gt);
        },
        *this);
}
template <class migration_table_data>
inline typename migration_table_handle<migration_table_data>::const_iterator
migration_table_handle<migration_table_data>::cend() const
{
    // return end();
    return const_iterator(base_table_citerator(std::pair<key_type, mapped_type>(
                                                   key_type(), mapped_type()),
                                               nullptr, nullptr),
                          0, *this);
}





// COUNTING FUNCTIONALITY ******************************************************

template <class migration_table_data>
inline void migration_table_handle<migration_table_data>::update_numbers()
{
    _counts._updates = 0;

    auto table = get_table();
    // if (table->version != size_t(_counts._version))
    // {
    //     _counts.set(table->_version, 0,0,0);
    //     rls_table();
    //     return;
    // }

    _mt_data._dummies.fetch_add(_counts._deleted, std::memory_order_relaxed);

    auto temp = _mt_data._elements.fetch_add(_counts._inserted,
                                             std::memory_order_relaxed);
    temp += _counts._inserted;

    int thresh = table->capacity() * _max_fill_factor;
    if (temp > thresh)
    {
        if (temp - _counts._inserted < thresh)
        {
            int v = table->_version;
            rls_table();
            grow(v);
            _counts.set(0, 0, 0);
            return;
        }
    }
    rls_table();
    _counts.set(0, 0, 0);
}

template <class migration_table_data>
inline void migration_table_handle<migration_table_data>::inc_inserted()
{
    // if (_counts._version == v)
    {
        ++_counts._inserted;
        if (++_counts._updates > 64) { update_numbers(); }
    }
    // else
    // {
    //     _counts.set(v,1,1,0);
    // }
}


template <class migration_table_data>
inline void migration_table_handle<migration_table_data>::inc_deleted()
{
    // if (_counts._version == v)
    {
        ++_counts._deleted;
        if (++_counts._updates > 64) { update_numbers(); }
    }
    // else
    // {
    //     _counts.set(v,1,0,1);
    // }
}

// template <typename migration_table_data>
// inline typename migration_table_handle<migration_table_data>::size_type
// migration_table_handle<migration_table_data>::element_count_unsafe()
// {
//     int v = get_table()->_version;
//     rls_table();

//     int temp = _mt_data._elements.load();
//     temp    -= _mt_data._dummies.load();
//     temp    += _mt_data.handle_ptr.forall([v](this_type* h, int res)
//                                         {
//                                             if (h->_counts._version != v)
//                                             {
//                                                 return res;
//                                             }
//                                             int temp = res;
//                                             temp += h->_counts._inserted;
//                                             temp -= h->_counts._deleted;
//                                             return temp;
//                                         });
//     return temp;
// }

} // namespace growt
