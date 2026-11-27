/*******************************************************************************
 * data-structures/base_circular.h
 *
 * Non growing table variant, that is also used by our growing
 * tables to represent the current table.
 *
 * Part of Project growt - https://github.com/TooBiased/growt.git
 *
 * Copyright (C) 2015-2016 Tobias Maier <t.maier@kit.edu>
 *
 * All rights reserved. Published under the BSD-2 license in the LICENSE file.
 ******************************************************************************/

#pragma once

#include <atomic>
#include <functional>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <stdlib.h>
#include <string>

#include "../utils/default_hash.hpp"
// #include "../utils/output.hpp"
// namespace otm = utils_tm::out_tm;

#include "../data-structures/base_linear_iterator.hpp"
#include "../data-structures/returnelement.hpp"
#include "../example/update_fcts.hpp"

namespace growt
{


template <class Slot,
          class HashFct     = utils_tm::hash_tm::default_hash,
          class Alloc       = std::allocator<typename Slot::atomic_slot_type>,
          bool CyclicMap    = false,
          bool CyclicProb   = true,
          bool NeedsCleanup = true>
class base_linear_config
{
  public:
    using slot_config = Slot;
    using allocator_type =
        typename Alloc::template rebind<typename Slot::atomic_slot_type>::other;
    using hash_fct_type = HashFct;

    // base table only needs cleanup if it wasnt growable (then elements are
    // reused) and slot needs cleanup
    static constexpr bool cleanup = NeedsCleanup && Slot::needs_cleanup;

    class mapper_type
    {
      private:
        // capacity is at least twice as large, as the inserted capacity
        static size_t compute_capacity(size_t desired_capacity)
        {
            auto temp = 256u;
            while (temp < desired_capacity) temp <<= 1;
            return temp << 1;
        }

        static size_t compute_right_shift(size_t capacity)
        {
            size_t log_size = 0;
            while (capacity >>= 1) log_size++;
            return 64 - log_size; // HashFct::significant_digits
        }

        void init_helper(size_t capacity);

        size_t _probe_helper;
        size_t _map_helper;
        size_t _grow_helper;

      public:
        mapper_type() : _probe_helper(0), _map_helper(0) {}
        mapper_type(size_t capacity);
        mapper_type(size_t capacity, size_t grow_helper);

        // size_t capacity;

        static constexpr bool   cyclic_mapping = CyclicMap;
        static constexpr bool   cyclic_probing = CyclicProb;
        static constexpr size_t lp_buffer      = 1024;

        size_t total_slots() const;
        size_t addressable_slots() const;
        size_t bitmask() const;
        size_t grow_helper() const;

        size_t      map(size_t hashed) const;
        size_t      remap(size_t hashed) const;
        mapper_type resize(size_t inserted, size_t deleted);
    };
};

template <class Config>
class base_linear
{
  private:
    using this_type = base_linear<Config>;

  protected:
    using config_type    = Config;
    using allocator_type = typename Config::allocator_type;
    using hash_fct_type  = typename Config::hash_fct_type;

    template <class>
    friend class migration_table_handle;
    template <class, bool>
    friend class migration_table_iterator;
    template <class, bool>
    friend class migration_table_mapped_reference;
    template <class>
    friend class estrat_async;
    template <class>
    friend class estrat_sync;
    template <class>
    friend class wstrat_user;

    // _parallel_init = false does not work with the asynchroneous variant
    static constexpr bool _parallel_init = true;

  public:
    using mapper_type      = typename Config::mapper_type;
    using slot_config      = typename Config::slot_config;
    using slot_type        = typename slot_config::slot_type;
    using atomic_slot_type = typename slot_config::atomic_slot_type;

    static constexpr bool allows_deletions = slot_config::allows_deletions;
    static constexpr bool allows_atomic_updates =
        slot_config::allows_atomic_updates;
    static constexpr bool allows_updates = slot_config::allows_updates;
    static constexpr bool allows_referential_integrity =
        slot_config::allows_referential_integrity;

    using key_type        = typename slot_config::key_type;
    using mapped_type     = typename slot_config::mapped_type;
    using value_type      = typename slot_config::value_type;
    using iterator        = base_linear_iterator<this_type, false>;
    using const_iterator  = base_linear_iterator<this_type, true>;
    using size_type       = size_t;
    using difference_type = std::ptrdiff_t;
    using reference       = typename iterator::reference;
    // base_linear_reference<this_type, false>;
    using const_reference = typename const_iterator::reference;
    // base_linear_reference<this_type, true>;
    using mapped_reference = typename iterator::mapped_reference;
    // base_linear_mapped_reference<this_type, false>;
    using const_mapped_reference = typename const_iterator::mapped_reference;
    // base_linear_mapped_reference<this_type, true>;
    using insert_return_type = std::pair<iterator, bool>;


    using local_iterator       = void;
    using const_local_iterator = void;
    using node_type            = void;

    using handle_type = this_type&;

  protected:
    using insert_return_intern = std::pair<iterator, ReturnCode>;

  public:
    base_linear(size_type size_ = 1 << 18);
    base_linear(mapper_type mapper_, size_type version_);

    base_linear(const base_linear&)            = delete;
    base_linear& operator=(const base_linear&) = delete;

    // Obviously move-constructor and move-assignment are not thread safe
    // They are merely comfort functions used during setup
    base_linear(base_linear&& rhs) noexcept;
    base_linear& operator=(base_linear&& rhs) noexcept;

    ~base_linear();

    handle_type get_handle() { return *this; }

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

    inline insert_return_type
    insert_or_assign(const key_type& k, const mapped_type& d)
    {
        return insert_or_update(k, d, example::Overwrite(), d);
    }

    inline mapped_reference operator[](const key_type& k)
    {
        return (*(insert(k, mapped_type()).first)).second;
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

    size_type migrate(this_type& target, size_type s, size_type e);

  protected:
    atomic_slot_type* _table;
    // std::atomic_int*   _init_table;
    mapper_type        _mapper;
    size_type          _version;
    std::atomic_size_t _current_copy_block;
    hash_fct_type      _hash;
    allocator_type     _allocator;


    // size_type   _capacity;
    // size_type   _bitmask;
    // size_type   _right_shift;

    static_assert(std::is_same<typename allocator_type::value_type,
                               atomic_slot_type>::value,
                  "Wrong allocator type given to base_linear!");

    inline size_type h(const key_type& k) const { return _hash(k); }
    // inline size_type map  (const size_type & hashed) const
    // { return hashed >> _right_shift; }
    // inline size_type remap(const size_type & hashed) const
    // {
    //     if constexpr (circular)
    //         return hashed && _bitmask;
    //     else
    //         return hashed;
    // }

  protected:
    insert_return_intern insert_intern(const slot_type& slot, size_type hash);
    ReturnCode           erase_intern(const key_type& k);
    ReturnCode erase_if_intern(const key_type& k, const mapped_type& d);


    template <class F, class... Types>
    insert_return_intern update_intern(const key_type& k, F f, Types&&... args);

    template <class F, class B, class... Types>
    insert_return_intern
    update_with_backoff_intern(const key_type& k, F f, B b, Types&&... args);

    template <class F, class... Types>
    insert_return_intern
    update_unsafe_intern(const key_type& k, F f, Types&&... args);


    template <class F, class... Types>
    insert_return_intern insert_or_update_intern(const slot_type& slot,
                                                 size_type        hash,
                                                 F                f,
                                                 Types&&... args);

    template <class F, class... Types>
    insert_return_intern insert_or_update_unsafe_intern(const slot_type& slot,
                                                        size_type        hash,
                                                        F                f,
                                                        Types&&... args);




    // HELPER FUNCTION FOR ITERATOR CREATION ***********************************

    inline iterator make_iterator(const slot_type& slot, atomic_slot_type* ptr)
    {
        return iterator(slot, ptr, _table + _mapper.total_slots());
    }

    inline const_iterator
    make_citerator(const slot_type& slot, atomic_slot_type* ptr) const
    {
        return const_iterator(slot, ptr, _table + _mapper.total_slots());
    }

    inline insert_return_type
    make_insert_ret(const slot_type& slot, atomic_slot_type* ptr, bool succ)
    {
        return std::make_pair(make_iterator(slot, ptr), succ);
    }

    inline insert_return_type make_insert_ret(iterator it, bool succ)
    {
        return std::make_pair(it, succ);
    }

    inline insert_return_intern make_insert_ret(const slot_type&  slot,
                                                atomic_slot_type* ptr,
                                                ReturnCode        code)
    {
        return std::make_pair(make_iterator(slot, ptr), code);
    }

    inline insert_return_intern make_insert_ret(iterator it, ReturnCode code)
    {
        return std::make_pair(it, code);
    }




    // OTHER HELPER FUNCTIONS **************************************************

    void        initialize(size_t start, size_t end);
    void        initialize(size_t idx);
    void        insert_unsafe(const slot_type& e);
    inline void slot_cleanup() // called, either by the destructor, or by the
                               // destructor of the parenttable
    {
        for (size_t i = 0; i < _mapper.total_slots(); ++i)
            _table[i].load().cleanup();
    }

  public:
    using range_iterator       = iterator;
    using const_range_iterator = const_iterator;

    /* size has to divide capacity */
    range_iterator              range(size_t rstart, size_t rend);
    const_range_iterator        crange(size_t rstart, size_t rend);
    inline range_iterator       range_end() { return end(); }
    inline const_range_iterator range_cend() const { return cend(); }
    inline size_t capacity() const { return _mapper.total_slots(); }

    static std::string name()
    {
        std::stringstream name;
        name << "base_table<" << slot_config::name() << ",";
        if constexpr (mapper_type::cyclic_mapping)
            name << "cmap,";
        else
            name << "lmap,";
        if constexpr (mapper_type::cyclic_probing)
            name << "cprob>";
        else
            name << "lprob>";
        return name.str();
    }
};








// CONSTRUCTORS/ASSIGNMENTS ****************************************************

template <class C>
base_linear<C>::base_linear(size_type capacity_)
    : _mapper(capacity_), _version(0), _current_copy_block(0)
{
    // _table =
    // static_cast<atomic_slot_type*>(malloc(sizeof(atomic_slot_type)*_mapper.capacity+1000));
    auto nslots = _mapper.total_slots();
    _table      = _allocator.allocate(nslots);

    if (!_table) throw std::bad_alloc();

    // otm::buffered_out() << "(allocated ver 0 ptr " << _table << ")" <<
    // std::endl;

    std::fill(_table, _table + nslots, slot_config::get_empty());
}

/*should always be called with a capacity_=2^k  */
template <class C>
base_linear<C>::base_linear(mapper_type mapper_, size_type version_)
    : _mapper(mapper_), _version(version_), _current_copy_block(0)
{
    // _table =
    // static_cast<atomic_slot_type*>(malloc(sizeof(atomic_slot_type)*_mapper.capacity+1000));
    _table = _allocator.allocate(_mapper.total_slots());

    if (!_table) throw std::bad_alloc();

    // otm::buffered_out() << "(allocated ver " << version_ << " ptr " << _table
    // << ")" << std::endl;

    /* The table is initialized in parallel, during the migration */
    if constexpr (!_parallel_init)
    {
        std::fill(_table, _table + _mapper.total_slots(),
                  slot_config::get_empty());
    }
    else if constexpr (!mapper_type::cyclic_probing)
    {
        std::fill(_table + _mapper.addressable_slots(),
                  _table + _mapper.total_slots(), slot_config::get_empty());
    }
}

template <class C>
base_linear<C>::~base_linear()
{
    // std::cout << "~base_linear" << std::endl;
    if constexpr (config_type::cleanup) slot_cleanup();

    // otm::buffered_out() << "(deallocate ver " << _version << " ptr " <<
    // _table << ")" << std::endl;

    if (_table) _allocator.deallocate(_table, _mapper.total_slots());
}


template <class C>
base_linear<C>::base_linear(base_linear&& rhs) noexcept
    : _table(nullptr), _mapper(rhs._mapper), _version(rhs._version),
      _current_copy_block(0)
{
    if (rhs._current_copy_block.load())
        std::invalid_argument("Cannot move a growing table!");
    rhs._mapper = mapper_type();
    std::swap(_table, rhs._table);
}

template <class C>
base_linear<C>& base_linear<C>::operator=(base_linear&& rhs) noexcept
{
    if (this == &rhs) return *this;
    this->~base_linear();
    new (this) base_linear(std::move(rhs));
    return *this;
}








// ITERATOR FUNCTIONALITY ******************************************************

template <class C>
inline typename base_linear<C>::iterator base_linear<C>::begin()
{
    for (size_t i = 0; i < _mapper.total_slots(); ++i)
    {
        auto temp = _table[i].load();
        if (!temp.is_empty() && !temp.is_deleted())
            return make_iterator(temp, &_table[i]);
    }
    return end();
}

template <class C>
inline typename base_linear<C>::iterator base_linear<C>::end()
{
    return iterator(slot_config::get_empty(), nullptr, nullptr);
}


template <class C>
inline typename base_linear<C>::const_iterator base_linear<C>::cbegin() const
{
    for (size_t i = 0; i < _mapper.total_slots(); ++i)
    {
        auto temp = _table[i].load();
        if (!temp.is_empty() && !temp.is_deleted())
            return make_citerator(temp, &_table[i]);
    }
    return end();
}

template <class C>
inline typename base_linear<C>::const_iterator base_linear<C>::cend() const
{
    return const_iterator(slot_config::get_empty(), nullptr, nullptr);
}


// RANGE ITERATOR FUNCTIONALITY ************************************************

template <class C>
inline typename base_linear<C>::range_iterator
base_linear<C>::range(size_t rstart, size_t rend)
{
    auto temp_rend = std::min(rend, _mapper.total_slots());
    for (size_t i = rstart; i < temp_rend; ++i)
    {
        auto temp = _table[i].load();
        if (!temp.is_empty() && !temp.is_deleted())
            return range_iterator(temp, &_table[i], &_table[temp_rend]);
    }
    return range_end();
}

template <class C>
inline typename base_linear<C>::const_range_iterator
base_linear<C>::crange(size_t rstart, size_t rend)
{
    auto temp_rend = std::min(rend, _mapper.total_slots());
    for (size_t i = rstart; i < temp_rend; ++i)
    {
        auto temp = _table[i].load();
        if (!temp.is_empty() && !temp.is_deleted())
            return const_range_iterator(
                std::make_pair(temp.get_key(), temp.get_mapped()), &_table[i],
                &_table[temp_rend]);
    }
    return range_cend();
}



// MAIN HASH TABLE FUNCTIONALITY (INTERN) **************************************

template <class C>
inline typename base_linear<C>::insert_return_intern
base_linear<C>::insert_intern(const slot_type& slot, size_type hash)
{
    const key_type& key = slot.get_key_ref();

    for (size_type i = _mapper.map(hash);; ++i) // i < htemp+MaDis
    {
        size_type temp = _mapper.remap(i);
        auto      curr = _table[temp].load();

        if (curr.is_marked())
        {
            return make_insert_ret(end(), ReturnCode::UNSUCCESS_INVALID);
        }
        else if (curr.is_empty())
        {
            if constexpr (!mapper_type::cyclic_probing)
            {
                if (temp > _mapper.addressable_slots() + 300)
                    return make_insert_ret(end(), ReturnCode::UNSUCCESS_FULL);
            }
            if (_table[temp].cas(curr, slot))
            {
                return make_insert_ret(curr, &_table[temp],
                                       ReturnCode::SUCCESS_IN);
            }
            // somebody changed the current element! recheck it
            --i;
        }
        else if (curr.compare_key(key, hash))
        {
            return make_insert_ret(curr, &_table[temp],
                                   ReturnCode::UNSUCCESS_ALREADY_USED);
        }
        else if (curr.is_deleted())
        {
            // do something appropriate
        }
        // else if (curr.get_mapped() != 666)
        // {
        //     otm::buffered_out() << "unexpected element in insert at:" << temp
        //     << std::endl;
        // }
    }
    return make_insert_ret(end(), ReturnCode::UNSUCCESS_FULL);
}

template <class C>
template <class F, class... Types>
inline typename base_linear<C>::insert_return_intern
base_linear<C>::update_intern(const key_type& k, F f, Types&&... args)
{
    size_type htemp = h(k);

    for (size_type i = _mapper.map(htemp);; ++i) // i < htemp+MaDis
    {
        size_type temp = _mapper.remap(i);
        auto      curr = _table[temp].load();
        if (curr.is_marked())
        {
            return make_insert_ret(end(), ReturnCode::UNSUCCESS_INVALID);
        }
        else if (curr.is_empty())
        {
            return make_insert_ret(end(), ReturnCode::UNSUCCESS_NOT_FOUND);
        }
        else if (curr.compare_key(k, htemp))
        {
            slot_type data = slot_config::get_empty();
            bool      succ;
            std::tie(data, succ) = _table[temp].atomic_update(
                curr, f, std::forward<Types>(args)...);
            if (succ)
                return make_insert_ret(data, &_table[temp],
                                       ReturnCode::SUCCESS_UP);
            i--;
        }
        else if (curr.is_deleted())
        {
            // do something appropriate
        }
    }
    return make_insert_ret(end(), ReturnCode::UNSUCCESS_NOT_FOUND);
}

template <class C>
template <class F, class B, class... Types>
inline typename base_linear<C>::insert_return_intern
base_linear<C>::update_with_backoff_intern(const key_type& k,
                                           F               f,
                                           B               b,
                                           Types&&... args)
{
    size_type htemp = h(k);

    for (size_type i = _mapper.map(htemp);; ++i) // i < htemp+MaDis
    {
        size_type temp = _mapper.remap(i);
        auto      curr = _table[temp].load();
        if (curr.is_marked())
        {
            return make_insert_ret(end(), ReturnCode::UNSUCCESS_INVALID);
        }
        else if (curr.is_empty())
        {
            return make_insert_ret(end(), ReturnCode::UNSUCCESS_NOT_FOUND);
        }
        else if (curr.compare_key(k, htemp))
        {
            slot_type data = slot_config::get_empty();
            bool      succ;
            std::tie(data, succ) = _table[temp].atomic_update(
                curr, f, std::forward<Types>(args)...);
            if (succ)
                return make_insert_ret(data, &_table[temp],
                                       ReturnCode::SUCCESS_UP);
            if (!b(std::forward<Types>(args)...))
                return make_insert_ret(end(), ReturnCode::UNSUCCESS_BACKOFF);
            i--;
        }
        else if (curr.is_deleted())
        {
            // do something appropriate
        }
    }
    return make_insert_ret(end(), ReturnCode::UNSUCCESS_NOT_FOUND);
}

template <class C>
template <class F, class... Types>
inline typename base_linear<C>::insert_return_intern
base_linear<C>::update_unsafe_intern(const key_type& k, F f, Types&&... args)
{
    size_type htemp = h(k);

    for (size_type i = _mapper.map(htemp);; ++i) // i < htemp+MaDis
    {
        size_type temp = _mapper.remap(i);
        auto      curr = _table[temp].load();
        if (curr.is_marked())
        {
            return make_insert_ret(end(), ReturnCode::UNSUCCESS_INVALID);
        }
        else if (curr.is_empty())
        {
            return make_insert_ret(end(), ReturnCode::UNSUCCESS_NOT_FOUND);
        }
        else if (curr.compare_key(k, htemp))
        {
            slot_type data = slot_config::get_empty();
            bool      succ;
            std::tie(data, succ) =
                _table[temp].non_atomic_update(f, std::forward<Types>(args)...);
            if (succ)
                return make_insert_ret(data, &_table[temp],
                                       ReturnCode::SUCCESS_UP);
            i--;
        }
        else if (curr.is_deleted())
        {
            // do something appropriate
        }
    }
    return make_insert_ret(end(), ReturnCode::UNSUCCESS_NOT_FOUND);
}


template <class C>
template <class F, class... Types>
inline typename base_linear<C>::insert_return_intern
base_linear<C>::insert_or_update_intern(const slot_type& slot,
                                        size_type        hash,
                                        F                f,
                                        Types&&... args)
{
    const key_type& key = slot.get_key_ref();

    for (size_type i = _mapper.map(hash);; ++i) // i < htemp+MaDis
    {
        size_type temp = _mapper.remap(i);
        auto      curr = _table[temp].load();
        if (curr.is_marked())
        {
            return make_insert_ret(end(), ReturnCode::UNSUCCESS_INVALID);
        }
        else if (curr.is_empty())
        {
            if constexpr (!mapper_type::cyclic_probing)
            {
                if (temp > _mapper.addressable_slots() + 300)
                    return make_insert_ret(end(), ReturnCode::UNSUCCESS_FULL);
            }
            if (_table[temp].cas(curr, slot))
                return make_insert_ret(slot, &_table[temp],
                                       ReturnCode::SUCCESS_IN);

            // somebody changed the current element! recheck it
            --i;
        }
        else if (curr.compare_key(key, hash))
        {
            slot_type data = slot_config::get_empty();
            bool      succ;
            std::tie(data, succ) = _table[temp].atomic_update(
                curr, f, std::forward<Types>(args)...);
            if (succ)
                return make_insert_ret(data, &_table[temp],
                                       ReturnCode::SUCCESS_UP);
            i--;
        }
        else if (curr.is_deleted())
        {
            // do something appropriate
        }
    }
    return make_insert_ret(end(), ReturnCode::UNSUCCESS_FULL);
}

template <class C>
template <class F, class... Types>
inline typename base_linear<C>::insert_return_intern
base_linear<C>::insert_or_update_unsafe_intern(const slot_type& slot,
                                               size_type        hash,
                                               F                f,
                                               Types&&... args)
{
    const key_type& key = slot.get_key_ref();

    for (size_type i = _mapper.map(hash);; ++i) // i < hash+MaDis
    {
        size_type temp = _mapper.remap(i);
        auto      curr = _table[temp].load();
        if (curr.is_marked())
        {
            return make_insert_ret(end(), ReturnCode::UNSUCCESS_INVALID);
        }
        else if (curr.is_empty())
        {
            if constexpr (!mapper_type::cyclic_probing)
            {
                if (temp > _mapper.addressable_slots() + 300)
                    return make_insert_ret(end(), ReturnCode::UNSUCCESS_FULL);
            }
            if (_table[temp].cas(curr, slot))
                return make_insert_ret(slot, &_table[temp],
                                       ReturnCode::SUCCESS_IN);
            // somebody changed the current element! recheck it
            --i;
        }
        else if (curr.compare_key(key, hash))
        {
            slot_type data = slot_config::get_empty();
            bool      succ;
            std::tie(data, succ) =
                _table[temp].non_atomic_update(f, std::forward<Types>(args)...);
            if (succ)
                return make_insert_ret(data, &_table[temp],
                                       ReturnCode::SUCCESS_UP);
            i--;
        }
        else if (curr.is_deleted())
        {
            // do something appropriate
        }
    }
    return make_insert_ret(end(), ReturnCode::UNSUCCESS_FULL);
}

template <class C>
inline ReturnCode base_linear<C>::erase_intern(const key_type& k)
{
    size_type htemp = h(k);

    for (size_type i = _mapper.map(htemp);; ++i) // i < htemp+MaDis
    {
        size_type temp = _mapper.remap(i);
        auto      curr = _table[temp].load();
        if (curr.is_marked()) { return ReturnCode::UNSUCCESS_INVALID; }
        else if (curr.is_empty()) { return ReturnCode::UNSUCCESS_NOT_FOUND; }
        else if (curr.compare_key(k, htemp))
        {
            if (_table[temp].atomic_delete(curr))
            {
                return ReturnCode::SUCCESS_DEL;
            }
            i--;
        }
        else if (curr.is_deleted())
        {
            // do something appropriate
        }
    }

    return ReturnCode::UNSUCCESS_NOT_FOUND;
}

template <class C>
inline ReturnCode
base_linear<C>::erase_if_intern(const key_type& k, const mapped_type& d)
{
    size_type htemp = h(k);
    for (size_type i = _mapper.map(htemp);; ++i) // i < htemp+MaDis
    {
        size_type temp = _mapper.remap(i);
        auto      curr = _table[temp].load();
        if (curr.is_marked()) { return ReturnCode::UNSUCCESS_INVALID; }
        else if (curr.is_empty()) { return ReturnCode::UNSUCCESS_NOT_FOUND; }
        else if (curr.compare_key(k, htemp))
        {
            if (curr.get_mapped() != d) return ReturnCode::UNSUCCESS_NOT_FOUND;

            if (_table[temp].atomic_delete(curr))
                return ReturnCode::SUCCESS_DEL;
            i--;
        }
        else if (curr.is_deleted())
        {
            // do something appropriate
        }
    }

    return ReturnCode::UNSUCCESS_NOT_FOUND;
}





// MAIN HASH TABLE FUNCTIONALITY (EXTERN) **************************************

template <class C>
inline typename base_linear<C>::iterator base_linear<C>::find(const key_type& k)
{
    size_type htemp = h(k);
    for (size_type i = _mapper.map(htemp);; ++i)
    {
        auto temp = _mapper.remap(i);
        auto curr = _table[temp].load();
        if (curr.is_empty()) return end();
        if (curr.compare_key(k, htemp))
            return make_iterator(curr, &_table[temp]);
    }
    return end();
}

template <class C>
inline typename base_linear<C>::const_iterator
base_linear<C>::find(const key_type& k) const
{
    size_type htemp = h(k);
    for (size_type i = _mapper.map(htemp);; ++i)
    {
        auto temp = _mapper.remap(i);
        auto curr = _table[temp].load();
        if (curr.is_empty()) return cend();
        if (curr.compare_key(k, htemp))
            return make_citerator(curr, &_table[temp]);
    }
    return cend();
}

template <class C>
inline typename base_linear<C>::insert_return_type
base_linear<C>::insert(const key_type& k, const mapped_type& d)
{
    auto hash        = h(k);
    auto slot        = slot_type(k, d, hash);
    auto [it, rcode] = insert_intern(slot, hash);
    if constexpr (slot_config::needs_cleanup)
    {
        if (!successful(rcode)) slot.cleanup();
    }
    return std::make_pair(it, successful(rcode));
}


template <class C>
inline typename base_linear<C>::insert_return_type
base_linear<C>::insert(const value_type& e)
{
    auto hash        = h(e.first);
    auto slot        = slot_type(e, hash);
    auto [it, rcode] = insert_intern(e.first, e.second);
    if constexpr (slot_type::needs_cleanup)
    {
        if (!successful(rcode)) slot.cleanup();
    }
    return std::make_pair(it, successful(rcode));
}

template <class C>
template <class... Args>
inline typename base_linear<C>::insert_return_type
base_linear<C>::emplace(Args&&... args)
{
    auto slot        = slot_type(std::forward<Args>(args)...);
    auto hash        = h(slot.get_key_ref());
    auto [it, rcode] = insert_intern(slot, hash);
    if constexpr (slot_config::needs_cleanup)
    {
        if (!successful(rcode)) slot.cleanup();
    }
    return std::make_pair(it, successful(rcode));
}

template <class C>
inline typename base_linear<C>::size_type
base_linear<C>::erase(const key_type& k)
{
    ReturnCode c = erase_intern(k);
    return (successful(c)) ? 1 : 0;
}

template <class C>
inline typename base_linear<C>::size_type
base_linear<C>::erase_if(const key_type& k, const mapped_type& d)
{
    ReturnCode c = erase_if_intern(k, d);
    return (successful(c)) ? 1 : 0;
}

template <class C>
template <class F, class... Types>
inline typename base_linear<C>::insert_return_type
base_linear<C>::update(const key_type& k, F f, Types&&... args)
{
    auto [it, rcode] = update_intern(k, f, std::forward<Types>(args)...);
    return std::make_pair(it, successful(rcode));
}

template <class C>
template <class F, class B, class... Types>
inline typename base_linear<C>::insert_return_type
base_linear<C>::update_with_backoff(const key_type& k,
                                    F               f,
                                    B               b,
                                    Types&&... args)
{
    auto [it, rcode] =
        update_with_backoff_intern(k, f, b, std::forward<Types>(args)...);
    return std::make_pair(it, successful(rcode));
}


template <class C>
template <class F, class... Types>
inline typename base_linear<C>::insert_return_type
base_linear<C>::update_unsafe(const key_type& k, F f, Types&&... args)
{
    auto [it, rcode] = update_unsafe_intern(k, f, std::forward<Types>(args)...);
    return std::make_pair(it, successful(rcode));
}

template <class C>
template <class F, class... Types>
inline typename base_linear<C>::insert_return_type
base_linear<C>::insert_or_update(const key_type&    k,
                                 const mapped_type& d,
                                 F                  f,
                                 Types&&... args)
{
    auto hash = h(k);
    auto slot = slot_type(k, d, hash);
    auto [it, rcode] =
        insert_or_update_intern(slot, hash, f, std::forward<Types>(args)...);
    if constexpr (slot_config::needs_cleanup)
    {
        if (rcode != ReturnCode::SUCCESS_IN) slot.cleanup();
    }
    return std::make_pair(it, (rcode == ReturnCode::SUCCESS_IN));
}

template <class C>
template <class F, class... Types>
inline typename base_linear<C>::insert_return_type
base_linear<C>::emplace_or_update(key_type&&    k,
                                  mapped_type&& d,
                                  F             f,
                                  Types&&... args)
{
    auto hash = h(k);
    auto slot = slot_type(std::move(k), std::move(d), hash);
    auto [it, rcode] =
        insert_or_update_intern(slot, hash, f, std::forward<Types>(args)...);
    if constexpr (slot_config::needs_cleanup)
    {
        if (rcode != ReturnCode::SUCCESS_IN) slot.cleanup();
    }
    return std::make_pair(it, (rcode == ReturnCode::SUCCESS_IN));
}

template <class C>
template <class F, class... Types>
inline typename base_linear<C>::insert_return_type
base_linear<C>::insert_or_update_unsafe(const key_type&    k,
                                        const mapped_type& d,
                                        F                  f,
                                        Types&&... args)
{
    auto hash        = h(k);
    auto slot        = slot_type(k, d, hash);
    auto [it, rcode] = insert_or_update_unsafe_intern(
        slot, hash, f, std::forward<Types>(args)...);
    if constexpr (slot_type::needs_cleanup)
    {
        if (rcode != ReturnCode::SUCCESS_IN) slot.cleanup();
    }
    return std::make_pair(it, (rcode == ReturnCode::SUCCESS_IN));
}

template <class C>
template <class F, class... Types>
inline typename base_linear<C>::insert_return_type
base_linear<C>::emplace_or_update_unsafe(key_type&&    k,
                                         mapped_type&& d,
                                         F             f,
                                         Types&&... args)
{
    auto hash        = h(k);
    auto slot        = slot_type(std::move(k), std::move(d), hash);
    auto [it, rcode] = insert_or_update_unsafe_intern(
        slot, hash, f, std::forward<Types>(args)...);
    if constexpr (slot_type::needs_cleanup)
    {
        if (rcode != ReturnCode::SUCCESS_IN) slot.cleanup();
    }
    return std::make_pair(it, (rcode == ReturnCode::SUCCESS_IN));
}








// MIGRATION/GROWING STUFF *****************************************************

// TRIVIAL MIGRATION (ASSUMES INITIALIZED TABLE)
// template<class C>
// inline typename base_linear<C>::size_type
// base_linear<C>::migrate(this_type& target, size_type s, size_type e)
// {
//     size_type count = 0;
//     for (size_t i = s; i < e; ++i)
//     {
//         auto curr = _table[i];
//         while (! _table[i].atomic_mark(curr))
//         { /* retry until we successfully mark the element */ }

//         target.insert(curr.get_key(), curr.get_mapped());
//         ++count;
//     }

//     return count;
// }

template <class C>
inline typename base_linear<C>::size_type
base_linear<C>::migrate(this_type& target, size_type s, size_type e)
{
    size_type n    = 0;
    long long i    = s;
    auto      curr = slot_config::get_empty();

    if (mapper_type::cyclic_probing || s > 0)
    {
        // FINDS THE FIRST EMPTY BUCKET (START OF IMPLICIT BLOCK)
        while (i < long(e))
        {
            curr = _table[i].load(); // no bitmask necessary (within one block)
            if (curr.is_empty())
            {
                if (_table[i].atomic_mark(curr))
                    break;
                else
                    --i;
            }
            ++i;
        }
    }

    if (i >= long(e)) return 0;

    // if (!s && i) std::cout << "bla" << std::endl;
    // std::fill(target._table+(i<<shift), target._table+(e<<shift),
    // slot_config::get_empty());
    target.initialize(i, e);

    // MIGRATE UNTIL THE END OF THE BLOCK
    for (; i < long(e); ++i)
    {
        curr = _table[i].load();
        if (!_table[i].atomic_mark(curr))
        {
            --i;
            continue;
        }
        else if (!curr.is_empty())
        {
            if (!curr.is_deleted())
            {
                // if (curr.get_mapped() == 15926) std::cout << "moving first"
                // << std::endl;
                target.insert_unsafe(curr);
                ++n;
            }
        }
    }

    auto b = true; // b indicates, if t[i-1] was non-empty

    // CONTINUE UNTIL WE FIND AN EMPTY BUCKET
    // THE TARGET POSITIONS WILL NOT BE INITIALIZED
    for (; b; ++i)
    {
        auto pos = _mapper.remap(i);
        // auto t_pos= pos<<shift;
        // for (size_type j = 0; j < 1ull<<shift; ++j)
        //     target._table[t_pos+j].non_atomic_set(slot_config::get_empty());
        target.initialize(pos);

        curr = _table[pos].load();

        if (!_table[pos].atomic_mark(curr)) --i;

        if ((b = !curr.is_empty())) // this might be nicer as an else if, but
                                    // this is faster
        {
            if (!curr.is_deleted())
            {
                target.insert_unsafe(curr);
                n++;
            }
        }
    }
    // if constexpr (!mapper_type::cyclic_probing &&
    // mapper_type::cyclic_mapping)
    // {
    //     if (e == _mapper.addressable_slots())
    //     {
    //         i = 0;
    //         b = true; // b indicates, if t[i-1] was non-empty

    //         for (; b; ++i)
    //         {
    //             auto pos  = _mapper.remap(i);
    //             // auto t_pos= pos<<shift;
    //             // for (size_type j = 0; j < 1ull<<shift; ++j)
    //             //
    //             target._table[t_pos+j].non_atomic_set(slot_config::get_empty());
    //             target.initialize(pos);

    //             curr = _table[pos].load();

    //             if (! _table[pos].atomic_mark(curr)) --i;
    //             else if ( (b = ! curr.is_empty()) ) // this might be nicer as
    //             an else if, but this is faster
    //             {
    //                 if (!curr.is_deleted())
    //                 {
    //                     target.insert_unsafe(curr); n++;
    //                 }
    //             }
    //         }
    //     }
    // }

    // std::cout << "migrated one block" << std::endl;
    return n;
}

template <class C>
inline void base_linear<C>::initialize(size_t start, size_t end)
{
    if constexpr (!_parallel_init) return;
    if constexpr (mapper_type::cyclic_mapping)
    {
        for (size_t i = start, j = end; i <= _mapper.bitmask();
             i += _mapper.grow_helper(), j += _mapper.grow_helper())
        {
            std::fill(_table + i, _table + j, slot_config::get_empty());
        }
    }
    else
    {
        std::fill(_table + (start << _mapper.grow_helper()),
                  _table + (end << _mapper.grow_helper()),
                  slot_config::get_empty());
    }
}

template <class C>
inline void base_linear<C>::initialize(size_t idx)
{
    if constexpr (!_parallel_init) return;
    if constexpr (mapper_type::cyclic_mapping)
    {
        if constexpr (!mapper_type::cyclic_probing)
        {
            if (idx >= _mapper.grow_helper()) return;
        }
        for (size_t i = idx; i <= _mapper.bitmask(); i += _mapper.grow_helper())
        {
            _table[i].non_atomic_set(slot_config::get_empty());
        }
    }
    else
    {
        std::fill(_table + (idx << _mapper.grow_helper()),
                  _table + ((idx + 1) << _mapper.grow_helper()),
                  slot_config::get_empty());
    }
}

template <class C>
inline void base_linear<C>::insert_unsafe(const slot_type& e)
{
    const key_type k = e.get_key();

    // if (e.get_mapped() != 666)
    //     otm::buffered_out() << "unsafe inserting weird element" << std::endl;

    size_type htemp = h(k);
    for (size_type i = _mapper.map(htemp);; ++i)
    {
        size_type temp = _mapper.remap(i);
        auto      curr = _table[temp].load();

        if (curr.is_empty())
        {
            _table[temp].non_atomic_set(e);
            return;
        }
    }
    throw std::bad_alloc();
}





// base_linear_config stuff
template <class S, class H, class A, bool CM, bool CP, bool CU>
base_linear_config<S, H, A, CM, CP, CU>::mapper_type::mapper_type(
    size_t capacity)
{
    auto tcapacity = compute_capacity(capacity);
    init_helper(tcapacity);
    _grow_helper = 0;
}

template <class S, class H, class A, bool CM, bool CP, bool CU>
base_linear_config<S, H, A, CM, CP, CU>::mapper_type::mapper_type(
    size_t capacity, size_t grow_helper)
{
    init_helper(capacity);
    _grow_helper = grow_helper;
}

template <class S, class H, class A, bool CM, bool CP, bool CU>
void base_linear_config<S, H, A, CM, CP, CU>::mapper_type::init_helper(
    size_t capacity)
{
    if constexpr (cyclic_probing)
        _probe_helper = capacity - 1;
    else
        _probe_helper = capacity + lp_buffer;

    if constexpr (cyclic_mapping)
        _map_helper = capacity - 1;
    else
        _map_helper = compute_right_shift(capacity);
}


template <class S, class H, class A, bool CM, bool CP, bool CU>
inline size_t
base_linear_config<S, H, A, CM, CP, CU>::mapper_type::total_slots() const
{
    if constexpr (cyclic_probing)
        return _probe_helper + 1;
    else
        return _probe_helper;
}

template <class S, class H, class A, bool CM, bool CP, bool CU>
inline size_t
base_linear_config<S, H, A, CM, CP, CU>::mapper_type::addressable_slots() const
{
    if constexpr (cyclic_probing)
        return _probe_helper + 1;
    else
        return _probe_helper - lp_buffer;
}

template <class S, class H, class A, bool CM, bool CP, bool CU>
inline size_t
base_linear_config<S, H, A, CM, CP, CU>::mapper_type::bitmask() const
{
    if constexpr (cyclic_probing)
        return _probe_helper;
    else if constexpr (cyclic_mapping)
        return _map_helper;
    else
        return _probe_helper - lp_buffer - 1;
}

template <class S, class H, class A, bool CM, bool CP, bool CU>
inline size_t
base_linear_config<S, H, A, CM, CP, CU>::mapper_type::grow_helper() const
{
    return _grow_helper;
}

template <class S, class H, class A, bool CM, bool CP, bool CU>
inline size_t
base_linear_config<S, H, A, CM, CP, CU>::mapper_type::map(size_t hashed) const
{
    if constexpr (cyclic_mapping)
        return hashed & _map_helper;
    else
        return hashed >> _map_helper;
}

template <class S, class H, class A, bool CM, bool CP, bool CU>
inline size_t
base_linear_config<S, H, A, CM, CP, CU>::mapper_type::remap(size_t hashed) const
{
    if constexpr (cyclic_probing)
        return hashed & _probe_helper;
    else
        return hashed;
}

template <class S, class H, class A, bool CM, bool CP, bool CU>
inline typename base_linear_config<S, H, A, CM, CP, CU>::mapper_type
base_linear_config<S, H, A, CM, CP, CU>::mapper_type::resize(size_t inserted,
                                                             size_t deleted)
{
    auto   nsize     = addressable_slots();
    double fill_rate = double(inserted - deleted) / double(nsize);

    if (fill_rate > 0.3) nsize <<= 1;

    size_t temp = 0;
    if constexpr (cyclic_mapping) { temp = addressable_slots(); }
    else { temp = (fill_rate > 0.3) ? 1 : 0; }

    return mapper_type(nsize, temp);
}


} // namespace growt
