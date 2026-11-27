/*******************************************************************************
 * data-structures/base_iterator.h
 *
 * Part of Project growt - https://github.com/TooBiased/growt.git
 *
 * Copyright (C) 2015-2016 Tobias Maier <t.maier@kit.edu>
 *
 * All rights reserved. Published under the BSD-2 license in the LICENSE file.
 ******************************************************************************/

#pragma once

#include <atomic>
#include <tuple>

namespace growt
{

// Forward Declarations ********************************************************
template <class, bool> class migration_table_mapped_reference;
template <class, bool> class migration_table_reference;
template <class, bool> class migration_table_iterator;

template <class, bool> class base_linear_reference;



// Mapped Reference
template <class BaseTable, bool is_const = false>
class base_linear_mapped_reference
{
  private:
    using base_table_type  = BaseTable;
    using key_type         = typename base_table_type::key_type;
    using mapped_type      = typename base_table_type::mapped_type;
    using value_nc         = std::pair<const key_type, mapped_type>;
    using slot_config      = typename base_table_type::slot_config;
    using slot_type        = typename slot_config::slot_type;
    using atomic_slot_type = typename slot_config::atomic_slot_type;

    template <class, bool> friend class migration_table_mapped_reference;
    template <class, bool> friend class migration_table_reference;
    template <class, bool> friend class base_linear_reference;

    struct _overwrite
    {
        mapped_type operator()(mapped_type& lhs, const mapped_type& rhs) const
        {
            lhs = rhs;
            return rhs;
        }
        mapped_type atomic(mapped_type& lhs, const mapped_type& rhs) const
        {
            reinterpret_cast<std::atomic<mapped_type>&>(lhs).store(
                rhs, std::memory_order_relaxed);
            return rhs;
        }
    };

  public:
    using value_type =
        typename std::conditional<is_const, const value_nc, value_nc>::type;

    base_linear_mapped_reference(const slot_type& copy, atomic_slot_type* ptr)
        : _copy(copy), _ptr(ptr)
    {
    }

    inline void refresh() { _copy = *_ptr; }

    template <bool is_const2 = is_const>
    inline
        typename std::enable_if<!is_const2, base_linear_mapped_reference>::type
        operator=(const mapped_type& value)
    {
        _ptr->atomic_update(_copy, _overwrite{}, value);
        return *this;
    }

    template <class F, class... Args> inline bool update(F f, Args&&... args)
    {
        static_assert(!is_const,
                      "update called on const reference to mapped object");
        return _ptr->atomic_update(_copy, f, std::forward<Args>(args)...);
    }

    inline bool compare_exchange(const mapped_type& val)
    {
        // this cannot be reached with a complex slot, where the constructor
        // should not be called here
        if (_ptr->cas(_copy, slot_type(_copy.get_key(), val)))
        {
            _copy.set_mapped(val);
            return true;
        }
        else
        {
            return false;
        }
    }

    inline operator mapped_type() const { return _copy.get_mapped(); }

  private:
    slot_type         _copy;
    atomic_slot_type* _ptr;
};




// Reference *******************************************************************
template <class BaseTable, bool is_const = false> class base_linear_reference
{
  private:
    using base_table_type  = BaseTable;
    using key_type         = typename base_table_type::key_type;
    using mapped_type      = typename base_table_type::mapped_type;
    using value_nc         = std::pair<const key_type, mapped_type>;
    using slot_config      = typename base_table_type::slot_config;
    using slot_type        = typename slot_config::slot_type;
    using atomic_slot_type = typename slot_config::atomic_slot_type;

    using mapped_ref = base_linear_mapped_reference<BaseTable, is_const>;

    template <class, bool> friend class migration_table_reference;
    template <class, bool> friend class migration_table_mapped_reference;

  public:
    using value_type =
        typename std::conditional<is_const, const value_nc, value_nc>::type;

    base_linear_reference(slot_type copy, atomic_slot_type* ptr)
        : second(copy, ptr), first(second._copy.get_key_ref())
    {
    }

    inline void refresh() { second.refresh(); }

    template <class F, class... Args> inline void update(F f, Args&&... args)
    {
        static_assert(!is_const, "update called on a const_reference");
        second.update(f, std::forward<Args>(args)...);
    }

    inline bool compare_exchange(const mapped_type& val)
    {
        static_assert(!is_const,
                      "compare_exchange called on a const_reference");
        return second.compare_exchange(val);
    }

    // inline operator pair_type()  const
    // { return second._copy; }
    inline operator value_type() const { return value_type(second._copy); }

    mapped_ref      second;
    const key_type& first;
};


// Iterator ********************************************************************
template <class BaseTable, bool is_const = false> class base_linear_iterator
{
  private:
    using base_table_type  = BaseTable;
    using key_type         = typename base_table_type::key_type;
    using mapped_type      = typename base_table_type::mapped_type;
    using value_nc         = std::pair<const key_type, mapped_type>;
    using slot_config      = typename base_table_type::slot_config;
    using slot_type        = typename slot_config::slot_type;
    using atomic_slot_type = typename slot_config::atomic_slot_type;

    template <class, bool> friend class migration_table_iterator;
    template <class, bool> friend class migration_table_reference;
    template <class, bool> friend class migration_table_mapped_reference;

    static constexpr bool allows_referential_integrity =
        base_table_type::allows_referential_integrity;
    using maybe_const_mapped_reference =
        typename std::conditional<is_const, const mapped_type&,
                                  mapped_type&>::type;

  public:
    using difference_type = std::ptrdiff_t;
    using value_type =
        typename std::conditional<is_const, const value_nc, value_nc>::type;

    using reference = typename std::conditional<
        allows_referential_integrity, value_type&,
        base_linear_reference<BaseTable, is_const>>::type;

    using mapped_reference = typename std::conditional<
        allows_referential_integrity, maybe_const_mapped_reference,
        base_linear_reference<BaseTable, is_const>>::type;

    using pointer           = value_type*;
    using iterator_category = std::forward_iterator_tag;

    // template<class T, bool b>
    // friend void swap(base_iterator<T,b>& l, base_iterator<T,b>& r);
    template <class T, bool b>
    friend bool operator==(const base_linear_iterator<T, b>& l,
                           const base_linear_iterator<T, b>& r);
    template <class T, bool b>
    friend bool operator!=(const base_linear_iterator<T, b>& l,
                           const base_linear_iterator<T, b>& r);

    // Constructors ************************************************************
    base_linear_iterator(const slot_type& copy, atomic_slot_type* ptr,
                         atomic_slot_type* eptr)
        : _copy(copy), _ptr(ptr), _eptr(eptr)
    {
    }

    base_linear_iterator(const base_linear_iterator& rhs)
        : _copy(rhs._copy), _ptr(rhs._ptr), _eptr(rhs._eptr)
    {
    }

    base_linear_iterator& operator=(const base_linear_iterator& r)
    {
        _copy = r._copy;
        _ptr  = r._ptr;
        _eptr = r._eptr;
        return *this;
    }

    ~base_linear_iterator() = default;

    // Basic Iterator Functionality ********************************************
    inline base_linear_iterator& operator++()
    {
        ++_ptr;
        while (_ptr < _eptr)
        {
            _copy = _ptr->load();
            if (!(_copy.is_empty() || _copy.is_deleted())) return *this;
            ++_ptr;
        }
        if (_ptr == _eptr) { _ptr = nullptr; }
        return *this;
    }

    inline base_linear_iterator& operator++(int)
    {
        base_linear_iterator copy(*this);
        ++(*this);
        return copy;
    }

    inline reference operator*()
    {
        if constexpr (allows_referential_integrity)
            return *(_copy.get_pointer());
        else
            return reference(_copy, _ptr);
    }
    inline pointer operator->()
    {
        static_assert(allows_referential_integrity,
                      "Pointer access is only allowed on tables with "
                      "referential integrity!");
        return _copy.get_pointer();
    }

    inline bool operator==(const base_linear_iterator& rhs) const
    {
        return _ptr == rhs._ptr;
    }
    inline bool operator!=(const base_linear_iterator& rhs) const
    {
        return _ptr != rhs._ptr;
    }

    // Functions necessary for concurrency *************************************
    inline void refresh() { _copy = _ptr->load(); }

    inline bool erase()
    {
        static_assert(!is_const, "erase is called on a const iterator");
        while (!_ptr->atomic_delete(_copy))
        { /*try again*/
        }
        return true;
    }

    inline bool erase_if_unchanged()
    {
        static_assert(!is_const, "erase is called on a const iterator");
        return _ptr->atomic_delete(_copy);
    }

  private:
    slot_type         _copy;
    atomic_slot_type* _ptr;
    atomic_slot_type* _eptr;
};


} // namespace growt
