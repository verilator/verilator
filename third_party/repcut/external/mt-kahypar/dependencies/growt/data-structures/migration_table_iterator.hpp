/*******************************************************************************
 * data-structures/grow_iterator.h
 *
 * Part of Project growt - https://github.com/TooBiased/growt.git
 *
 * Copyright (C) 2015-2016 Tobias Maier <t.maier@kit.edu>
 *
 * All rights reserved. Published under the BSD-2 license in the LICENSE file.
 ******************************************************************************/

#pragma once

#include <functional>

#include "base_linear_iterator.hpp"

namespace growt
{

template <class, bool>
class migration_table_reference;

template <class Table, bool is_const = false>
class migration_table_mapped_reference
{
  private:
    static_assert(
        std::is_same<typename Table::mapped_reference,
                     migration_table_mapped_reference<Table, false>>::value,
        "unexpected mapped_reference type");

    static_assert(
        std::is_same<typename Table::const_mapped_reference,
                     migration_table_mapped_reference<Table, true>>::value,
        "unexpected const_mapped_reference type");

    using this_type = migration_table_mapped_reference<Table, is_const>;
    using table_type =
        typename std::conditional<is_const, const Table, Table>::type;
    using key_type    = typename table_type::key_type;
    using mapped_type = typename table_type::mapped_type;

    using base_mapped_reference = typename std::conditional<
        is_const,
        typename table_type::base_table_type::const_reference::mapped_ref,
        typename table_type::base_table_type::reference::mapped_ref>::type;

    using hash_ptr_reference = typename table_type::hash_ptr_reference;

    template <class, bool>
    friend class migration_table_reference;

  public:
    migration_table_mapped_reference(base_mapped_reference mref,
                                     size_t                ver,
                                     table_type&           table)
        : _tab(table), _version(ver), _mref(mref)
    {
    }


    // Functions necessary for concurrency *************************************
    inline void refresh()
    {
        _tab.execute(
            [&](hash_ptr_reference t, this_type& sref) -> int {
                base_refresh_ptr(t);
                sref._mref.refresh();
                return 0;
            },
            *this);
    }

    template <bool is_const2 = is_const>
    inline typename std::enable_if<!is_const2,
                                   migration_table_mapped_reference>::type
    operator=(const mapped_type& value)
    {
        static_assert(!is_const,
                      "assignment operator called on a const_mapped_reference");
        _tab.execute(
            [](hash_ptr_reference t, this_type& sref,
               const mapped_type& value) -> int {
                sref.base_refresh_ptr(t);
                sref._mref.operator=(value);
                return 0;
            },
            *this, value);
        return *this;
    }
    template <class F, class... Args>
    inline void update(const mapped_type& value, F f, Args&&... args)
    {
        static_assert(!is_const, "update called on a const_mapped_reference");
        _tab.execute(
            [](hash_ptr_reference t, this_type& sref, const mapped_type& value,
               F f, Args&&... args) -> int {
                sref.base_refresh_ptr(t);
                sref._mref.update(f, std::forward<Args>(args)...);
                return 0;
            },
            *this, value, f, std::forward<Args>(args)...);
    }
    inline bool compare_exchange(const mapped_type& val)
    {
        static_assert(!is_const,
                      "compare_exchange called on a const_mapped_reference");
        return _tab.execute(
            [](hash_ptr_reference t, this_type& sref, const mapped_type& val) {
                sref.base_refresh_ptr(t);
                return sref._mref.compare_exchange(val);
            },
            *this, val);
    }

    inline operator mapped_type() const { return mapped_type(_mref); }

  private:
    table_type&           _tab;
    size_t                _version;
    base_mapped_reference _mref;

    // the table should be locked, while this is called
    inline bool base_refresh_ptr(hash_ptr_reference ht)
    {
        if (ht->_version == _version) return false;

        _version = ht->_version;
        auto it  = ht->find(_mref._copy.get_key());
        _mref    = (*it).second;
        return true;
    }
};

template <class Table, bool is_const = false>
class migration_table_reference
{
  private:
    static_assert(std::is_same<typename Table::reference,
                               migration_table_reference<Table, false>>::value,
                  "unexpected reference type");

    static_assert(std::is_same<typename Table::const_reference,
                               migration_table_reference<Table, true>>::value,
                  "unexpected const_reference type");

    using table_type =
        typename std::conditional<is_const, const Table, Table>::type;

    using key_type       = typename table_type::key_type;
    using mapped_type    = typename table_type::mapped_type;
    using base_reference = typename std::conditional<
        is_const,
        typename table_type::base_table_type::const_reference,
        typename table_type::base_table_type::reference>::type;

    using hash_ptr_reference = typename table_type::hash_ptr_reference;
    // using pair_type          = std::pair<key_type, mapped_type>;
    using mapped_ref = migration_table_mapped_reference<Table, is_const>;

  public:
    using value_type = typename base_reference::value_type;

    migration_table_reference(base_reference ref, size_t ver, table_type& table)
        : second(ref.second, ver, table),
          first(second._mref._copy.get_key_ref())
    {
    }


    // Functions necessary for concurrency *************************************
    inline void refresh() { second.refresh(); }

    template <class F>
    inline void update(const mapped_type& value, F f)
    {
        static_assert(!is_const, "update called on a const_reference");
        second.update(value, f);
    }
    inline bool compare_exchange(const mapped_type& val)
    {
        static_assert(!is_const,
                      "compare_exchange called on a const_reference");
        return second.compare_exchange(val);
    }

    // inline operator pair_type()  const { return pair_type (second.ref); }
    inline operator value_type() const { return value_type(second._mref); }

  public:
    mapped_ref      second;
    const key_type& first;
    // const mapped_type& second;
};





template <class Table, bool is_const = false>
class migration_table_iterator
{
  private:
    static_assert(std::is_same<typename Table::iterator,
                               migration_table_iterator<Table, false>>::value,
                  "unexpected migration iterator type");

    static_assert(std::is_same<typename Table::const_iterator,
                               migration_table_iterator<Table, true>>::value,
                  "unexpected const migration iterator type");

    using table_type =
        typename std::conditional<is_const, const Table, Table>::type;
    using key_type         = typename table_type::key_type;
    using mapped_type      = typename table_type::mapped_type;
    using value_nc         = std::pair<const key_type, mapped_type>;
    using slot_config      = typename table_type::slot_config;
    using slot_type        = typename slot_config::slot_type;
    using atomic_slot_type = typename slot_config::atomic_slot_type;

    using hash_ptr_reference = typename table_type::hash_ptr_reference;
    using base_table_type =
        typename std::conditional<is_const,
                                  const typename table_type::base_table_type,
                                  typename table_type::base_table_type>::type;
    using base_iterator =
        typename std::conditional<is_const,
                                  typename base_table_type::const_iterator,
                                  typename base_table_type::iterator>::type;
    static constexpr bool allows_referential_integrity =
        table_type::allows_referential_integrity;

    using maybe_const_mapped_reference = typename std::
        conditional<is_const, const mapped_type&, mapped_type&>::type;

  public:
    using difference_type = std::ptrdiff_t;
    using value_type      = typename base_iterator::value_type;
    using reference       = typename std::conditional<
        allows_referential_integrity,
        value_type&,
        migration_table_reference<Table, is_const>>::type;

    using mapped_reference = typename std::conditional<
        allows_referential_integrity,
        maybe_const_mapped_reference,
        migration_table_mapped_reference<Table, is_const>>::type;

    using pointer           = value_type*;
    using iterator_category = std::forward_iterator_tag;

    // template<class T, bool b>
    // friend void swap(migration_table_iterator<T,b>& l,
    // migration_table_iterator<T,b>& r);
    template <class T, bool b>
    friend bool operator==(const migration_table_iterator<T, b>& l,
                           const migration_table_iterator<T, b>& r);
    template <class T, bool b>
    friend bool operator!=(const migration_table_iterator<T, b>& l,
                           const migration_table_iterator<T, b>& r);


    // Constructors ************************************************************
    migration_table_iterator(base_iterator it,
                             size_t        version,
                             table_type&   table)
        : _tab(table), _version(version), _it(it)
    {
    }

    migration_table_iterator(const migration_table_iterator& rhs)
        : _tab(rhs._tab), _version(rhs._version), _it(rhs._it)
    {
    }

    migration_table_iterator& operator=(const migration_table_iterator& r)
    {
        if (this == &r) return *this;
        this->~migration_table_iterator();

        new (this) migration_table_iterator(r);

        return *this;
    }

    ~migration_table_iterator() = default;


    // Basic Iterator Functionality ********************************************
    inline migration_table_iterator& operator++()
    {
        _tab.cexecute(
            [](hash_ptr_reference t, migration_table_iterator& sit) -> int {
                sit.base_refresh_ptr(t);
                ++sit._it;
                return 0;
            },
            *this);
        return *this;
    }

    inline migration_table_iterator& operator++(int)
    {
        migration_table_iterator copy(*this);
        ++(*this);
        return copy;
    }

    inline reference operator*()
    {
        if constexpr (allows_referential_integrity)
            return *_it;
        else
            return reference(*_it, _version, _tab);
    }
    inline pointer operator->()
    {
        static_assert(allows_referential_integrity,
                      "Pointer access is only allowed on tables with "
                      "referential integrity!");
        return _it.operator->();
    }

    inline bool operator==(const migration_table_iterator& rhs) const
    {
        return _it == rhs._it;
    }
    inline bool operator!=(const migration_table_iterator& rhs) const
    {
        return _it != rhs._it;
    }

    // Functions necessary for concurrency *************************************
    inline void refresh()
    {
        _tab.cexecute(
            [](hash_ptr_reference t, migration_table_iterator& sit) -> int {
                sit.base_refresh_ptr(t);
                sit._it.refresh();
                return 0;
            },
            *this);
    }

    inline bool erase()
    {
        while (true)
        {
            auto res = _tab.cexecute(
                [](hash_ptr_reference        t,
                   migration_table_iterator& sit) -> bool {
                    sit.base_refresh_ptr(t);
                    sit._it.refresh();
                    sit.erase_if_unchanged();
                    return 0;
                },
                *this);
        }
        return true;
    }

    inline bool erase_if_unchanged()
    {
        auto res = _tab.cexecute(
            [](hash_ptr_reference t, migration_table_iterator& sit) -> bool {
                auto val = sit._it._copy.get_key();
                if (sit.base_refresh_ptr(t) && val != sit._it._copy.get_key())
                    return false;

                return sit._it.erase_if_unchanged();
            },
            *this);
        return res;
    }

  private:
    table_type&   _tab;
    size_t        _version;
    base_iterator _it;

    // the table should be locked, while this is called
    inline bool base_refresh_ptr(hash_ptr_reference ht)
    {
        if (ht->_version == _version) return false;

        _version = ht->_version;
        _it      = static_cast<base_table_type&>(*ht).find(_it._copy.get_key());
        return true;
    }
};
} // namespace growt
