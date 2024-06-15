// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Doubly linked endogenous (intrusive) list
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3LIST_H_
#define VERILATOR_V3LIST_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"

#include <type_traits>
#include <utility>

//============================================================================
// The list links (just 2 pointers), to be instantiated as a member in the
// list element base class 'T_Base'. They are considered mutable, even if the
// list element is 'const', as they are only used for storing the elements in
// a V3List. That is, you can store const elements in a V3List.
template <typename T_Base>
class V3ListLinks final {
    // The V3List itself, but nothing else can access the link pointers
    template <typename B, V3ListLinks<B>& (B::*)(), typename>
    friend class V3List;

    T_Base* m_nextp = nullptr;  // Next element in list
    T_Base* m_prevp = nullptr;  // Previous element in list

public:
    V3ListLinks() = default;
    ~V3ListLinks() {
#ifdef VL_DEBUG
        m_nextp = reinterpret_cast<T_Base*>(1);
        m_prevp = reinterpret_cast<T_Base*>(1);
#endif
    }
    VL_UNCOPYABLE(V3ListLinks);
    VL_UNMOVABLE(V3ListLinks);
};

//============================================================================
// Generic endogenous (or intrusive) doubly linked list, with links stored
// inside the elements. The template parameters are:
// - 'T_Base' is the base type of elements that contains the V3ListLinks
//   instance as a data member.
// - 'LinksGetter' is a member function pointer that returns a reference to
//   the links within 'T_Base'. Note that you should be able to use a data
//   member pointer, instead of a function pointer, but that is buggy in MSVC.
// - 'T_Element' is the actual type of elements, which must be the same,
//    or a subtype of 'T_Base'.
template <typename T_Base,  //
          V3ListLinks<T_Base>& (T_Base::*LinksGetter)(),  //
          typename T_Element = T_Base>
class V3List final {
    static_assert(std::is_base_of<T_Base, T_Element>::value,
                  "'T_Element' must be a subtype of 'T_Base");

    using ListType = V3List<T_Base, LinksGetter, T_Element>;

    // MEMBERS
    T_Base* m_headp = nullptr;
    T_Base* m_lastp = nullptr;

    // Given the T_Base, return the Links. The links are always mutable, even in const elements.
    VL_ATTR_ALWINLINE
    static V3ListLinks<T_Base>& toLinks(const T_Base* elementp) {
        return (const_cast<T_Base*>(elementp)->*LinksGetter)();
    }

    VL_ATTR_ALWINLINE
    static void prefetch(const T_Base* elementp, const T_Base* fallbackp) {
        UDEBUGONLY(UASSERT(fallbackp, "Prefetch fallback pointer must be non nullptr"););
        // This compiles to a branchless prefetch with cmove, with the address always valid
        VL_PREFETCH_RW(elementp ? elementp : fallbackp);
    }

    // Iterator class template for V3List. This is just enough to support range based for loops
    // and basic usage. Feel free to extend as required.
    template <typename T_IteratorElement, bool T_Reverse>
    class SimpleItertatorImpl final {
        static_assert(std::is_same<T_IteratorElement, T_Element>::value
                          || std::is_same<T_IteratorElement, const T_Element>::value,
                      "'SimpleItertatorImpl' must be used with element type only");

        // The List itself, but nothing else can construct iterators
        template <typename B, V3ListLinks<B>& (B::*)(), typename>
        friend class V3List;

        using IteratorType = SimpleItertatorImpl<T_IteratorElement, T_Reverse>;

        T_Base* m_currp;  // Currently iterated element, or 'nullptr' for 'end()' iterator

        VL_ATTR_ALWINLINE
        explicit SimpleItertatorImpl(T_Base* elementp)
            : m_currp{elementp} {}

        VL_ATTR_ALWINLINE
        static T_Base* step(T_Base* currp) {
            if VL_CONSTEXPR_CXX17 (T_Reverse) {
                return toLinks(currp).m_prevp;
            } else {
                return toLinks(currp).m_nextp;
            }
        }

    public:
        // Dereference
        VL_ATTR_ALWINLINE
        T_IteratorElement& operator*() const {
            UDEBUGONLY(UASSERT(m_currp, "Dereferencing end of list iterator"););
            prefetch(step(m_currp), m_currp);
            return *static_cast<T_IteratorElement*>(m_currp);
        }
        // Pre increment
        VL_ATTR_ALWINLINE
        IteratorType& operator++() {
            UDEBUGONLY(UASSERT(m_currp, "Pre-incrementing end of list iterator"););
            m_currp = step(m_currp);
            return *this;
        }
        // Post increment
        VL_ATTR_ALWINLINE
        IteratorType operator++(int) {
            UDEBUGONLY(UASSERT(m_currp, "Post-incrementing end of list iterator"););
            T_Base* const elementp = m_currp;
            m_currp = step(m_currp);
            return IteratorType{elementp};
        }
        VL_ATTR_ALWINLINE
        bool operator==(const IteratorType& other) const { return m_currp == other.m_currp; }
        VL_ATTR_ALWINLINE
        bool operator!=(const IteratorType& other) const { return m_currp != other.m_currp; }
        // Convert to const iterator
        VL_ATTR_ALWINLINE
        operator SimpleItertatorImpl<const T_IteratorElement, T_Reverse>() const {
            return SimpleItertatorImpl<const T_IteratorElement, T_Reverse>{m_currp};
        }
    };

    // Proxy class for creating unlinkable iterators, so we can use
    // 'for (T_Element* const ptr : list.unlinkable()) list.unlink(ptr);'
    class UnlinkableProxy final {
        // The List itself, but nothing else can construct UnlinkableProxy
        template <typename B, V3ListLinks<B>& (B::*)(), typename>
        friend class V3List;

        ListType& m_list;  // The proxied list

        explicit UnlinkableProxy(ListType& list)
            : m_list{list} {}

        // Unlinkable iterator class template. This only supports enough for range based for loops.
        // If you want something fancier, use and manage the direct iterator manually.
        template <typename T_IteratorElement>
        class UnlinkableItertatorImpl final {
            static_assert(std::is_same<T_IteratorElement, T_Element>::value
                              || std::is_same<T_IteratorElement, const T_Element>::value,
                          "'UnlinkableItertatorImpl' must be used with element type only");

            // The UnlinkableProxy, but nothing else can construct unlinkable iterators
            friend class UnlinkableProxy;

            using IteratorType = UnlinkableItertatorImpl<T_IteratorElement>;

            T_Base* m_currp;  // Currently iterated element, or 'nullptr' for 'end()' iterator
            T_Base* m_nextp;  // Next element after current, or 'nullptr' for 'end()' iterator

            VL_ATTR_ALWINLINE
            explicit UnlinkableItertatorImpl(T_Base* elementp)
                : m_currp{elementp}
                , m_nextp{toLinks(m_currp).m_nextp} {}
            VL_ATTR_ALWINLINE
            explicit UnlinkableItertatorImpl(std::nullptr_t)
                : m_currp{nullptr}
                , m_nextp{nullptr} {}

        public:
            // Dereference - Note this returns a pointer.
            VL_ATTR_ALWINLINE
            T_IteratorElement* operator*() const {
                UDEBUGONLY(UASSERT(m_currp, "Dereferencing end of list iterator"););
                prefetch(m_nextp, m_currp);
                return static_cast<T_IteratorElement*>(m_currp);
            }
            // Pre increment - Keeps hold of current next pointer.
            VL_ATTR_ALWINLINE
            IteratorType& operator++() {
                UDEBUGONLY(UASSERT(m_currp, "Pre-incrementing end of list iterator"););
                m_currp = m_nextp;
                m_nextp = m_currp ? toLinks(m_currp).m_nextp : nullptr;
                return *this;
            }
            VL_ATTR_ALWINLINE
            bool operator!=(const IteratorType& other) const { return m_currp != other.m_currp; }
        };

    public:
        using iterator = UnlinkableItertatorImpl<T_Element>;
        using const_iterator = UnlinkableItertatorImpl<const T_Element>;
        iterator begin() {  //
            return m_list.m_headp ? iterator{m_list.m_headp} : end();
        }
        const_iterator begin() const {
            return m_list.m_headp ? const_iterator{m_list.m_headp} : end();
        }
        iterator end() { return iterator{nullptr}; }
        const_iterator end() const { return const_iterator{nullptr}; }
    };

public:
    using iterator = SimpleItertatorImpl<T_Element, /* T_Reverse: */ false>;
    using const_iterator = SimpleItertatorImpl<const T_Element, /* T_Reverse: */ false>;
    using reverse_iterator = SimpleItertatorImpl<T_Element, /* T_Reverse: */ true>;
    using const_reverse_iterator = SimpleItertatorImpl<const T_Element, /* T_Reverse: */ true>;

    // CONSTRUCTOR
    V3List() = default;
    ~V3List() {
#ifdef VL_DEBUG
        m_headp = reinterpret_cast<T_Element*>(1);
        m_lastp = reinterpret_cast<T_Element*>(1);
#endif
    }
    VL_UNCOPYABLE(V3List);
    VL_UNMOVABLE(V3List);

    // METHDOS
    bool empty() const { return !m_headp; }
    bool hasSingleElement() const { return m_headp && m_headp == m_lastp; }
    bool hasMultipleElements() const { return m_headp && m_headp != m_lastp; }

    // These return pointers, as we often want to unlink/delete them, and can also signal empty
    T_Element* frontp() { return static_cast<T_Element*>(m_headp); }
    const T_Element* frontp() const { return static_cast<T_Element*>(m_headp); }
    T_Element* backp() { return static_cast<T_Element*>(m_lastp); }
    const T_Element* backp() const { return static_cast<T_Element*>(m_lastp); }

    // Standard iterators. The iterator is only invalidated if the element it points to is
    // unlinked. Other list operations do not invalidate the itartor. If you want to be able to
    // unlink the currently iterated element, use 'unlinkable()' below.
    iterator begin() { return iterator{m_headp}; }
    const_iterator begin() const { return const_iterator{m_headp}; }
    iterator end() { return iterator{nullptr}; }
    const_iterator end() const { return const_iterator{nullptr}; }
    reverse_iterator rbegin() { return reverse_iterator{m_lastp}; }
    const_reverse_iterator rbegin() const { return const_reverse_iterator{m_lastp}; }
    reverse_iterator rend() { return reverse_iterator{nullptr}; }
    const_reverse_iterator rend() const { return const_reverse_iterator{nullptr}; }

    // Handle to create unlinkable iterators, which allows unlinking the currently iterated
    // element without invalidating the iterator. However, every other operation that mutates
    // the list invalidates the unlinkable iterator!
    UnlinkableProxy unlinkable() { return UnlinkableProxy{*this}; }

    // Link (insert) existing element at front
    void linkFront(const T_Element* elementp) {
        auto& links = toLinks(elementp);
        links.m_nextp = m_headp;
        links.m_prevp = nullptr;
        if (m_headp) toLinks(m_headp).m_prevp = const_cast<T_Element*>(elementp);
        m_headp = const_cast<T_Element*>(elementp);
        if (!m_lastp) m_lastp = m_headp;
    }

    // Link (insert) existing element at back
    void linkBack(const T_Element* elementp) {
        auto& links = toLinks(elementp);
        links.m_nextp = nullptr;
        links.m_prevp = m_lastp;
        if (m_lastp) toLinks(m_lastp).m_nextp = const_cast<T_Element*>(elementp);
        m_lastp = const_cast<T_Element*>(elementp);
        if (!m_headp) m_headp = m_lastp;
    }

    // Unlink (remove) and return element at the front. Returns 'nullptr' if the list is empty.
    T_Element* unlinkFront() {
        T_Element* const headp = m_headp;
        if (headp) unlink(headp);
        return headp;
    }

    // Unlink (remove) and return element at the back. Returns 'nullptr' if the list is empty.
    T_Element* unlinkBack() {
        T_Element* const lastp = m_lastp;
        if (lastp) unlink(lastp);
        return lastp;
    }

    // Unlink (remove) the given element.
    void unlink(const T_Element* elementp) {
        auto& links = toLinks(elementp);
        if (links.m_nextp) toLinks(links.m_nextp).m_prevp = links.m_prevp;
        if (links.m_prevp) toLinks(links.m_prevp).m_nextp = links.m_nextp;
        if (m_headp == elementp) m_headp = links.m_nextp;
        if (m_lastp == elementp) m_lastp = links.m_prevp;
        links.m_prevp = nullptr;
        links.m_nextp = nullptr;
    }

    // Swap elements of 2 lists
    void swap(ListType& other) {
        std::swap(m_headp, other.m_headp);
        std::swap(m_lastp, other.m_lastp);
    }

    // Take elements from 'other' and link (insert) them all before the given position.
    void splice(const_iterator pos, ListType& other) {
        if (empty()) {
            swap(other);
        } else if (other.empty()) {
            return;
        } else {
            UASSERT(pos == end(), "Sorry, only splicing at the end is implemented at the moment");
            toLinks(m_lastp).m_nextp = other.m_headp;
            toLinks(other.m_headp).m_prevp = m_lastp;
            m_lastp = other.m_lastp;
            other.m_headp = nullptr;
            other.m_lastp = nullptr;
        }
    }

    // This is O(n)!
    size_t size() const {
        size_t result = 0;
        for (auto it = begin(); it != end(); ++it) ++result;
        return result;
    }
};

#endif  // Guard
