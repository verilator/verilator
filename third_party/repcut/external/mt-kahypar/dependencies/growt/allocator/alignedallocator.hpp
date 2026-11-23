/*******************************************************************************
 * utils/aligned_allocator.h
 *
 * Simple allocator using memalign to get aligned memory
 *
 * Part of Project growt - https://github.com/TooBiased/growt.git
 *
 * Copyright (C) 2015-2016 Tobias Maier <t.maier@kit.edu>
 *
 * All rights reserved. Published under the BSD-2 license in the LICENSE file.
 ******************************************************************************/

#ifndef ALIGNED_ALLOCATOR_H
#define ALIGNED_ALLOCATOR_H

#include <algorithm>
#include <malloc.h>
#include <stdlib.h>

namespace growt
{

#define DEFAULT_ALIGNMENT 128 // two cacheline sizes => nicely aligned!

template <class T = char, size_t A = DEFAULT_ALIGNMENT>
class GenericAlignedAllocator
{
  public:
    using value_type      = T;
    using pointer         = T*;
    using const_pointer   = const T*;
    using reference       = T&;
    using const_reference = const T&;
    using size_type       = std::size_t;
    using difference_type = std::ptrdiff_t;

    //! C++11 type flag
    using is_always_equal = std::false_type;
    //! C++11 type flag
    using propagate_on_container_move_assignment = std::true_type;


    //! Return allocator for different type.
    template <class U> struct rebind
    {
        using other = GenericAlignedAllocator<U, A>;
    };


    GenericAlignedAllocator()                                        = default;
    GenericAlignedAllocator(const GenericAlignedAllocator&) noexcept = default;
    template <class U>
    GenericAlignedAllocator(const GenericAlignedAllocator<U>&) noexcept {};
    GenericAlignedAllocator&
    operator=(const GenericAlignedAllocator&) noexcept = default;


    //! Allocates memory for n objects of type T
    pointer allocate(size_type n, const void* /* hint */ = nullptr)
    {

        if (n > max_size()) throw std::bad_alloc();
#ifdef _WIN32
        return static_cast<pointer>(_aligned_malloc(n * sizeof(T), A));
#else
        return static_cast<pointer>(memalign(A, n * sizeof(T)));
#endif
    }

    //! Frees an allocated piece of memory
    void deallocate(pointer p, size_type /* size_hint */ = 0) noexcept
    {
#ifdef _WIN32
        _aligned_free(p);
#else
        free(p);
#endif
    }

    //! Returns the adress of x.
    pointer address(reference x) const noexcept { return std::addressof(x); }

    //! Returns the adress of x.
    const_pointer address(const_reference x) const noexcept
    {
        return std::addressof(x);
    }

    //! Maximum size possible to allocate
    size_type max_size() const noexcept { return size_t(-1) / sizeof(T); }

    //! Constructs an element object on the location pointed by p.
    void construct(pointer p, const_reference value)
    {
        ::new ((void*)p) T(value);
    }

    //! Destroys in-place the object pointed by p.
    void destroy(pointer p) const noexcept { p->~T(); }



    //! Constructs an element object on the location pointed by p.
    template <typename SubType, typename... Args>
    void construct(SubType* p, Args&&... args)
    {
        ::new ((void*)p) SubType(std::forward<Args>(args)...);
    }

    //! Destroys in-place the object pointed by p.
    template <typename SubType> void destroy(SubType* p) const noexcept
    {
        p->~SubType();
    }


    template <class Other, size_t OtherAlignment>
    bool operator==(const GenericAlignedAllocator<Other, OtherAlignment>&)
    {
        return A == OtherAlignment;
    }

    template <class Other, size_t OtherAlignment>
    bool operator!=(const GenericAlignedAllocator<Other, OtherAlignment>&)
    {
        return A != OtherAlignment;
    }
};

template <typename E = char>
using AlignedAllocator = GenericAlignedAllocator<E, DEFAULT_ALIGNMENT>;

} // namespace growt

#endif // ALIGNEDALLOCATOR_H
