#pragma once

#include <atomic>
#include <mutex>
#include <tuple>
#include <vector>

#include "../concurrency/memory_order.hpp"
#include "../data_structures/circular_buffer.hpp"
#include "../debug.hpp"
#include "../mark_pointer.hpp"
#include "../output.hpp"

#include "default_destructor.hpp"
#include "reclamation_guard.hpp"

namespace utils_tm
{
namespace reclamation_tm
{

namespace ctm = concurrency_tm;

template <class T,
          class Destructor             = default_destructor<T>,
          template <class> class Queue = circular_buffer>
class counting_manager
{
  private:
    using memo = concurrency_tm::standard_memory_order_policy;

    class _counted_object : public T
    {
      public:
        template <class... Args>
        _counted_object(Args&&... arg);

        void erase();

        template <class... Args>
        void emplace(Args&&... arg);

        void               increment_counter();
        [[nodiscard]] bool decrement_counter();
        [[nodiscard]] bool mark_deletion();
        bool               is_safe();
        bool               reset();
        void               print() const;

      private:
        std::atomic_uint      _counter;
        static constexpr unsigned int del_flag = 1 << 31;
    };

    using this_type       = counting_manager<T, Destructor, Queue>;
    using destructor_type = Destructor;
    using internal_type   = _counted_object;
    using queue_type      = Queue<internal_type*>;

  public:
    using pointer_type        = T*;
    using atomic_pointer_type = std::atomic<T*>;
    using protected_type      = internal_type;

    template <class lT                  = T,
              class lD                  = default_destructor<lT>,
              template <class> class lQ = Queue>
    struct rebind
    {
        using other = counting_manager<lT, lD, lQ>;
    };



    counting_manager(Destructor&& destructor = Destructor())
        : _destructor(std::move(destructor))
    {
    }
    counting_manager(const counting_manager&) = delete;
    counting_manager& operator=(const counting_manager&) = delete;
    counting_manager(counting_manager&& other);
    counting_manager& operator=(counting_manager&& other);
    ~counting_manager();

    class handle_type
    {
      private:
        using parent_type   = counting_manager<T, Destructor, Queue>;
        using this_type     = handle_type;
        using internal_type = typename parent_type::internal_type;

      public:
        using pointer_type        = typename parent_type::pointer_type;
        using atomic_pointer_type = typename parent_type::atomic_pointer_type;
        using guard_type          = reclamation_guard<T, this_type>;

        handle_type(parent_type& parent) : n(0), _parent(parent) {}
        handle_type(const handle_type&) = delete;
        handle_type& operator=(const handle_type&) = delete;
        handle_type(handle_type&& other) noexcept  = default;
        handle_type& operator=(handle_type&& other) noexcept = default;
        ~handle_type()                                       = default;

        size_t n;

      private:
        parent_type& _parent;

      public:
        template <class... Args>
        inline T* create_pointer(Args&&... arg) const;

        inline T*         protect(const atomic_pointer_type& ptr);
        inline void       protect_raw(pointer_type ptr);
        inline void       unprotect(pointer_type ptr);
        inline void       unprotect(std::vector<pointer_type>& vec);
        inline guard_type guard(const atomic_pointer_type& ptr);
        inline guard_type guard(pointer_type ptr);

        inline void safe_delete(pointer_type ptr);
        inline void delete_raw(pointer_type ptr);
        inline bool is_safe(pointer_type ptr);

        void print(pointer_type ptr) const;
        void print() const;

      private:
        inline internal_type* get_iptr(pointer_type ptr) const;
        inline void           internal_delete(internal_type* iptr);
    };

    handle_type get_handle() { return handle_type(*this); }
    void        delete_raw(pointer_type ptr);

  private:
    destructor_type _destructor;
    std::mutex      _freelist_mutex;
    queue_type      _freelist;
};


template <class T, class D, template <class> class Q>
counting_manager<T, D, Q>::counting_manager(counting_manager&& other)
    : _destructor(std::move(other._destructor)), _freelist_mutex(), _freelist()
{
    std::lock_guard<std::mutex> guard(other._freelist_mutex);
    _freelist = std::move(other._freelist);
}

template <class T, class D, template <class> class Q>
counting_manager<T, D, Q>&
counting_manager<T, D, Q>::operator=(counting_manager&& other)
{
    if (&other == this) return *this;
    this->~counting_manager();
    new (this) counting_manager(std::move(other));
    return *this;
}

template <class T, class D, template <class> class Q>
counting_manager<T, D, Q>::~counting_manager()
{
    // no concurrency possible thus no mutex necessary
    // std::lock_guard<std::mutex> guard(_freelist_mutex);
    for (auto ptr : _freelist) free(ptr);
}

template <class T, class D, template <class> class Q>
void counting_manager<T, D, Q>::delete_raw(pointer_type ptr)
{
    auto iptr = static_cast<internal_type*>(mark::clear(ptr));

    iptr->internal_type::erase();

    std::lock_guard<std::mutex> guard(_freelist_mutex);
    _freelist.push_back(iptr);
}



// *** COUNTING_OBJECT *********************************************************
template <class T, class D, template <class> class Q>
template <class... Args>
counting_manager<T, D, Q>::_counted_object::_counted_object(Args&&... arg)
    : T(std::forward<Args>(arg)...), _counter(0)
{
}

template <class T, class D, template <class> class Q>
void counting_manager<T, D, Q>::_counted_object::erase()
{
    this->T::~T();
}

template <class T, class D, template <class> class Q>
template <class... Args>
void counting_manager<T, D, Q>::_counted_object::emplace(Args&&... arg)
{
    new (this) T(std::forward<Args>(arg)...);
}

template <class T, class D, template <class> class Q>
void counting_manager<T, D, Q>::_counted_object::increment_counter()
{
    _counter.fetch_add(1, memo::acquire);
}

template <class T, class D, template <class> class Q>
bool counting_manager<T, D, Q>::_counted_object::decrement_counter()
{
    auto temp = _counter.fetch_sub(1, memo::acq_rel);
    debug_tm::if_debug("Warning: in decrement_counter - "
                       "created a negative counter",
                       temp == 0);
    debug_tm::if_debug("Warning: in decrement counter - "
                       "weird counter",
                       (temp > 666) && (temp < del_flag + 1));

    return (temp == del_flag + 1);
}

template <class T, class D, template <class> class Q>
bool counting_manager<T, D, Q>::_counted_object::mark_deletion()
{
    auto temp = _counter.fetch_or(del_flag, memo::acq_rel);

    debug_tm::if_debug_critical(
        "Warning: in counting pointer trying to mark a marked pointer",
        temp & del_flag);

    return (temp == 0); // element was unused, and not marked before
}

template <class T, class D, template <class> class Q>
bool counting_manager<T, D, Q>::_counted_object::is_safe()
{
    return !_counter.load(memo::acquire);
}

template <class T, class D, template <class> class Q>
bool counting_manager<T, D, Q>::_counted_object::reset()
{
    auto temp = del_flag;
    return _counter.compare_exchange_strong(temp, 0, memo::acq_rel);
}

template <class T, class D, template <class> class Q>
void counting_manager<T, D, Q>::_counted_object::print() const
{
    auto temp = _counter.load(memo::acquire);
    out_tm::out() << ((temp & del_flag) ? "d" : "") //
                  << (temp & (~del_flag)) << std::endl;
}

// *** HANDLE STUFF ************************************************************
// ***** HANDLE MAIN FUNCTIONALITY *********************************************
template <class T, class D, template <class> class Q>
template <class... Args>
T* counting_manager<T, D, Q>::handle_type::create_pointer(Args&&... arg) const
{
    internal_type* temp = nullptr;
#ifndef NO_FREELIST
    { // area for the lock_guard
        std::lock_guard<std::mutex> guard(_parent._freelist_mutex);
        auto                        result = _parent._freelist.pop_front();
        if (result) { temp = result.value(); }
    }
    if (temp)
    {
        temp->emplace(std::forward<Args>(arg)...);
        return temp;
    }
#endif
    // temp = new internal_type(std::forward<Args>(arg)...);
    temp = static_cast<internal_type*>(malloc(sizeof(internal_type)));
    new (temp) internal_type(std::forward<Args>(arg)...);

    return temp;
}

template <class T, class D, template <class> class Q>
T* counting_manager<T, D, Q>::handle_type::protect(
    const atomic_pointer_type& ptr)
{
    ++n;
    auto temp = ptr.load(memo::acquire);
    if (!mark::clear(temp)) return nullptr; // nullptr cannot be protected
    get_iptr(temp)->increment_counter();
    auto temp2 = ptr.load(memo::acquire);
    while (temp != temp2)
    {
        auto itemp = get_iptr(temp);
        if (itemp->decrement_counter()) internal_delete(itemp);
        temp = temp2;
        if (!mark::clear(temp)) return nullptr;
        get_iptr(temp)->increment_counter();
        temp2 = ptr.load(memo::acquire);
    }
    return temp;
}

template <class T, class D, template <class> class Q>
void counting_manager<T, D, Q>::handle_type::protect_raw(pointer_type ptr)
{
    ++n;
    get_iptr(ptr)->increment_counter();
}

template <class T, class D, template <class> class Q>
void counting_manager<T, D, Q>::handle_type::unprotect(pointer_type ptr)
{
    --n;
    auto temp = get_iptr(ptr);
    if (temp->decrement_counter()) internal_delete(temp);
}

template <class T, class D, template <class> class Q>
void counting_manager<T, D, Q>::handle_type::unprotect(
    std::vector<pointer_type>& vec)
{
    n -= vec.size();
    for (auto ptr : vec)
    {
        auto temp = get_iptr(ptr);
        if (temp->decrement_counter()) internal_delete(temp);
    }
}

template <class T, class D, template <class> class Q>
typename counting_manager<T, D, Q>::handle_type::guard_type
counting_manager<T, D, Q>::handle_type::guard(const atomic_pointer_type& aptr)
{
    return make_rec_guard(*this, aptr);
}

template <class T, class D, template <class> class Q>
typename counting_manager<T, D, Q>::handle_type::guard_type
counting_manager<T, D, Q>::handle_type::guard(pointer_type ptr)
{
    return make_rec_guard(*this, ptr);
}

template <class T, class D, template <class> class Q>
void counting_manager<T, D, Q>::handle_type::safe_delete(pointer_type ptr)
{
    auto temp = get_iptr(ptr);
    if (temp->mark_deletion()) internal_delete(temp);
}

template <class T, class D, template <class> class Q>
void counting_manager<T, D, Q>::handle_type::delete_raw(pointer_type ptr)
{
    auto iptr = get_iptr(ptr);

    iptr->internal_type::erase();

    std::lock_guard<std::mutex> guard(_parent._freelist_mutex);
    _parent._freelist.push_back(iptr);
}

template <class T, class D, template <class> class Q>
bool counting_manager<T, D, Q>::handle_type::is_safe(pointer_type ptr)
{
    return get_iptr(ptr)->is_safe();
}




// ***** HANDLE HELPER FUNCTIONS ***********************************************
template <class T, class D, template <class> class Q>
void counting_manager<T, D, Q>::handle_type::print(pointer_type ptr) const
{
    get_iptr(ptr)->print();
}


template <class T, class D, template <class> class Q>
void counting_manager<T, D, Q>::handle_type::print() const
{
    std::lock_guard<std::mutex> guard(_parent._freelist_mutex);
    out_tm::out() << "* print in counting reclamation strategy "
                  << _parent._freelist.size() << " elements in the freelist *"
                  << std::endl;
}


template <class T, class D, template <class> class Q>
typename counting_manager<T, D, Q>::handle_type::internal_type*
counting_manager<T, D, Q>::handle_type::get_iptr(pointer_type ptr) const
{
    return static_cast<internal_type*>(mark::clear(ptr));
}

template <class T, class D, template <class> class Q>
void counting_manager<T, D, Q>::handle_type::internal_delete(internal_type* ptr)
{
    if (ptr->reset())
    {
        _parent._destructor.destroy(*this, static_cast<pointer_type>(ptr));
    }
}

} // namespace reclamation_tm
} // namespace utils_tm
