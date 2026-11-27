#pragma once

#include "../mark_pointer.hpp"
#include <atomic>

namespace utils_tm
{
template <class V, template <class> class R> class protected_singly_linked_list;

namespace reclamation_tm
{

template <class GuardType>
GuardType
add_guard(const GuardType& guard, typename GuardType::pointer_type ptr);

template <class GuardType>
GuardType add_guard(const GuardType&                               guard,
                    const typename GuardType::atomic_pointer_type& aptr);

template <class T, class ReclamationType> class reclamation_guard
{
  private:
    using this_type        = reclamation_guard<T, ReclamationType>;
    using reclamation_type = ReclamationType;

  public:
    using pointer_type        = typename ReclamationType::pointer_type;
    using atomic_pointer_type = typename ReclamationType::atomic_pointer_type;

    inline reclamation_guard(reclamation_type& rec);
    inline reclamation_guard(reclamation_type&          rec,
                             const atomic_pointer_type& aptr);
    inline reclamation_guard(reclamation_type& rec, pointer_type ptr);

    inline reclamation_guard(const reclamation_guard&);
    inline reclamation_guard& operator=(const reclamation_guard&);

    inline reclamation_guard(reclamation_guard&& source);
    inline reclamation_guard& operator=(reclamation_guard&& source);
    inline ~reclamation_guard();

    inline    operator T*() const { return _ptr; }
    inline    operator bool() const { return _ptr != nullptr; }
    inline T* operator->() const { return _ptr; }
    inline T& operator*() const { return *_ptr; }

    inline T*   release();
    inline bool unmark();

    friend this_type
    add_guard<this_type>(const this_type& guard, pointer_type ptr);

    friend this_type add_guard<this_type>(const this_type&           guard,
                                          const atomic_pointer_type& ptr);

  private:
    reclamation_type& _rec_handle;
    T*                _ptr;

    // template <class V, template <class> class R, bool c>
    // friend class protected_singly_linked_list<V,R>::template
    // iterator_base<c>::this_type;
};

template <class T, class R>
reclamation_guard<T, R>::reclamation_guard(reclamation_type& rec)
    : _rec_handle(rec), _ptr(nullptr)
{
}


template <class T, class R>
reclamation_guard<T, R>::reclamation_guard(reclamation_type&          rec,
                                           const atomic_pointer_type& aptr)
    : _rec_handle(rec), _ptr(rec.protect(aptr))
{
}


template <class T, class R>
reclamation_guard<T, R>::reclamation_guard(reclamation_type& rec,
                                           pointer_type      ptr)
    : _rec_handle(rec), _ptr(ptr)
{
    _rec_handle.protect_raw(ptr);
}

template <class T, class R>
reclamation_guard<T, R>::reclamation_guard(const reclamation_guard& source)
    : _rec_handle(source._rec_handle), _ptr(source._ptr)
{
    _rec_handle.protect_raw(_ptr);
}

template <class T, class R>
reclamation_guard<T, R>&
reclamation_guard<T, R>::operator=(const reclamation_guard& source)
{
    if (&source == this) return *this;
    this->~reclamation_guard();
    new (this) reclamation_guard(source);
    return *this;
}


template <class T, class R>
reclamation_guard<T, R>::reclamation_guard(reclamation_guard&& source)
    : _rec_handle(source._rec_handle), _ptr(source._ptr)
{
    source._ptr = nullptr;
}

template <class T, class R>
reclamation_guard<T, R>&
reclamation_guard<T, R>::operator=(reclamation_guard&& source)
{
    if (&source == this) return *this;
    this->~reclamation_guard();
    new (this) reclamation_guard(std::move(source));
    return *this;
}

template <class T, class R> reclamation_guard<T, R>::~reclamation_guard()
{
    if (mark::clear(_ptr)) _rec_handle.unprotect(_ptr);
}

template <class T, class R> T* reclamation_guard<T, R>::release()
{
    auto temp = _ptr;
    if (mark::clear(_ptr)) _rec_handle.unprotect(_ptr);
    _ptr = nullptr;
    return temp;
}

template <class T, class R> bool reclamation_guard<T, R>::unmark()
{
    bool was_marked = (_ptr != mark::clear(_ptr));
    _ptr            = mark::clear(_ptr);
    return was_marked;
}






template <class T, class ReclamationType>
reclamation_guard<T, ReclamationType>
make_rec_guard(ReclamationType& rec, T* ptr)
{
    return reclamation_guard<T, ReclamationType>(rec, ptr);
}

template <class T, class ReclamationType>
reclamation_guard<T, ReclamationType>
make_rec_guard(ReclamationType& rec, const std::atomic<T*>& aptr)
{
    return reclamation_guard<T, ReclamationType>(rec, aptr);
}

template <class GuardType>
GuardType
add_guard(const GuardType& guard, typename GuardType::pointer_type ptr)
{
    return GuardType(guard._rec_handle, ptr);
}

template <class GuardType>
GuardType add_guard(const GuardType&                               guard,
                    const typename GuardType::atomic_pointer_type& aptr)
{
    return GuardType(guard._rec_handle, aptr);
}

} // namespace reclamation_tm
} // namespace utils_tm
