
#pragma once

#include <algorithm>
#include <cstddef>
#include <optional>

namespace utils_tm
{

// This structure is owned by one thread, and is meant to pass inputs
// to that thread
template <class T>
class circular_buffer
{
  private:
    using this_type = circular_buffer<T>;

    size_t _start;
    size_t _end;
    size_t _bitmask;
    T*     _buffer;

  public:
    using value_type = T;

    circular_buffer(size_t capacity = 128);
    circular_buffer(const circular_buffer&)            = delete;
    circular_buffer& operator=(const circular_buffer&) = delete;
    circular_buffer(circular_buffer&& other);
    circular_buffer& operator=(circular_buffer&& rhs);
    ~circular_buffer();

    inline void push_back(const T& e);
    inline void push_front(const T& e);
    template <class... Args>
    inline void emplace_back(Args&&... args);
    template <class... Args>
    inline void emplace_front(Args&&... args);

    inline std::optional<T> pop_back();
    inline std::optional<T> pop_front();

    size_t size() const;
    size_t capacity() const;

    template <bool is_const>
    class iterator_base
    {
      private:
        using this_type = iterator_base<is_const>;
        friend circular_buffer;

        const circular_buffer* _circular;
        size_t                 _off;

      public:
        using difference_type = std::ptrdiff_t;
        using value_type =
            typename std::conditional<is_const, const T, T>::type;
        using reference         = value_type&;
        using pointer           = value_type*;
        using iterator_category = std::random_access_iterator_tag;

        iterator_base(const circular_buffer* buffer, size_t offset)
            : _circular(buffer), _off(offset)
        {
        }
        iterator_base(const iterator_base& other)            = default;
        iterator_base& operator=(const iterator_base& other) = default;
        ~iterator_base()                                     = default;

        inline reference operator*() const;
        inline pointer   operator->() const;
        inline reference operator[](difference_type d) const;

        inline iterator_base& operator+=(difference_type rhs);
        inline iterator_base& operator-=(difference_type rhs);
        inline iterator_base& operator++();
        inline iterator_base& operator--();
        inline iterator_base  operator+(difference_type rhs) const;
        inline iterator_base  operator-(difference_type rhs) const;

        inline bool operator==(const iterator_base& other) const;
        inline bool operator!=(const iterator_base& other) const;
        inline bool operator<(const iterator_base& other) const;
        inline bool operator>(const iterator_base& other) const;
        inline bool operator<=(const iterator_base& other) const;
        inline bool operator>=(const iterator_base& other) const;
    };

    using iterator       = iterator_base<false>;
    using const_iterator = iterator_base<true>;

    inline iterator       begin() { return iterator(this, _start); }
    inline const_iterator begin() const { return const_iterator(this, _start); }
    inline const_iterator cbegin() const
    {
        return const_iterator(this, _start);
    }
    inline iterator       end() { return iterator(this, _end); }
    inline const_iterator end() const { return const_iterator(this, _end); }
    inline const_iterator cend() const { return const_iterator(this, _end); }

  private:
    inline size_t mod(size_t i) const { return i & _bitmask; }
    inline size_t inc(size_t i, size_t diff = 1) const { return i + diff; }
    inline size_t dec(size_t i, size_t diff = 1) const { return i - diff; }

    inline size_t compare_offsets(size_t lhs, size_t rhs) const;

    void grow();
    void cleanup();
};




// CTORS AND DTOR !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
template <class T>
circular_buffer<T>::circular_buffer(size_t capacity) : _start(0), _end(0)
{
    size_t tcap = 1;
    while (tcap < capacity) tcap <<= 1;

    _buffer  = static_cast<T*>(malloc(sizeof(T) * tcap));
    _bitmask = tcap - 1;
}

template <class T>
circular_buffer<T>::circular_buffer(circular_buffer&& other)
    : _bitmask(other._bitmask), _buffer(other._buffer)
{
    other._buffer = nullptr;
}

template <class T>
circular_buffer<T>& circular_buffer<T>::operator=(circular_buffer&& other)
{
    if (&other == this) return *this;

    this->~this_type();
    new (this) circular_buffer(std::move(other));
    return *this;
}

template <class T>
circular_buffer<T>::~circular_buffer()
{
    cleanup();
    free(_buffer);
}




// MAIN FUNCTIONALITY !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
template <class T>
void circular_buffer<T>::push_back(const T& e)
{

    if (_end > _start + _bitmask) grow();

    _buffer[mod(_end)] = e;
    _end               = inc(_end);
}

template <class T>
void circular_buffer<T>::push_front(const T& e)
{
    if (_end > _start + _bitmask) grow();

    _start               = dec(_start);
    _buffer[mod(_start)] = e;
}

template <class T>
template <class... Args>
void circular_buffer<T>::emplace_back(Args&&... args)
{

    if (_end > _start + _bitmask) grow();

    new (&_buffer[mod(_end)]) T(std::forward<Args>(args)...);
    _end = inc(_end);
}

template <class T>
template <class... Args>
void circular_buffer<T>::emplace_front(Args&&... args)
{
    if (_end > _start + _bitmask) grow();

    _start = dec(_start);
    new (&_buffer[mod(_start)]) T(std::forward<Args>(args)...);
}

template <class T>
std::optional<T> circular_buffer<T>::pop_back()
{
    if (_start == _end) { return {}; }

    _end        = dec(_end);
    auto result = std::make_optional(std::move(_buffer[mod(_end)]));
    _buffer[mod(_end)].~T();
    return result;
}

template <class T>
std::optional<T> circular_buffer<T>::pop_front()
{
    if (_start == _end) { return {}; }

    auto result = std::make_optional(std::move(_buffer[mod(_start)]));
    _buffer[mod(_start)].~T();
    _start = inc(_start);
    return result;
}


// SIZE AND CAPACITY !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
template <class T>
size_t circular_buffer<T>::size() const
{
    return _end - _start;
}

template <class T>
size_t circular_buffer<T>::capacity() const
{
    return _bitmask + 1;
}


// HELPER FUNCTIONS !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
template <class T>
size_t circular_buffer<T>::compare_offsets(size_t lhs, size_t rhs) const
{
    if (lhs == rhs) return 0;
    return (lhs < rhs) ? -1 : 1;
}

template <class T>
void circular_buffer<T>::grow()
{
    auto nbitmask = (_bitmask << 1) + 1;
    auto nbuffer  = static_cast<T*>(malloc(sizeof(T) * (nbitmask + 1)));

    size_t i = 0;
    for (iterator it = begin(); it != end(); ++it)
    {
        nbuffer[i++] = std::move(*it);
        it->~T();
    }
    // std::fill(nbuffer + i, nbuffer + nbitmask + 1, T());

    free(_buffer);
    _start   = 0;
    _end     = i;
    _bitmask = nbitmask;
    _buffer  = nbuffer;
}

template <class T>
void circular_buffer<T>::cleanup()
{
    for (iterator it = begin(); it != end(); ++it) { it->~T(); }
    _start = _end = 0;
}


// ITERATOR STUFF !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
// template <class T> template <bool b>
// typename circular_buffer<T>::template iterator_base<b>&
// circular_buffer<T>::iterator_base<b>::operator=(const iterator_base& rhs)
// {
//     if (this == &rhs) return *this;

//     this->~iterator_base();
//     new (this) iterator_base(rhs);
//     return *this;
// }

template <class T>
template <bool b>
typename circular_buffer<T>::template iterator_base<b>::reference
circular_buffer<T>::iterator_base<b>::operator*() const
{
    return _circular->_buffer[_circular->mod(_off)];
}

template <class T>
template <bool b>
typename circular_buffer<T>::template iterator_base<b>::pointer
circular_buffer<T>::iterator_base<b>::operator->() const
{
    return _circular->_buffer + _circular->mod(_off);
}

template <class T>
template <bool b>
typename circular_buffer<T>::template iterator_base<b>::reference
circular_buffer<T>::iterator_base<b>::operator[](difference_type d) const
{
    return _circular->_buffer[_circular->mod(_circular->inc(_off, d))];
}


template <class T>
template <bool b>
typename circular_buffer<T>::template iterator_base<b>&
circular_buffer<T>::iterator_base<b>::operator+=(difference_type rhs)
{
    _off = _circular->inc(_off, rhs);
}

template <class T>
template <bool b>
typename circular_buffer<T>::template iterator_base<b>&
circular_buffer<T>::iterator_base<b>::operator-=(difference_type rhs)
{
    _off = _circular->dec(_off, rhs);
}

template <class T>
template <bool b>
typename circular_buffer<T>::template iterator_base<b>&
circular_buffer<T>::iterator_base<b>::operator++()
{
    _off = _circular->inc(_off);
    return *this;
}

template <class T>
template <bool b>
typename circular_buffer<T>::template iterator_base<b>&
circular_buffer<T>::iterator_base<b>::operator--()
{
    _off = _circular->dec(_off);
    return *this;
}

template <class T>
template <bool b>
typename circular_buffer<T>::template iterator_base<b>
circular_buffer<T>::iterator_base<b>::operator+(difference_type rhs) const
{
    return iterator_base(_circular, _circular->inc(rhs));
}

template <class T>
template <bool b>
typename circular_buffer<T>::template iterator_base<b>
circular_buffer<T>::iterator_base<b>::operator-(difference_type rhs) const
{
    return iterator_base(_circular, _circular->dec(rhs));
}

template <class T>
template <bool b>
bool circular_buffer<T>::iterator_base<b>::operator==(
    const iterator_base& other) const
{
    return (_circular == other._circular) && (_off == other._off);
}

template <class T>
template <bool b>
bool circular_buffer<T>::iterator_base<b>::operator!=(
    const iterator_base& other) const
{
    return (_circular != other._circular) || (_off != other._off);
}

template <class T>
template <bool b>
bool circular_buffer<T>::iterator_base<b>::operator<(
    const iterator_base& other) const
{
    return _circular->compare_offsets(_off, other._off) < 0;
}

template <class T>
template <bool b>
bool circular_buffer<T>::iterator_base<b>::operator>(
    const iterator_base& other) const
{
    return _circular->compare_offsets(_off, other._off) > 0;
}

template <class T>
template <bool b>
bool circular_buffer<T>::iterator_base<b>::operator<=(
    const iterator_base& other) const
{
    return _circular->compare_offsets(_off, other._off) <= 0;
}

template <class T>
template <bool b>
bool circular_buffer<T>::iterator_base<b>::operator>=(
    const iterator_base& other) const
{
    return _circular->compare_offsets(_off, other._off) >= 0;
}

} // namespace utils_tm
