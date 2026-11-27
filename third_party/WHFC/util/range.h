#pragma once

#include <cstdint>

class IteratorChecks {
public:
    template<class Iterator>
    static bool iteratorInRange(Iterator x, Iterator _begin, Iterator _end) {
        return std::distance(x, _end) > 0 && std::distance(_begin, x) >= 0; //> and >= are different by intention
    }
};

template<class Range>
struct const_range {
    using const_iterator = typename Range::const_iterator;
    const_iterator __begin;
    const_iterator __end;
    inline const_iterator begin() const { return __begin; }
    inline const_iterator end() const { return __end; }
    const_range(const_iterator __begin, const_iterator __end) : __begin(__begin), __end(__end) {}
    const_range(const Range& r, std::size_t a, std::size_t b) : const_range(r.cbegin() + a, r.cbegin() + b) {}
    explicit const_range(const Range& r) : const_range(r.cbegin(), r.cend()) {}
};

template<class Range>
struct mutable_range {
    using iterator = typename Range::iterator;
    using reference = typename Range::reference;
    using value_type = typename Range::value_type;

    iterator __begin;
    iterator __end;
    inline iterator begin() const { return __begin; }
    inline iterator end() const { return __end; }
    inline bool empty() const { return begin() == end(); }
    inline std::size_t size() const { return static_cast<size_t>(std::distance(__begin, __end)); }
    inline reference front() {
        assert(!empty());
        return *begin();
    }
    inline reference back() {
        assert(!empty());
        return *(end() - 1);
    }
    inline reference at(iterator it) { return *it; }
    inline reference operator[](const std::size_t n) { return *(begin() + n); }
    inline reference at(const std::size_t n) { return *(begin() + n); }

    inline iterator advance_begin() { return __begin++; }
    inline iterator retreat_begin() { return --__begin; }
    inline iterator advance_end() { return __end++; }
    inline iterator retreat_end() { return --__end; }

    mutable_range(iterator __begin, iterator __end) : __begin(__begin), __end(__end) {}
    mutable_range(Range& r, const std::size_t a, const std::size_t b) : mutable_range(r.begin() + a, r.begin() + b) {}
    explicit mutable_range(Range& r) : mutable_range(r.begin(), r.end()) {}
};

template<typename Index_t>
struct mutable_index_range {
    using Type = mutable_index_range<Index_t>;
    Index_t __begin;
    Index_t __end;

    inline Index_t begin() const { return __begin; }
    inline Index_t end() const { return __end; }
    inline bool empty() const { return begin() == end(); }
    inline bool contains(const Index_t i) { return i < __end && i >= __begin; }
    inline std::size_t size() const { return static_cast<size_t>(__end - __begin); }

    inline bool isInvalid() const { return __end < __begin; }
    static Type Invalid() { return Type(Index_t(1), Index_t(0)); }
    void invalidate() { __begin = __end + Index_t(1); }
    void makeEmpty() { __begin = __end; }
    static Type createEmpty() { return Type(); }

    inline void advance_begin() { __begin++; }
    inline void retreat_begin() { __begin--; }
    inline void advance_end() { __end++; }
    inline void retreat_end() { __end--; }

    mutable_index_range() : __begin(Index_t(0)), __end(Index_t(0)) {}
    mutable_index_range(const Index_t _beg, const Index_t _end) : __begin(_beg), __end(_end) {}
};
