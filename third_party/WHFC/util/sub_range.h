#pragma once

#include <vector>


template<typename RANGE>
class sub_range {

public:
    using Range = RANGE;
    using Type = sub_range<Range>;

public:
    class Iterator {
    public:
        Iterator(const Range* const range, const size_t i) : range(range), i(i) {}
        inline bool operator!=(const Iterator& other) const noexcept { return i != other.i; }
        inline auto operator*() const noexcept { return (*range)[i]; }
        inline Iterator& operator++() noexcept {
            ++i;
            return *this;
        }
        inline Iterator& operator+=(const size_t n) noexcept {
            i += n;
            return *this;
        }
        inline Iterator operator+(const size_t n) const noexcept { return Iterator(range, i + n); }
        inline auto operator[](const size_t n) const noexcept { return (*range)[i + n]; }

    private:
        const Range* range;
        size_t i;
    };

    sub_range() : range(nullptr), beginIndex(0), endIndex(0) {}

    sub_range(const Range& range, const size_t beginIndex = 0, const size_t endIndex = 0) : range(&range), beginIndex(beginIndex), endIndex(endIndex) {}

    template<typename INDEX_TYPE_A, typename INDEX_TYPE_B>
    sub_range(const Range& range, const std::vector<INDEX_TYPE_A>& indices, const INDEX_TYPE_B index) :
        range(&range), beginIndex(indices[index]), endIndex(indices[index + 1]) {}

    sub_range(const Range&&, const size_t = 0, const size_t = 0) = delete;

    template<typename INDEX_TYPE_A, typename INDEX_TYPE_B>
    sub_range(const Range&& range, const std::vector<INDEX_TYPE_A>&, const INDEX_TYPE_B) = delete;

    inline Iterator begin() const noexcept { return Iterator(range, beginIndex); }

    inline Iterator end() const noexcept { return Iterator(range, endIndex); }

    inline bool empty() const noexcept { return endIndex <= beginIndex; }

    inline size_t size() const noexcept { return endIndex - beginIndex; }

    inline auto operator[](const size_t i) const noexcept {
        assert(i < size());
        return (*range)[beginIndex + i];
    }

    inline auto front() const noexcept {
        assert(!empty());
        return (*range)[beginIndex];
    }

    inline auto back() const noexcept {
        assert(!empty());
        return (*range)[endIndex - 1];
    }

private:
    const Range* range;
    size_t beginIndex;
    size_t endIndex;
};
