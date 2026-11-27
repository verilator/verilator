#pragma once

#include <vector>

template<typename RANGE, typename ELEMENT>
class concatenated_range {

public:
    using Range = RANGE;
    using Element = ELEMENT;
    using Type = concatenated_range<Range, Element>;

public:
    class Iterator {
    public:
        Iterator(const concatenated_range* const concatenatedRange, const size_t i) : concatenatedRange(concatenatedRange), i(i) {}
        inline bool operator!=(const Iterator& other) const noexcept { return i != other.i; }
        inline Element operator*() const noexcept { return (*concatenatedRange)[i]; }
        inline Iterator& operator++() noexcept {
            ++i;
            return *this;
        }
        inline Iterator& operator+=(const size_t n) noexcept {
            i += n;
            return *this;
        }
        inline Iterator operator+(const size_t n) const noexcept { return Iterator(concatenatedRange, i + n); }
        inline Element operator[](const size_t n) const noexcept { return (*concatenatedRange)[i + n]; }

    private:
        const concatenated_range* concatenatedRange;
        size_t i;
    };

    concatenated_range(const Range& firstRange, const Range& secondRange) : firstRange(firstRange), secondRange(secondRange) {}

    inline Iterator begin() const noexcept { return Iterator(this, 0); }

    inline Iterator end() const noexcept { return Iterator(this, size()); }

    inline bool empty() const noexcept { return firstRange.empty() && secondRange.empty(); }

    inline size_t size() const noexcept { return firstRange.size() + secondRange.size(); }

    inline Element operator[](const size_t i) const noexcept {
        assert(i < size());
        if (i < firstRange.size()) {
            return firstRange[i];
        } else {
            return secondRange[i - firstRange.size()];
        }
    }
    inline Element front() const noexcept {
        assert(!empty());
        return operator[](0);
    }

    inline Element back() const noexcept {
        assert(!empty());
        return operator[](size() - 1);
    }

private:
    Range firstRange;
    Range secondRange;
};
