#pragma once

#include <utility>
#include <algorithm>

namespace Util {
    template<typename T>
    class InvertComparison {
    public:
        T value;

        explicit InvertComparison(const T& value) : value(value) {}

        InvertComparison& operator=(const T& value) {
            this->value = value;
            return *this;
        }

        bool operator<(const InvertComparison<T>& o) const { return value > o.value; }

        bool operator==(const InvertComparison<T>& o) const { return value == o.value; }

        bool operator>(const InvertComparison<T>& o) const { return value < o.value; }
    };


    template<typename T>
    std::pair<T, T> minmax(T a, T b) {
        return a < b ? std::make_pair(a, b) : std::make_pair(b, a);
    }

    template<typename T>
    void min_to(T& a, T& b) {
        a = std::min(a, b);
    }
} // namespace Util
