#pragma once

#include <cmath>
#include <numeric>
#include <vector>

class Math {
public:
    template<typename T>
    static T percentile(double fraction, std::vector<T>& elements) {
        long ind = std::lround(elements.size() * fraction);
        if (ind >= elements.size()) {
            ind = elements.size() - 1;
        }
        if (ind < 0) {
            ind = 0;
        }
        return elements[ind];
    }

    template<typename T>
    static double avg(std::vector<T>& elements) {
        T sum = std::accumulate(elements.begin(), elements.end(), T());
        return static_cast<double>(sum) / static_cast<double>(elements.size());
    }

    template<typename T>
    static T absdiff(const T a, const T b) {
        return a < b ? b - a : a - b;
    }
};
