#pragma once

#include <algorithm>
#include <vector>

namespace whfc {
    namespace util {
        /*
         * Removes all elements which fulfill p and 1) copies to new vector 2) removes them in-place
         */

        template<typename Container, typename Predicate>
        auto remove_if_copy(const Container& C, const Predicate& p) {
            std::vector<typename Container::value_type> out;
            for (const auto& x : C)
                if (!p(x))
                    out.push_back(x);
            return out;
        }

        template<typename Container, typename Predicate>
        void remove_if_inplace(Container& C, const Predicate& p) {
            auto new_end = std::remove_if(C.begin(), C.end(), p);
            C.erase(new_end, C.end());
        }

        template<typename Container, typename Predicate>
        void move_to_end_if(Container& C, size_t& size, const Predicate& p) {
            for (size_t i = 0; i < size; ++i) {
                if (p(C[i])) {
                    std::swap(C[i--], C[--size]);
                }
            }
        }

        template<typename Container, typename Predicate>
        void move_to_front_if(Container& C, size_t& front, size_t size, const Predicate& p) {
            for (; front < size;) {
                assert(size > 0);
                if (p(C[--size])) {
                    std::swap(C[front++], C[size++]);
                }
            }
        }
    } // namespace util
} // namespace whfc
