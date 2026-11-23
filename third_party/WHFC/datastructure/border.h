#pragma once

#include "../definitions.h"
#include "../util/filter.h"
#include "bitvector.h"

#include "../util/concatenated_range.h"
#include "../util/range.h"
#include "../util/sub_range.h"

namespace whfc {

    template<typename T, bool track_elements>
    class PersistentSet {
    private:
        bool persistent_mode = true;
        size_t persistent_begin = 0, persistent_end = 0, non_persistent_begin = 0;
        BitVector was_added;
        std::vector<T> elements;

        sub_range<std::vector<T>> persistent_entries() const { return sub_range(elements, persistent_begin, persistent_end); }

        sub_range<std::vector<T>> non_persistent_entries() const { return sub_range(elements, non_persistent_begin, elements.size()); }

    public:
        explicit PersistentSet(const size_t nT) { was_added.reserve(nT); }

        bool wasAdded(const T x) const { return was_added[x]; }

        void add(const T& x) {
            assert(!wasAdded(x));
            was_added.set(x);
            if (track_elements || !persistent_mode)
                elements.push_back(x);
        }

        // delete non persistent entries, even those removed from the list
        // and recover the persistent entries, even those removed from the list
        void recover() {
            while (elements.size() > persistent_end) {
                was_added.reset(elements.back());
                elements.pop_back();
            }
            non_persistent_begin = persistent_end;
            persistent_begin = 0;
        }

        void lockInPersistentEntries() {
            persistent_mode = false;
            persistent_end = elements.size();
            non_persistent_begin = persistent_end;
        }

        template<typename Predicate>
        void cleanUp(Predicate p) {
            if (persistent_mode) {
                util::remove_if_inplace(elements, p);
            } else {
                util::move_to_front_if(elements, persistent_begin, persistent_end, p);
                util::move_to_front_if(elements, non_persistent_begin, elements.size(), p);
            }
        }

        void reset(size_t newN) {
            was_added.resize(newN);
            was_added.reset(0, newN);
            elements.clear();
            persistent_begin = 0;
            persistent_end = 0;
            non_persistent_begin = 0;
            persistent_mode = true;
        }

        bool empty() const { return persistent_begin == persistent_end && non_persistent_begin == elements.size(); }

        auto entries() const { return concatenated_range<sub_range<std::vector<T>>, T>(persistent_entries(), non_persistent_entries()); }

        std::vector<T> copy() const {
            std::vector<T> c;
            for (const T& x : entries())
                c.push_back(x);
            return c;
        }
    };

    template<typename T, bool trackElements>
    class Borders {
    public:
        explicit Borders(size_t nT) : source_side(nT), target_side(nT) {}

        PersistentSet<T, trackElements> source_side, target_side;

        void reset(const size_t newN) {
            source_side.reset(newN);
            target_side.reset(newN);
        }

        void enterMostBalancedCutMode() {
            source_side.lockInPersistentEntries();
            target_side.lockInPersistentEntries();
        }

        void resetForMostBalancedCut() {
            source_side.recover();
            target_side.recover();
        }
    };

    // track hyperedges only for assertions in debug mode
#ifndef NDEBUG
    using HyperedgeCuts = Borders<Hyperedge, true>;
#else
    using HyperedgeCuts = Borders<Hyperedge, false>;
#endif

} // namespace whfc
