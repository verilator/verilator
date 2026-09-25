// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2024-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
///
/// \file
/// \brief Verilated functional-coverage collection runtime implementation
///
/// Linked when covergroups are present.  The coverage-database registration
/// is compiled only with "verilator --coverage".
///
//=============================================================================

#include "verilatedos.h"

#include "verilated_covergroup.h"

#include "verilated.h"

#include <map>
#include <tuple>

// This file is compiled whenever covergroups are used, with or without
// "verilator --coverage" (see V3Global::verilatedCppFiles).  Bin counts are
// owned by the covergroup instance nodes in the VerilatedContext's registry, so
// sampling, bin naming, and coverage queries such as get_inst_coverage() all
// work with no coverage database present.  VL_COVER_INSERT does not copy a
// count; it hands the database the address of a counter the registry owns and
// reads it at write time.  Only that publication step needs the database, so
// only the registerBins() bodies -- and this include -- are gated on
// VM_COVERAGE.
#if VM_COVERAGE
#include "verilated_cov.h"
#endif

struct VlCoverpoint::ValueData final {
    // CONSTANTS
    static constexpr uint32_t QUERY_WORK_LIMIT = 1U << 20;  // Maximum graph steps per query
    static constexpr uint32_t QUERY_DEPTH_LIMIT = 1024;  // Max width for recursive queries

    // TYPES
    // A value's words, held inline up to INLINE_WORDS so that common widths do not allocate
    class Value final {
        static constexpr uint32_t INLINE_WORDS = 2;  // Words stored without an allocation
        uint32_t m_size = 0;  // Number of words
        EData m_inline[INLINE_WORDS] = {0, 0};  // Words of a value up to INLINE_WORDS wide
        std::vector<EData> m_heap;  // Words of a wider value

    public:
        Value() = default;
        Value(const EData* beginp, const EData* endp)
            : m_size{static_cast<uint32_t>(endp - beginp)} {
            if (m_size <= INLINE_WORDS) {
                std::copy(beginp, endp, m_inline);
            } else {
                m_heap.assign(beginp, endp);
            }
        }
        EData* data() { return m_size <= INLINE_WORDS ? m_inline : m_heap.data(); }
        const EData* data() const { return m_size <= INLINE_WORDS ? m_inline : m_heap.data(); }
        bool empty() const { return !m_size; }
        void clear() {
            m_size = 0;
            m_heap.clear();
        }
        EData& operator[](uint32_t i) { return data()[i]; }
        const EData& operator[](uint32_t i) const { return data()[i]; }
        EData& back() { return data()[m_size - 1]; }
        EData* begin() { return data(); }
        EData* end() { return data() + m_size; }
        const EData* begin() const { return data(); }
        const EData* end() const { return data() + m_size; }
        bool operator==(const Value& other) const {
            return std::equal(begin(), end(), other.begin(), other.end());
        }
    };
    struct Range final {
        Value m_lo;  // Inclusive lower bound and fixed-bit values for wildcard patterns
        Value m_hi;  // Inclusive upper bound in coverpoint value order
        Value m_mask;  // Significant wildcard bits; empty for an ordinary interval
    };
    struct Values final {
        std::vector<Range> m_ranges;  // Source intervals and patterns associated with this bin
        bool m_transition = false;  // State-value exclusions must not alter this transition bin
    };
    // Outcome of searching a range for a value outside every exclusion
    enum class Search : uint8_t { EMPTY, VALUE, WORK_LIMIT, DEPTH_LIMIT };
    class Query;

    // MEMBERS
    const uint32_t m_bits;  // Width of the coverpoint's effective integral type
    const uint32_t m_words;  // EData words required to store one value
    const bool m_isSigned;  // Use signed ordering when comparing values
    bool m_frozen = false;  // Construction-time value metadata has been finalized
    std::vector<Values> m_values;  // Values by declared bin, released once crosses are built
    std::vector<Range> m_exclusions;  // Normalized state ignore/illegal ranges and patterns
    uint32_t m_regularExclusions = 0;  // Length of the merged interval prefix in m_exclusions
    std::vector<uint32_t> m_reported;  // Declared bins that have values, in declaration order

    ValueData(uint32_t bits, bool isSigned, uint32_t bins)
        : m_bits{bits}
        , m_words{VL_WORDS_I(bits)}
        , m_isSigned{isSigned}
        , m_values{bins} {
        assert(m_bits);
    }
    static WDataInP view(const Value& value) { return WDataInP::external(value.data()); }
    Value read(WDataInP valuep) const {
        Value result(valuep.datap(), valuep.datap() + m_words);
        return result;
    }
    // Operands have already been cleaned to m_bits.
    bool less(WDataInP lhs, WDataInP rhs) const {
        if (m_isSigned) {
            const EData leftSign = VL_SIGN_E(m_bits, lhs[m_words - 1]);
            const EData rightSign = VL_SIGN_E(m_bits, rhs[m_words - 1]);
            if (leftSign != rightSign) return leftSign;
        }
        for (uint32_t i = m_words; i > 0; --i) {
            const EData left = lhs[i - 1];
            const EData right = rhs[i - 1];
            if (left != right) return left < right;
        }
        return false;
    }
    bool less(const Value& lhs, const Value& rhs) const { return less(view(lhs), view(rhs)); }
    bool less(WDataInP lhs, const Value& rhs) const { return less(lhs, view(rhs)); }
    bool less(const Value& lhs, WDataInP rhs) const { return less(view(lhs), rhs); }
    void increment(Value& value) const {
        for (EData& word : value) {
            if (++word) break;
        }
        value.back() &= VL_MASK_E(m_bits);
    }
    // Add in m_bits-wide modular arithmetic, which orders correctly within a run of bins
    void add(Value& value, const Value& addend) const {
        VL_ADD_W(static_cast<int>(m_words), WDataOutP::external(value.data()), view(value),
                 view(addend));
        value.back() &= VL_MASK_E(m_bits);
    }
    bool contains(const Range& range, WDataInP value) const {
        if (less(value, range.m_lo) || less(range.m_hi, value)) return false;
        if (!range.m_mask.empty()) {
            EData mismatch = 0;
            for (uint32_t i = 0; i < m_words; ++i) {
                mismatch |= (value[i] & range.m_mask[i]) ^ (range.m_lo[i] & range.m_mask[i]);
            }
            return mismatch == 0;
        }
        return true;
    }
    const Range* interval(const std::vector<Range>& ranges, uint32_t count, WDataInP value) const {
        auto it = std::upper_bound(
            ranges.begin(), ranges.begin() + count, value,
            [&](WDataInP candidate, const Range& range) { return less(candidate, range.m_lo); });
        if (it == ranges.begin()) return nullptr;
        --it;
        return contains(*it, value) ? &*it : nullptr;
    }
    uint32_t normalize(std::vector<Range>& ranges) const {
        // Most bins have one ordered range, which needs no sorting or merging.
        if (ranges.size() == 1 && !less(ranges[0].m_hi, ranges[0].m_lo)) {
            return ranges[0].m_mask.empty() ? 1 : 0;
        }
        const auto middle = std::stable_partition(
            ranges.begin(), ranges.end(), [](const Range& range) { return range.m_mask.empty(); });
        std::sort(ranges.begin(), middle,
                  [&](const Range& lhs, const Range& rhs) { return less(lhs.m_lo, rhs.m_lo); });
        std::vector<Range> merged;
        for (auto it = ranges.begin(); it != middle; ++it) {
            if (less(it->m_hi, it->m_lo)) continue;
            if (!merged.empty()) {
                Value adjacent = merged.back().m_hi;
                increment(adjacent);
                if (!less(merged.back().m_hi, it->m_lo) || adjacent == it->m_lo) {
                    if (less(merged.back().m_hi, it->m_hi)) merged.back().m_hi = it->m_hi;
                    continue;
                }
            }
            merged.push_back(std::move(*it));
        }
        const uint32_t count = static_cast<uint32_t>(merged.size());
        merged.insert(merged.end(), std::make_move_iterator(middle),
                      std::make_move_iterator(ranges.end()));
        ranges = std::move(merged);
        return count;
    }
    bool excluded(WDataInP value) const {
        return interval(m_exclusions, m_regularExclusions, value)
               || std::any_of(m_exclusions.begin() + m_regularExclusions, m_exclusions.end(),
                              [&](const Range& range) { return contains(range, value); });
    }
    // Value bits, unlike wildcard mask bits, flip the sign bit for signed ordering.
    bool orderBit(const Value& value, uint32_t bit) const {
        return (VL_BITISSET_W(value, bit) != 0) ^ (m_isSigned && bit == m_bits - 1);
    }
    void setOrderBit(Value& value, uint32_t bit, bool ordered) const {
        VL_ASSIGNBIT_II(bit, value[VL_BITWORD_E(bit)],
                        ordered ^ (m_isSigned && bit == m_bits - 1));
    }
    bool patternAtLeast(const Range& range, const Value& lower, Value& result) const {
        if (range.m_mask.empty()) {
            result = lower;
            return true;
        }
        result = range.m_lo;
        int32_t carry = -1;
        bool greater = false;
        for (uint32_t pos = m_bits; pos > 0;) {
            const uint32_t bit = --pos;
            const bool fixed = VL_BITISSET_W(range.m_mask, bit);
            const bool low = orderBit(lower, bit);
            const bool chosen = fixed ? orderBit(range.m_lo, bit) : greater ? false : low;
            if (!greater && fixed && !chosen && low) {
                if (carry < 0) return false;
                setOrderBit(result, static_cast<uint32_t>(carry), true);
                for (uint32_t tail = 0; tail < static_cast<uint32_t>(carry); ++tail) {
                    const uint32_t w = VL_BITWORD_E(tail);
                    VL_ASSIGNBIT_II(tail, result[w],
                                    VL_BITISSET_E(range.m_lo[w] & range.m_mask[w], tail) != 0);
                }
                return true;
            }
            if (!greater && !fixed && !chosen) carry = static_cast<int32_t>(bit);
            if (chosen != low) greater |= chosen && !low;
            setOrderBit(result, bit, chosen);
        }
        return true;
    }
    bool clip(Range& range, const Value& lo, const Value& hi) const {
        const Value lower = less(lo, range.m_lo) ? range.m_lo : lo;
        const Value upper = less(range.m_hi, hi) ? range.m_hi : hi;
        Value first;
        if (less(upper, lower) || !patternAtLeast(range, lower, first) || less(upper, first)) {
            return false;
        }
        range.m_lo = std::move(first);
        range.m_hi = upper;
        return true;
    }
    bool pattern(WDataInP valuep, WDataInP maskp, WDataInP lop, WDataInP hip,
                 Range& result) const {
        result = {read(valuep), read(valuep), read(maskp)};
        for (uint32_t i = 0; i < m_words; ++i) {
            result.m_lo[i] &= result.m_mask[i];
            result.m_hi[i] |= ~result.m_mask[i];
        }
        result.m_hi.back() &= VL_MASK_E(m_bits);
        if (m_isSigned && !VL_SIGN_E(m_bits, result.m_mask.back())) {
            VL_ASSIGNBIT_IO(m_bits - 1, result.m_lo.back());
            VL_ASSIGNBIT_II(m_bits - 1, result.m_hi.back(), 0);
        }
        bool fixed = false;
        bool contiguous = true;
        for (uint32_t bit = 0; bit < m_bits; ++bit) {
            if (VL_BITISSET_W(result.m_mask, bit)) {
                fixed = true;
            } else if (fixed) {
                contiguous = false;
            }
        }
        if (contiguous) result.m_mask.clear();
        return clip(result, read(lop), read(hip));
    }
    Value lastValue(const Range& range) const {
        Range reversed = range;
        Value lower = range.m_hi;
        for (uint32_t word = 0; word < m_words; ++word) {
            reversed.m_lo[word] = ~reversed.m_lo[word];
            lower[word] = ~lower[word];
        }
        reversed.m_lo.back() &= VL_MASK_E(m_bits);
        lower.back() &= VL_MASK_E(m_bits);
        Value result;
        const bool found VL_ATTR_UNUSED = patternAtLeast(reversed, lower, result);
        assert(found);
        for (EData& word : result) word = ~word;
        result.back() &= VL_MASK_E(m_bits);
        return result;
    }
    Search hasValue(uint32_t bin, const Range& range) const;
    Search intersects(uint32_t bin, const Range& filter) const;
};

// One bounded search.  Shared ordered decisions avoid expanding the complement of wildcard
// exclusions; the graph is discarded with the query, so instances retain none of it.
class VlCoverpoint::ValueData::Query final {
    struct Decision final {
        uint32_t m_position;  // One-based value-bit position; zero denotes a terminal
        uint32_t m_low;  // Child node ID for a zero-valued ordering bit
        uint32_t m_high;  // Child node ID for a one-valued ordering bit
        uint32_t m_inverse;  // Complement node ID, or UINT32_MAX if not cached
    };

    const ValueData& m_data;  // Value width and ordering of the queried coverpoint
    std::vector<Decision> m_decisions{{0, 0, 0, 1}, {0, 1, 1, 0}};  // Nodes; 0=false, 1=true
    // (Position, low, high) -> canonical node ID
    std::map<std::tuple<uint32_t, uint32_t, uint32_t>, uint32_t> m_unique;
    std::map<std::pair<uint32_t, uint32_t>, uint32_t> m_combined;  // Cached intersection roots
    uint32_t m_work = 0;  // Graph steps consumed by this query
    bool m_limited = false;  // The work limit was exceeded, so the result is unknown

    bool step() {
        if (m_limited) return false;
        if (++m_work <= QUERY_WORK_LIMIT) return true;
        m_limited = true;
        return false;
    }
    uint32_t decision(uint32_t position, uint32_t low, uint32_t high) {
        if (m_limited) return 0;
        if (low == high) return low;
        const auto key = std::make_tuple(position, low, high);
        const auto it = m_unique.find(key);
        if (it != m_unique.end()) return it->second;
        const uint32_t result = static_cast<uint32_t>(m_decisions.size());
        m_decisions.push_back({position, low, high, UINT32_MAX});
        m_unique.emplace(key, result);
        return result;
    }
    uint32_t rangeDecision(const Range& range, uint32_t position, uint32_t bounds,
                           std::vector<std::array<uint32_t, 4>>& cache) {
        if (!step()) return 0;
        uint32_t& cached = cache[position][bounds];
        if (cached != UINT32_MAX) return cached;
        const uint32_t bit = position - 1;
        const uint32_t lower = m_data.orderBit(range.m_lo, bit);
        const uint32_t upper = m_data.orderBit(range.m_hi, bit);
        uint32_t children[2] = {0, 0};
        for (uint32_t value = 0; value < 2; ++value) {
            if ((!range.m_mask.empty() && VL_BITISSET_W(range.m_mask, bit) && value != lower)
                || ((bounds & 1U) && value < lower) || ((bounds & 2U) && value > upper)) {
                continue;
            }
            const uint32_t next = ((bounds & 1U) && value == lower ? 1U : 0U)
                                  | ((bounds & 2U) && value == upper ? 2U : 0U);
            children[value] = rangeDecision(range, position - 1, next, cache);
        }
        cached = decision(position, children[0], children[1]);
        return cached;
    }

public:
    explicit Query(const ValueData& data)
        : m_data{data} {}
    bool limited() const { return m_limited; }
    uint32_t intersect(uint32_t lhs, uint32_t rhs) {
        if (!step()) return 0;
        if (lhs == rhs) return lhs;
        if (!lhs || !rhs) return 0;
        if (lhs == 1) return rhs;
        if (rhs == 1) return lhs;
        if (rhs < lhs) std::swap(lhs, rhs);
        const auto key = std::make_pair(lhs, rhs);
        const auto it = m_combined.find(key);
        if (it != m_combined.end()) return it->second;
        // Recursive calls can grow decisions, so do not retain references into it.
        const Decision left = m_decisions[lhs];
        const Decision right = m_decisions[rhs];
        const uint32_t position = std::max(left.m_position, right.m_position);
        const uint32_t low = intersect(left.m_position == position ? left.m_low : lhs,
                                       right.m_position == position ? right.m_low : rhs);
        const uint32_t high = intersect(left.m_position == position ? left.m_high : lhs,
                                        right.m_position == position ? right.m_high : rhs);
        const uint32_t result = decision(position, low, high);
        m_combined.emplace(key, result);
        return result;
    }
    uint32_t negate(uint32_t root) {
        if (!step()) return 0;
        if (m_decisions[root].m_inverse != UINT32_MAX) return m_decisions[root].m_inverse;
        const Decision node = m_decisions[root];
        const uint32_t low = negate(node.m_low);
        const uint32_t high = negate(node.m_high);
        const uint32_t result = decision(node.m_position, low, high);
        m_decisions[root].m_inverse = result;
        m_decisions[result].m_inverse = root;
        return result;
    }
    uint32_t rangeRoot(const Range& range) {
        if (m_data.less(range.m_hi, range.m_lo)) return 0;
        std::vector<std::array<uint32_t, 4>> cache(m_data.m_bits + 1);
        for (auto& entry : cache) entry.fill(UINT32_MAX);
        cache[0].fill(1);
        return rangeDecision(range, m_data.m_bits, 3, cache);
    }
};

VlCoverpoint::ValueData::Search VlCoverpoint::ValueData::hasValue(uint32_t bin,
                                                                  const Range& range) const {
    if (m_values[bin].m_transition || m_exclusions.empty() || !excluded(view(range.m_lo))) {
        return Search::VALUE;
    }
    const Value last = lastValue(range);
    if (!excluded(view(last))) return Search::VALUE;
    if (last == range.m_lo) return Search::EMPTY;
    // Try cheap witnesses first; only difficult queries need a bounded symbolic search.
    if (m_bits > QUERY_DEPTH_LIMIT) return Search::DEPTH_LIMIT;
    Query query{*this};
    uint32_t root = query.rangeRoot(range);
    for (const Range& exclusion : m_exclusions) {
        root = query.intersect(root, query.negate(query.rangeRoot(exclusion)));
        if (!root) break;
    }
    if (query.limited()) return Search::WORK_LIMIT;
    return root ? Search::VALUE : Search::EMPTY;
}

VlCoverpoint::ValueData::Search VlCoverpoint::ValueData::intersects(uint32_t bin,
                                                                    const Range& filter) const {
    Search result = Search::EMPTY;
    for (const Range& source : m_values[bin].m_ranges) {
        Range range = source;
        if (!clip(range, filter.m_lo, filter.m_hi)) continue;
        const Search search = hasValue(bin, range);
        if (search == Search::VALUE) return search;
        if (search != Search::EMPTY) result = search;
    }
    return result;
}

VlCoverpoint::VlCoverpoint() = default;
VlCoverpoint::~VlCoverpoint() = default;

void VlCoverpoint::valueType(uint32_t bits, bool isSigned) {
    assert(!m_valuesp);
    m_valuesp.reset(new ValueData{bits, isSigned, m_total});
}

void VlCoverpoint::valueRanges(std::initializer_list<EData> entries) {
    ValueData& data = *m_valuesp;
    assert(!data.m_frozen);
    const uint32_t words = data.m_words;
    assert(entries.size() % (1 + 2 * words) == 0);
    for (const EData* entryp = entries.begin(); entryp != entries.end(); entryp += 1 + 2 * words) {
        data.m_values[entryp[0]].m_ranges.push_back(
            {data.read(WDataInP::external(entryp + 1)),
             data.read(WDataInP::external(entryp + 1 + words)),
             {}});
    }
}

void VlCoverpoint::valueRuns(std::initializer_list<EData> entries) {
    // The compiler describes each run of bins with one entry, rather than one per bin, so the
    // constructor's code does not grow with the number of bins.  An entry holds the first bin
    // and the bin count, then the low, span, and high values, each of 'words' words.
    static constexpr uint32_t HEADER_WORDS = 2;  // First bin and bin count, before the values
    static constexpr uint32_t VALUES = 3;  // Low, span, and high values
    ValueData& data = *m_valuesp;
    assert(!data.m_frozen);
    const uint32_t words = data.m_words;
    const uint32_t entryWords = HEADER_WORDS + VALUES * words;
    const EData* const endp = entries.end();
    for (const EData* entryp = entries.begin(); entryp != endp; entryp += entryWords) {
        assert(static_cast<size_t>(endp - entryp) >= entryWords);  // Only whole entries
        const uint32_t first = entryp[0];
        const uint32_t count = entryp[1];
        const EData* const valuesp = entryp + HEADER_WORDS;
        ValueData::Value lo = data.read(WDataInP::external(valuesp));
        const ValueData::Value span = data.read(WDataInP::external(valuesp + words));
        const ValueData::Value hi = data.read(WDataInP::external(valuesp + 2 * words));
        // Expand the run into the value range of each of its bins, as valueRanges() gives them:
        // until valueRelease(), valueFinalize() finds the bins exclusions leave without values,
        // and runtime cross selections intersect their filters, from these ranges.  Each bin
        // starts after the previous bin's last value and holds span + 1 values, except the last
        // bin, which extends to the run's high value.
        for (uint32_t k = 0; k < count; ++k) {
            ValueData::Value last = hi;
            if (k + 1 < count) {
                last = lo;
                data.add(last, span);
            }
            data.m_values[first + k].m_ranges.push_back({lo, last, {}});
            lo = last;
            data.increment(lo);
        }
    }
}

void VlCoverpoint::valuePatterns(std::initializer_list<EData> entries) {
    ValueData& data = *m_valuesp;
    assert(!data.m_frozen);
    const uint32_t words = data.m_words;
    assert(entries.size() % (1 + 4 * words) == 0);
    for (const EData* entryp = entries.begin(); entryp != entries.end(); entryp += 1 + 4 * words) {
        ValueData::Range range;
        if (data.pattern(WDataInP::external(entryp + 1), WDataInP::external(entryp + 1 + words),
                         WDataInP::external(entryp + 1 + 2 * words),
                         WDataInP::external(entryp + 1 + 3 * words), range)) {
            data.m_values[entryp[0]].m_ranges.push_back(std::move(range));
        }
    }
}

void VlCoverpoint::valueTransitions(std::initializer_list<uint32_t> bins) {
    for (const uint32_t bin : bins) m_valuesp->m_values[bin].m_transition = true;
}

bool VlCoverpoint::liveBin(uint32_t bin) const {
    const ValueData& data = *m_valuesp;
    ValueData::Search limit = ValueData::Search::EMPTY;
    for (const ValueData::Range& range : data.m_values[bin].m_ranges) {
        const ValueData::Search search = data.hasValue(bin, range);
        if (search == ValueData::Search::VALUE) return true;
        if (search != ValueData::Search::EMPTY) limit = search;
    }
    if (limit == ValueData::Search::EMPTY) return false;
    // Keep a bin whose exclusions cannot be analyzed, rather than stop the simulation.
    const VlCovNamer& namer = namerFor(bin);
    VL_WARN_MT(
        namer.file(), namer.line(), "",
        limit == ValueData::Search::WORK_LIMIT
            ? "Coverage bin exclusions exceed the decision-graph work limit; bin retained"
            : "Coverage bin exclusions exceed the decision-graph depth limit; bin retained");
    return true;
}

void VlCoverpoint::valueFinalize() {
    ValueData& data = *m_valuesp;
    assert(!data.m_frozen);
    for (const VlCovNamer& namer : m_namers) {
        const bool exclusion = namer.set() == VlCovBinKind::KIND_IGNORE
                               || namer.set() == VlCovBinKind::KIND_ILLEGAL;
        for (uint32_t bin = namer.base(); bin < namer.base() + namer.count(); ++bin) {
            ValueData::Values& values = data.m_values[bin];
            data.normalize(values.m_ranges);
            if (exclusion && !values.m_transition) {
                data.m_exclusions.insert(data.m_exclusions.end(), values.m_ranges.begin(),
                                         values.m_ranges.end());
            }
        }
    }
    data.m_regularExclusions = data.normalize(data.m_exclusions);
    m_crossToBin.clear();
    std::fill(m_crossIdx.begin(), m_crossIdx.end(), -1);
    m_normal = 0;
    // Normal bins without values leave the report and the coverage denominator.
    for (const VlCovNamer& namer : m_namers) {
        const bool normal = namer.set() == VlCovBinKind::KIND_NORMAL;
        for (uint32_t bin = namer.base(); bin < namer.base() + namer.count(); ++bin) {
            if (normal && !liveBin(bin)) continue;
            data.m_reported.push_back(bin);
            if (!normal) continue;
            m_crossIdx[bin] = static_cast<int>(m_normal++);
            m_crossToBin.push_back(bin);
        }
    }
    data.m_frozen = true;
}

void VlCoverpoint::valueRelease() {
    ValueData& data = *m_valuesp;
    assert(data.m_frozen);
    std::vector<ValueData::Values>{}.swap(data.m_values);
}

bool VlCoverpoint::valueExcluded(QData value) const {
    VlWide<VL_WQ_WORDS_E> words;
    VL_SET_WQ(words, value);
    return valueExcludedW(words);
}

bool VlCoverpoint::valueExcludedW(WDataInP valuep) const { return m_valuesp->excluded(valuep); }

void VlCoverpoint::init(const char* hier, uint32_t atLeast, uint32_t nBins) {
    m_hier = hier;
    m_atLeast = atLeast;
    m_total = nBins;
    m_counts.assign(nBins, 0);
    m_crossIdx.assign(nBins, -1);
    m_crossToBin.clear();
}

void VlCoverpoint::addNamer(VlCovBinKind set, uint32_t count, VlCovBinNaming naming,
                            const char* name, const char* file, int line, int col) {
    m_namers.emplace_back(set, count, m_nextBase, naming, name, file, line, col);
    if (set == VlCovBinKind::KIND_NORMAL) {
        // Assign each Normal bin a cross index, and record the inverse map.
        for (uint32_t b = m_nextBase; b < m_nextBase + count; ++b) {
            m_crossIdx[b] = static_cast<int>(m_crossToBin.size());
            m_crossToBin.push_back(b);
        }
        m_normal += count;
    }
    m_nextBase += count;
}

std::string VlCoverpoint::normalBinName(uint32_t crossIdx) const {
    // Build the bin name based on the bin index
    return declaredBinName(m_crossToBin[crossIdx]);
}

const VlCovNamer& VlCoverpoint::namerFor(uint32_t i) const {
    // Namers are appended in ascending order covering [0, m_total).
    const auto it = std::upper_bound(
        m_namers.begin(), m_namers.end(), i,
        [](uint32_t bin, const VlCovNamer& namer) { return bin < namer.base(); });
    assert(it != m_namers.begin());
    return *std::prev(it);
}

std::string VlCoverpoint::declaredBinName(uint32_t bin) const {
    const VlCovNamer& nm = namerFor(bin);
    std::string name = nm.name();
    if (nm.naming() == VlCovBinNaming::Array) {
        name += '[' + std::to_string(bin - nm.base()) + ']';
    } else if (nm.naming() == VlCovBinNaming::Numbered) {
        name += '_' + std::to_string(bin - nm.base());
    }
    return name;
}

uint32_t VlCoverpoint::reportedBin(uint32_t i) const {
    return m_valuesp ? m_valuesp->m_reported[i] : i;
}

uint32_t VlCoverpoint::binCount() const {
    return m_valuesp ? static_cast<uint32_t>(m_valuesp->m_reported.size()) : m_total;
}

std::string VlCoverpoint::binName(uint32_t i) const { return declaredBinName(reportedBin(i)); }

#if VM_COVERAGE
void VlCoverpoint::registerBins(VerilatedCovContext* covcontextp, const char* page) {
    for (uint32_t reported = 0; reported < binCount(); ++reported) {
        const uint32_t i = reportedBin(reported);
        const VlCovNamer& nm = namerFor(i);
        const VlCovBinKind kind = binKind(reported);
        const std::string binp = binName(reported);
        const std::string full = m_hier + "." + binp;
        const std::string lineStr = std::to_string(nm.line());
        const std::string colStr = std::to_string(nm.col());
        if (kind == VlCovBinKind::KIND_NORMAL) {
            VL_COVER_INSERT(covcontextp, full.c_str(), &m_counts[i], "page", page, "filename",
                            nm.file(), "lineno", lineStr.c_str(), "column", colStr.c_str(), "bin",
                            binp.c_str());
        } else {
            const char* const binType = kind == VlCovBinKind::KIND_IGNORE    ? "ignore"
                                        : kind == VlCovBinKind::KIND_ILLEGAL ? "illegal"
                                                                             : "default";
            VL_COVER_INSERT(covcontextp, full.c_str(), &m_counts[i], "page", page, "filename",
                            nm.file(), "lineno", lineStr.c_str(), "column", colStr.c_str(), "bin",
                            binp.c_str(), "bin_type", binType);
        }
    }
}
#endif  // VM_COVERAGE

//=============================================================================
// VlCoverCross

void VlCoverCross::init(const char* hier, uint32_t dims, VlCoverpoint* const* cps,
                        const char* file, int line, int col) {
    m_hier = hier;
    m_file = file;
    m_line = line;
    m_col = col;
    assert(dims == m_dims);
    // Accumulate in 64 bits so the overflow check itself cannot overflow.
    uint64_t product = m_numAutoBins ? 1 : 0;
    for (uint32_t d = 0; d < dims; ++d) {
        m_dimensionsp[d] = {cps[d], nullptr, cps[d]->normalBinCount(), 1};
        product *= m_dimensionsp[d].bins;
        if (VL_UNLIKELY(product > UINT32_MAX)) {  // LCOV_EXCL_START
            VL_FATAL_MT(file, line, "", "Cross has too many auto bins to represent");
        }  // LCOV_EXCL_STOP
    }
    assert(product == m_numAutoBins);
    // stride[d] = product of the Normal bin counts of all dimensions after d.
    // Counts down with an offset so the unsigned index never wraps below zero.
    for (uint32_t d = dims; d > 1; --d) {
        m_dimensionsp[d - 2].stride = m_dimensionsp[d - 1].stride * m_dimensionsp[d - 1].bins;
    }
}

void VlCoverCross::addBin(VlCovBinKind kind, std::initializer_list<uint64_t> selection,
                          const char* namep, const char* filep, int line, int col) {
    if (!m_numAutoBins) return;  // An empty product creates no cross bin.
    addBinImpl(kind, selection.begin(), static_cast<uint32_t>(selection.size()), namep, filep,
               line, col, m_explicitp->numBins);
}

void VlCoverCross::addBinImpl(VlCovBinKind kind, const uint64_t* sourcep, uint32_t words,
                              const char* namep, const char* filep, int line, int col,
                              uint32_t iffIndex) {
    Explicit& data = *m_explicitp;
    assert(words == VL_BITWORD_Q(static_cast<uint64_t>(m_numAutoBins) + VL_QUADSIZE - 1));
    assert(data.numBins < data.bins.size());
    uint64_t* const selectionp = data.selectionp + static_cast<uint64_t>(data.numBins) * words;
    std::copy(sourcep, sourcep + words, selectionp);
    Bin& bin = data.bins[data.numBins++];
    bin.selectionp = selectionp;
    bin.namep = namep;
    bin.filep = filep;
    bin.line = line;
    bin.col = col;
    bin.kind = kind;
    bin.iffIndex = iffIndex;
    if (kind == VlCovBinKind::KIND_NORMAL) ++data.normalBins;
    for (uint32_t word = 0; word < words; ++word) {
        data.wordsp[word].autoExcluded |= selectionp[word];
    }
}

void VlCoverCross::finalizeBins() {
    if (!hasExplicitBins()) return;
    Explicit& data = *m_explicitp;
    assert(data.numBins == data.bins.size());
    uint32_t autoIdx = 0;
    for (uint32_t flat = 0; flat < m_numAutoBins; ++flat) {
        if (!(data.wordsp[flat / 64].autoExcluded & (uint64_t{1} << (flat % 64)))) {
            assert(autoIdx < data.autoBins.size());
            data.autoBins[autoIdx++] = flat;
        }
    }
    const uint32_t words = m_numAutoBins / 64 + (m_numAutoBins % 64 != 0);
    assert(autoIdx == data.autoBins.size());
    data.minBinWords = words;
    uint64_t pos = 0;
    const uint32_t* const indicesp = data.binWords.begin();
    for (Bin& bin : data.bins) {
        const uint64_t begin = pos;
        for (uint32_t word = 0; word < words; ++word) {
            if (bin.selectionp[word]) {
                assert(pos < data.binWords.size());
                data.binWords[pos++] = word;
            }
        }
        bin.wordIndicesp = indicesp ? indicesp + begin : nullptr;
        bin.numWords = static_cast<uint32_t>(pos - begin);
        data.minBinWords = std::min(data.minBinWords, bin.numWords);
    }
    assert(pos == data.binWords.size());
}

template <bool T_Explicit, bool T_RecordHits>
void VlCoverCross::iterateProduct(uint32_t dim, uint32_t baseIdx) {
    const VlCoverpoint* const cpp = m_dimensionsp[dim].cpp;
    const uint32_t hits = cpp->hitCount();
    const uint32_t* const list = m_dimensionsp[dim].hitsp;
    const bool last = (dim == m_dims - 1);
    const uint32_t stride = m_dimensionsp[dim].stride;
    for (uint32_t hit = 0; hit < hits; ++hit) {
        const uint32_t idx = baseIdx + list[hit] * stride;
        if (last) {
            if (T_Explicit) {
                incrementTuple<T_RecordHits>(idx);
            } else {
                incrementAuto(idx);
            }
        } else {
            iterateProduct<T_Explicit, T_RecordHits>(dim + 1, idx);
        }
    }
}

void VlCoverCross::incrementBin(Bin& bin) {
    if (bin.count++ == 0 && bin.kind == VlCovBinKind::KIND_NORMAL) ++m_numCovered;
    if (VL_UNLIKELY(bin.kind == VlCovBinKind::KIND_ILLEGAL)) {
        VL_PRINTF_MT("%%Error: %s:%d: Illegal cross bin '%s' hit in cross '%s'.\n", bin.filep,
                     bin.line, bin.namep, m_hier.c_str());
        VL_STOP_MT(bin.filep, bin.line, "");
    }
}

template <bool T_ApplyIffs>
void VlCoverCross::sampleSingleTuple(uint32_t idx, const bool* binIffs) {
    Explicit& data = *m_explicitp;
    const uint32_t word = idx / VL_QUADSIZE;
    const uint64_t bit = uint64_t{1} << VL_BITBIT_Q(idx);
    if (!(data.wordsp[word].autoExcluded & bit)) {
        incrementAuto(idx);
        return;
    }
    for (Bin& bin : data.bins) {
        if (T_ApplyIffs && !binIffs[bin.iffIndex]) continue;
        if (bin.selectionp[word] & bit) incrementBin(bin);
    }
}

template <bool T_ApplyIffs, uint32_t T_Touched, bool T_Dense>
void VlCoverCross::sampleBins(const bool* binIffs) {
    struct HitWord final {
        uint32_t index;
        uint64_t bits;
    };
    Explicit& data = *m_explicitp;
    const uint64_t bins = data.numBins;
    const uint64_t touched = T_Touched ? T_Touched : data.numTouchedWords;
    const Word* const wordsp = data.wordsp;
    std::array<HitWord, T_Touched> cached{};
    for (uint32_t i = 0; i < T_Touched; ++i) {
        const uint32_t word = wordsp[i].touchedWord;
        cached[i] = {word, wordsp[word].hitBits};
    }
    for (uint64_t binIdx = 0; binIdx < bins; ++binIdx) {
        Bin& bin = data.bins[binIdx];
        if (T_ApplyIffs && !binIffs[bin.iffIndex]) continue;
        bool matched = false;
        if (T_Touched == 1) {
            matched = (bin.selectionp[cached[0].index] & cached[0].bits) != 0;
        } else if (T_Dense || bin.numWords >= touched) {
            for (uint64_t i = 0; i < touched; ++i) {
                const uint32_t word = T_Touched ? cached[i].index : wordsp[i].touchedWord;
                const uint64_t hits = T_Touched ? cached[i].bits : wordsp[word].hitBits;
                if (bin.selectionp[word] & hits) {
                    matched = true;
                    break;
                }
            }
        } else {
            for (uint32_t pos = 0; pos < bin.numWords; ++pos) {
                const uint32_t word = bin.wordIndicesp[pos];
                if (bin.selectionp[word] & wordsp[word].hitBits) {
                    matched = true;
                    break;
                }
            }
        }
        if (matched) incrementBin(bin);
    }
    for (uint32_t i = 0; i < data.numTouchedWords; ++i) {
        data.wordsp[wordsp[i].touchedWord].hitBits = 0;
    }
    data.numTouchedWords = 0;
}

template <bool T_ApplyIffs, bool T_Dense>
void VlCoverCross::sampleHitWords(const bool* binIffs) {
    switch (m_explicitp->numTouchedWords) {
    case 1: sampleBins<T_ApplyIffs, 1, T_Dense>(binIffs); break;
    case 2: sampleBins<T_ApplyIffs, 2, T_Dense>(binIffs); break;
    case 3: sampleBins<T_ApplyIffs, 3, T_Dense>(binIffs); break;
    default: sampleBins<T_ApplyIffs, 0, T_Dense>(binIffs); break;
    }
}

void VlCoverCross::sample(const bool* binIffs) {
    if (VL_UNLIKELY(!m_numAutoBins)) return;
    // Fast path: if any dimension had no Normal-bin hit, the cross cannot hit.
    bool single = true;
    for (uint32_t d = 0; d < m_dims; ++d) {
        const uint32_t hits = m_dimensionsp[d].cpp->hitCount();
        if (hits == 0) return;
        single &= hits == 1;
    }
    if (single) {
        uint32_t idx = 0;
        for (uint32_t d = 0; d < m_dims; ++d) {
            idx += m_dimensionsp[d].cpp->hitList()[0] * m_dimensionsp[d].stride;
        }
        if (hasExplicitBins()) {
            if (binIffs) {
                sampleSingleTuple<true>(idx, binIffs);
            } else {
                sampleSingleTuple<false>(idx, nullptr);
            }
        } else {
            incrementAuto(idx);
        }
        return;
    }
    bool enabled = true;
    if (hasExplicitBins() && binIffs && !binIffs[m_explicitp->bins[0].iffIndex]) {
        enabled = std::any_of(m_explicitp->bins.begin() + 1, m_explicitp->bins.end(),
                              [binIffs](const Bin& bin) { return binIffs[bin.iffIndex]; });
        if (!enabled && m_explicitp->autoBins.empty()) return;
    }
    for (uint32_t d = 0; d < m_dims; ++d) {
        m_dimensionsp[d].hitsp = m_dimensionsp[d].cpp->hitList();
    }
    if (!hasExplicitBins()) {
        iterateProduct<false>(0, 0);
        return;
    }
    if (!enabled) {
        iterateProduct<true, false>(0, 0);
        return;
    }
    iterateProduct<true>(0, 0);
    if (m_explicitp->numTouchedWords) {
        const bool dense = m_explicitp->minBinWords >= m_explicitp->numTouchedWords;
        if (binIffs) {
            if (dense) {
                sampleHitWords<true, true>(binIffs);
            } else {
                sampleHitWords<true, false>(binIffs);
            }
        } else {
            if (dense) {
                sampleHitWords<false, true>(nullptr);
            } else {
                sampleHitWords<false, false>(nullptr);
            }
        }
    }
}

std::string VlCoverCross::binName(uint32_t i) const {
    if (hasExplicitBins()) {
        if (i < m_explicitp->bins.size()) return m_explicitp->bins[i].namep;
        i -= static_cast<uint32_t>(m_explicitp->bins.size());
    }
    return autoBinName(autoIndex(i));
}

std::string VlCoverCross::autoBinName(uint32_t flat) const {
    // Built on demand by concatenating each coverpoint's own bin name.
    std::string name;
    for (uint32_t d = 0; d < m_dims; ++d) {
        const Dimension& dimension = m_dimensionsp[d];
        const uint32_t crossIdx = (flat / dimension.stride) % dimension.bins;
        if (d > 0) name += "_x_";
        name += dimension.cpp->normalBinName(crossIdx);
    }
    return name;
}

#if VM_COVERAGE
void VlCoverCross::registerBins(VerilatedCovContext* covcontextp, const char* page) {
    const std::string lineStr = std::to_string(m_line);
    const std::string colStr = std::to_string(m_col);
    const uint32_t explicitCount
        = hasExplicitBins() ? static_cast<uint32_t>(m_explicitp->bins.size()) : 0;
    // Use the same indexed names for registration and the runtime read interface.
    for (uint32_t i = 0; i < binCount(); ++i) {
        const std::string bin = binName(i);
        const std::string full = m_hier + "." + bin;
        if (i < explicitCount) {
            Bin& userBin = m_explicitp->bins[i];
            const std::string binLineStr = std::to_string(userBin.line);
            const std::string binColStr = std::to_string(userBin.col);
            if (userBin.kind == VlCovBinKind::KIND_NORMAL) {
                VL_COVER_INSERT(covcontextp, full.c_str(), &userBin.count, "page", page,
                                "filename", userBin.filep, "lineno", binLineStr.c_str(), "column",
                                binColStr.c_str(), "bin", bin.c_str(), "cross", "1");
            } else {
                const char* const binType
                    = userBin.kind == VlCovBinKind::KIND_IGNORE ? "ignore" : "illegal";
                VL_COVER_INSERT(covcontextp, full.c_str(), &userBin.count, "page", page,
                                "filename", userBin.filep, "lineno", binLineStr.c_str(), "column",
                                binColStr.c_str(), "bin", bin.c_str(), "cross", "1", "bin_type",
                                binType);
            }
            continue;
        }
        const uint32_t flat = autoIndex(i - explicitCount);
        // cross_bins metadata: the same components joined by ',' (not read by the report)
        std::string crossBins;
        for (uint32_t d = 0; d < m_dims; ++d) {
            const Dimension& dimension = m_dimensionsp[d];
            const uint32_t crossIdx = (flat / dimension.stride) % dimension.bins;
            if (d > 0) crossBins += ",";
            crossBins += dimension.cpp->normalBinName(crossIdx);
        }
        VL_COVER_INSERT(covcontextp, full.c_str(), &m_flatCountsp[flat], "page", page, "filename",
                        m_file, "lineno", lineStr.c_str(), "column", colStr.c_str(), "bin",
                        bin.c_str(), "cross", "1", "cross_bins", crossBins.c_str());
    }
}
#endif  // VM_COVERAGE

//=============================================================================
// VlCoverCrossDyn

class VlCoverCrossDyn::Layout final {
    friend class VlCoverCrossDyn;

    using Mask = std::vector<uint64_t>;
    using Search = VlCoverpoint::ValueData::Search;
    struct Selected final {
        Bin m_info{};  // Declaration metadata, bin kind, and original iff index
        Mask m_mask;  // Tuple-selection bitmap for the declared bin
    };
    uint32_t m_tuples = 0;  // Cartesian product of live coverpoint-bin counts
    uint32_t m_words = 0;  // 64-bit words per tuple-selection bitmap
    std::vector<Dimension> m_dimensions;  // Coverpoint bindings, hit lists, and tuple strides
    std::vector<uint32_t> m_counts;  // Dense automatic-bin counters, one slot per flat tuple ID
    std::vector<Bin> m_bins;  // Final compacted explicit-bin records
    std::vector<Word> m_hitWords;  // Auto-exclusion and hit masks, plus touched-word IDs
    std::vector<uint32_t> m_autoBins;  // Flat tuple IDs retained as automatic cross bins
    std::vector<uint32_t> m_binWords;  // Packed nonzero selection-word indices per explicit bin
    std::vector<uint64_t> m_selections;  // Contiguous bitmaps for finalized explicit bins
    Explicit m_explicitData{{nullptr, 0},
                            nullptr,
                            {nullptr, 0},
                            {nullptr, 0},
                            nullptr};  // Storage views bound to the base sampler
    std::vector<Mask> m_stack;  // Postfix evaluation stack for construction-time selections
    std::vector<Selected> m_selected;  // Declared bins pending exclusion and compaction
    uint32_t m_selectDimension = 0;  // Dimension whose binsof selection is being built
    uint32_t m_selectFirst = 0;  // First declared coverpoint bin named by the binsof term
    uint32_t m_selectEnd = 0;  // One past the last declared coverpoint bin named by binsof
    bool m_negate = false;  // Complement the completed dimension membership mask
    Search m_limit = Search::EMPTY;  // A search limit left the current bin's selection unknown
    std::vector<bool> m_allowed;  // Normal-bin membership mask for the current dimension

    static void setRange(Mask& mask, uint64_t first, uint64_t end) {
        while (first < end) {
            const uint64_t bit = VL_BITBIT_Q(first);
            const uint64_t bits = std::min<uint64_t>(VL_QUADSIZE - bit, end - first);
            mask[VL_BITWORD_Q(first)]
                |= (bits == VL_QUADSIZE ? ~uint64_t{0} : (uint64_t{1} << bits) - 1) << bit;
            first += bits;
        }
    }
    bool named(uint32_t index) const {
        const uint32_t bin = m_dimensions[m_selectDimension].cpp->m_crossToBin[index];
        return bin >= m_selectFirst && bin < m_selectEnd;
    }
    void range(WDataInP lop, WDataInP hip) {
        const VlCoverpoint* const cpp = m_dimensions[m_selectDimension].cpp;
        const VlCoverpoint::ValueData& data = *cpp->m_valuesp;
        const VlCoverpoint::ValueData::Range filter{data.read(lop), data.read(hip), {}};
        for (uint32_t i = 0; i < m_allowed.size(); ++i) {
            if (m_allowed[i] || !named(i)) continue;
            const Search search = data.intersects(cpp->m_crossToBin[i], filter);
            if (search == Search::VALUE) {
                m_allowed[i] = true;
            } else if (search != Search::EMPTY) {
                m_limit = search;
            }
        }
    }
};

VlCoverCrossDyn::VlCoverCrossDyn()
    : VlCoverCross{0, 0}
    , m_layoutp{new Layout} {}

VlCoverCrossDyn::~VlCoverCrossDyn() = default;

void VlCoverCrossDyn::init(const char* hier, uint32_t dims, VlCoverpoint* const* cps,
                           const char* file, int line, int col) {
    Layout& data = *m_layoutp;
    uint64_t tuples = std::any_of(cps, cps + dims,
                                  [](const VlCoverpoint* cpp) { return !cpp->normalBinCount(); })
                          ? 0
                          : 1;
    for (uint32_t i = 0; i < dims; ++i) tuples *= cps[i]->normalBinCount();
    // Verilation bounds the product of the declared bins, which live bins cannot exceed.
    assert(tuples <= UINT32_MAX);
    data.m_tuples = static_cast<uint32_t>(tuples);
    data.m_words = VL_BITWORD_Q(static_cast<uint64_t>(data.m_tuples) + VL_QUADSIZE - 1);
    data.m_dimensions.resize(dims);
    data.m_counts.resize(data.m_tuples, 0);
    shape(dims, data.m_tuples);
    bindStorage(data.m_dimensions.data(), data.m_counts.data());
    VlCoverCross::init(hier, dims, cps, file, line, col);
}

void VlCoverCrossDyn::selectAll() {
    Layout& data = *m_layoutp;
    data.m_stack.emplace_back(data.m_words, ~uint64_t{0});
    if (data.m_words) data.m_stack.back().back() &= VL_MASK_Q(data.m_tuples);
}

void VlCoverCrossDyn::selectDim(uint32_t dim, uint32_t first, uint32_t end, bool negated,
                                bool intersect) {
    Layout& data = *m_layoutp;
    data.m_selectDimension = dim;
    data.m_selectFirst = first;
    data.m_selectEnd = end;
    data.m_negate = negated;
    data.m_allowed.assign(data.m_dimensions[dim].bins, false);
    if (!intersect) {
        for (uint32_t i = 0; i < data.m_allowed.size(); ++i) data.m_allowed[i] = data.named(i);
    }
}

void VlCoverCrossDyn::selectRange(QData lo, QData hi) {
    VlWide<VL_WQ_WORDS_E> low;
    VlWide<VL_WQ_WORDS_E> high;
    VL_SET_WQ(low, lo);
    VL_SET_WQ(high, hi);
    m_layoutp->range(low, high);
}

void VlCoverCrossDyn::selectRangeW(WDataInP lop, WDataInP hip) { m_layoutp->range(lop, hip); }

void VlCoverCrossDyn::selectDimEnd() {
    Layout& data = *m_layoutp;
    data.m_stack.emplace_back(data.m_words, 0);
    Layout::Mask& mask = data.m_stack.back();
    const Dimension& dim = data.m_dimensions[data.m_selectDimension];
    // Each run of adjacent selected bins covers one contiguous tuple span per period.
    std::vector<std::pair<uint32_t, uint32_t>> runs;  // [first, end) bin indices
    for (uint32_t i = 0; i < dim.bins;) {
        if (data.m_allowed[i] == data.m_negate) {
            ++i;
            continue;
        }
        const uint32_t begin = i++;
        while (i < dim.bins && data.m_allowed[i] != data.m_negate) ++i;
        runs.emplace_back(begin, i);
    }
    const uint64_t stride = dim.stride;
    const uint64_t period = stride * dim.bins;
    for (uint64_t base = 0; base < data.m_tuples; base += period) {
        for (const auto& run : runs) {
            Layout::setRange(mask, base + run.first * stride, base + run.second * stride);
        }
    }
}

void VlCoverCrossDyn::selectAnd() {
    Layout& data = *m_layoutp;
    Layout::Mask rhs = std::move(data.m_stack.back());
    data.m_stack.pop_back();
    for (uint32_t word = 0; word < data.m_words; ++word) data.m_stack.back()[word] &= rhs[word];
}

void VlCoverCrossDyn::selectOr() {
    Layout& data = *m_layoutp;
    Layout::Mask rhs = std::move(data.m_stack.back());
    data.m_stack.pop_back();
    for (uint32_t word = 0; word < data.m_words; ++word) data.m_stack.back()[word] |= rhs[word];
}

void VlCoverCrossDyn::selectBin(VlCovBinKind kind, const char* namep, const char* filep, int line,
                                int col, uint32_t iffIndex) {
    Layout& data = *m_layoutp;
    if (VL_UNLIKELY(data.m_limit != Layout::Search::EMPTY)) {
        // Ignore a bin whose selection cannot be analyzed, rather than stop the simulation.
        VL_WARN_MT(
            filep, line, "",
            data.m_limit == Layout::Search::WORK_LIMIT
                ? "Cross bin selection exceeds the decision-graph work limit; bin ignored"
                : "Cross bin selection exceeds the decision-graph depth limit; bin ignored");
        data.m_limit = Layout::Search::EMPTY;
        data.m_stack.pop_back();
        return;
    }
    Bin bin{};
    bin.kind = kind;
    bin.namep = namep;
    bin.filep = filep;
    bin.line = line;
    bin.col = col;
    bin.iffIndex = iffIndex;
    data.m_selected.push_back({bin, std::move(data.m_stack.back())});
    data.m_stack.pop_back();
}

void VlCoverCrossDyn::finalizeBins() {
    Layout& data = *m_layoutp;
    Layout::Mask excluded(data.m_words, 0);
    for (const Layout::Selected& bin : data.m_selected) {
        if (bin.m_info.kind == VlCovBinKind::KIND_NORMAL) continue;
        for (uint32_t word = 0; word < data.m_words; ++word) excluded[word] |= bin.m_mask[word];
    }
    for (Layout::Selected& bin : data.m_selected) {
        if (bin.m_info.kind != VlCovBinKind::KIND_NORMAL) continue;
        for (uint32_t word = 0; word < data.m_words; ++word) bin.m_mask[word] &= ~excluded[word];
    }
    data.m_selected.erase(std::remove_if(data.m_selected.begin(), data.m_selected.end(),
                                         [](const Layout::Selected& bin) {
                                             return std::all_of(
                                                 bin.m_mask.begin(), bin.m_mask.end(),
                                                 [](uint64_t word) { return !word; });
                                         }),
                          data.m_selected.end());
    if (data.m_selected.empty()) return;
    Layout::Mask occupied(data.m_words, 0);
    uint64_t binWords = 0;
    for (const Layout::Selected& bin : data.m_selected) {
        for (uint32_t word = 0; word < data.m_words; ++word) {
            occupied[word] |= bin.m_mask[word];
            if (bin.m_mask[word]) ++binWords;
        }
    }
    // Selection masks have no bits past m_tuples, so this counts the automatic bins.
    uint32_t autoBins = data.m_tuples;
    for (const uint64_t word : occupied) autoBins -= VL_COUNTONES_Q(word);
    data.m_autoBins.resize(autoBins);
    data.m_bins.resize(data.m_selected.size());
    data.m_hitWords.resize(data.m_words);
    data.m_binWords.resize(binWords);
    data.m_selections.resize(data.m_selected.size() * data.m_words);
    data.m_explicitData = {{data.m_bins.data(), data.m_bins.size()},
                           data.m_hitWords.data(),
                           {data.m_autoBins.data(), data.m_autoBins.size()},
                           {data.m_binWords.data(), data.m_binWords.size()},
                           data.m_selections.data()};
    bindStorage(data.m_dimensions.data(), data.m_counts.data(), &data.m_explicitData);
    for (const Layout::Selected& bin : data.m_selected) {
        addBinImpl(bin.m_info.kind, bin.m_mask.data(), data.m_words, bin.m_info.namep,
                   bin.m_info.filep, bin.m_info.line, bin.m_info.col, bin.m_info.iffIndex);
    }
    VlCoverCross::finalizeBins();
    data.m_selected.clear();
    data.m_stack.clear();
}

//=============================================================================
// VlCovergroupInst

// IEEE 1800-2023 19.11: coverage is the weighted average of the contributions; with a zero
// denominator it is 0.0, or 100.0 when the covergroup's weight is zero
static double _vl_cov_calculate(double weighted, double weights, int32_t weight) VL_PURE {
    if (weights == 0.0) return weight ? 0.0 : 100.0;
    return weighted / weights;
}

// IEEE 1800-2023 19.7: a weight shall be non-negative.  A negative constant is rejected when
// verilating; a weight that is negative only at run time is reported as it is loaded, and
// counts as zero, so that coverage stays within 0..100.
static int32_t _vl_cov_load_weight(const char* optionp, IData value,
                                   VlFileLineDebug fileline) VL_MT_SAFE {
    const int32_t weight = static_cast<int32_t>(value);
    if (VL_LIKELY(weight >= 0)) return weight;
    const char* filep = "";  // VlFileLineDebug keeps the location only under VL_DEBUG
    int line = 0;
#ifdef VL_DEBUG
    filep = fileline.filename();
    line = fileline.lineno();
#else
    static_cast<void>(fileline);
#endif
    const std::string where = filep && filep[0]
                                  ? std::string{filep} + ":" + std::to_string(line) + ": "
                                  : std::string{};
    VL_PRINTF_MT("%%Error: %sCoverage option '%s' is set to negative value '%d';"
                 " weights must be non-negative (IEEE 1800-2023 19.7)\n",
                 where.c_str(), optionp, static_cast<int>(weight));
    VL_STOP_MT(filep, line, "");
    return 0;
}

void VlCoverpointIf::weight(uint32_t value, VlFileLineDebug fileline) {
    m_weight = _vl_cov_load_weight("option.weight", value, fileline);
}

VlCoverCrossDyn* VlCovergroupInst::addCrossDyn() {
    VlCoverCrossDyn* const cxp = new VlCoverCrossDyn{};
    m_items.emplace_back(cxp);
    return cxp;
}

void VlCovergroupInst::loadWeight() {
    // Only a new value, so that each negative value is reported once
    if (!m_weightp || *m_weightp == m_loadedWeight) return;
    m_loadedWeight = *m_weightp;
    m_weight = _vl_cov_load_weight("option.weight", m_loadedWeight, m_fileline);
}

std::pair<double, double> VlCovergroupInst::coverageSums() const {
    double weighted = 0.0;
    double weights = 0.0;
    for (const auto& itemp : m_items) {
        double covered = 0.0;
        double total = 0.0;
        itemp->coverageParts(covered, total);
        if (total == 0.0) continue;  // No bins: excluded from both sums
        weighted += itemp->weight() * (covered / total);
        weights += itemp->weight();
    }
    return {100.0 * weighted, weights};
}

double VlCovergroupInst::coverage() {
    loadWeight();
    const std::pair<double, double> sums = coverageSums();
    return _vl_cov_calculate(sums.first, sums.second, m_weight);
}

//=============================================================================
// VlCovergroupType / VlCovRegistry

VlCovergroupInst* VlCovergroupType::newInstance() {
    VlCovergroupInst* const instp = new VlCovergroupInst{this, m_nextInstId++};
    m_insts.emplace_back(instp);
#if !VM_COVERAGE
    instp->m_slot = static_cast<uint32_t>(m_insts.size() - 1);
#endif
    ++m_createdInsts;
    return instp;
}

void VlCovergroupType::foldResidue(VlCovergroupInst* instp) {
    const std::pair<double, double> sums = instp->coverageSums();
    // Nothing coverable: excluded from both sums, so it moves neither the mean
    // nor the denominator.  Never-sampled is different: it has bins, none hit,
    // and folds as 0%.
    if (sums.second == 0.0) return;
    // The same weighted average of the items as get_inst_coverage(), so that a live
    // instance and the same instance one delta after death never disagree.  With the
    // weight last loaded: the object that lent option.weight is gone, and nothing may
    // be reported here, as this can run after ~VerilatedContext (see ~VlCovRegistry).
    const int32_t weight = instp->weight();
    m_retired.sumCoverage += weight * (sums.first / sums.second);
    m_retired.sumWeight += weight;
    ++m_retired.count;
}

// Runs when the last handle to instp drops, possibly after ~VlCovRegistry, on a
// type teardown leaked to keep this valid (see ~VlCovRegistry).  That late case
// needs no special handling: the leaked type is self-consistent.
void VlCovergroupType::retire(VlCovergroupInst* instp) {
    foldResidue(instp);  // Before unlink: reads instp's items, freed below

#if VM_COVERAGE
    // registerBins() gave the coverage database raw &m_counts[i], read at
    // write() time.  Keep the node alive, marked dead so it counts as neither
    // live nor residue.  Freeing here needs the coverage-writer rework.
    instp->m_retained = true;
#else
    // Move out first, so the node destructs at end of scope with m_insts
    // already consistent rather than mid-swap.
    const uint32_t slot = instp->m_slot;
    const std::unique_ptr<VlCovergroupInst> dying = std::move(m_insts[slot]);
    if (slot != m_insts.size() - 1) {
        m_insts[slot] = std::move(m_insts.back());
        m_insts[slot]->m_slot = slot;  // Moved node's slot is now stale
    }
    m_insts.pop_back();
#endif
}

uint32_t VlCovergroupType::liveInstanceCount() const {
    uint32_t live = 0;
    // Under VM_COVERAGE m_insts also holds retained (dead) nodes; otherwise
    // retained() is never set and this equals m_insts.size().
    for (const auto& instp : m_insts) {
        if (!instp->retained()) ++live;
    }
    return live;
}

bool VlCovergroupType::anyAttached() const {
    for (const auto& instp : m_insts) {
        if (instp->m_attachCount > 0) return true;
    }
    return false;
}

double VlCovergroupType::coverage(IData typeWeight, VlFileLineDebug fileline) {
    if (typeWeight != m_loadedTypeWeight) {  // Only a new value, as in loadWeight()
        m_loadedTypeWeight = typeWeight;
        m_typeWeight = _vl_cov_load_weight("type_option.weight", typeWeight, fileline);
    }
    // Instances that have died still count: their contribution is the residue
    double sumCoverage = m_retired.sumCoverage;
    double sumWeight = m_retired.sumWeight;
    for (const auto& instp : m_insts) {
        if (instp->retained()) continue;  // Already folded into the residue
        instp->loadWeight();
        const std::pair<double, double> sums = instp->coverageSums();
        if (sums.second == 0.0) continue;  // A covergroup without coverage does not contribute
        sumCoverage += instp->weight() * (sums.first / sums.second);
        sumWeight += instp->weight();
    }
    return _vl_cov_calculate(sumCoverage, sumWeight, m_typeWeight);
}

double VlCovergroupType::retiredCoverage() const {
    if (m_retired.count == 0 || m_retired.sumWeight == 0.0) return -1.0;
    return m_retired.sumCoverage / m_retired.sumWeight;
}

// Defined here, not in verilated.cpp, so that the registry costs nothing in a model with no
// covergroups: this file is linked only when covergroups are used (or --coverage is on).
// Mirrors VerilatedContext::coveragep(), which lives in verilated_cov.cpp for the same reason.
VlCovRegistry* VerilatedContext::covergroupRegistryp() VL_MT_SAFE {
    static VerilatedMutex s_mutex;
    // cppcheck-suppress identicalInnerCondition
    if (VL_UNLIKELY(!m_covergroupsp)) {
        const VerilatedLockGuard lock{s_mutex};
        // cppcheck-suppress identicalInnerCondition
        if (VL_LIKELY(!m_covergroupsp)) {  // LCOV_EXCL_LINE // Not redundant, prevents race
            m_covergroupsp.reset(new VlCovRegistry{});
        }
    }
    return static_cast<VlCovRegistry*>(m_covergroupsp.get());
}

VlCovergroupType* VlCovRegistry::findOrCreateType(const char* typeName) {
    VlCovergroupType*& typep = m_byName[typeName];
    if (!typep) {  // First use of this type
        m_types.emplace_back(new VlCovergroupType{});
        typep = m_types.back().get();
    }
    return typep;
}

VlCovergroupInst* VlCovRegistry::newCovergroupInst(const char* typeName) {
    return findOrCreateType(typeName)->newInstance();
}

double VlCovRegistry::typeCoverage(const char* typeName, IData typeWeight,
                                   VlFileLineDebug fileline) {
    // Also for a type never instantiated, whose node then remembers type_option.weight
    return findOrCreateType(typeName)->coverage(typeWeight, fileline);
}

// A covergroup object can outlive the registry: models must be destroyed before
// their context, and a user who gets that backwards drops covergroup handles
// after ~VerilatedContext.  Those handle destructors call attachDec(), which
// reads the instance node and its type -- so freeing the nodes here is itself
// what would make the wrong ordering a use-after-free, and a "retirement
// disarmed" flag could not help.  Instead, leak any type that still has an
// attached node, keeping the type, its nodes and their items valid; the late
// retire() then frees the nodes itself, so only the type object leaks.
VlCovRegistry::~VlCovRegistry() {
    for (auto& typep : m_types) {
        // Normally nothing is still attached; if something is, the model
        // outlived its context and those handles still reach this type.
        if (VL_UNLIKELY(typep->anyAttached())) {
            VlCovergroupType* const leakedp = typep.release();
            static_cast<void>(leakedp);  // Deliberate leak
        }
    }
}

VlCovergroupType* VlCovRegistry::findType(const char* typeName) const {
    const auto it = m_byName.find(typeName);
    return it == m_byName.end() ? nullptr : it->second;
}

uint32_t VlCovRegistry::liveInstanceCount() const {
    uint32_t total = 0;
    for (const auto& typep : m_types) total += typep->liveInstanceCount();
    return total;
}

uint32_t VlCovRegistry::createdInstanceCount() const {
    uint32_t total = 0;
    for (const auto& typep : m_types) total += typep->createdInstanceCount();
    return total;
}

uint32_t VlCovRegistry::liveInstanceCount(const char* typeName) const {
    const VlCovergroupType* const typep = findType(typeName);
    return typep ? typep->liveInstanceCount() : 0;
}

uint32_t VlCovRegistry::createdInstanceCount(const char* typeName) const {
    const VlCovergroupType* const typep = findType(typeName);
    return typep ? typep->createdInstanceCount() : 0;
}

uint32_t VlCovRegistry::retiredInstanceCount(const char* typeName) const {
    const VlCovergroupType* const typep = findType(typeName);
    return typep ? typep->retiredInstanceCount() : 0;
}

double VlCovRegistry::retiredCoverage(const char* typeName) const {
    const VlCovergroupType* const typep = findType(typeName);
    return typep ? typep->retiredCoverage() : -1.0;
}
