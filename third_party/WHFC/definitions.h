#pragma once

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <limits>
#include <random>
#include <string>
#include "logger.h"
#include "util/range.h"
#include "util/tagged_integer.h"
#include "util/timer.h"

template<typename int1, typename int2>
int1 ceil_div(int1 numerator, int2 denominator) {
    return numerator / denominator + (numerator % denominator == 0 ? 0 : 1);
}

namespace whfc {
    // every tagged integer takes as first template argument an integer tag, which is unique to its type
    using Node = TaggedInteger<0, uint32_t, std::numeric_limits<uint32_t>::max(), 0>;
    static constexpr Node invalidNode = Node::Invalid();
    using Hyperedge = TaggedInteger<1, uint32_t, std::numeric_limits<uint32_t>::max(), 0>;
    static constexpr Hyperedge invalidHyperedge = Hyperedge::Invalid();

    using PinIndex = TaggedInteger<7, uint32_t, std::numeric_limits<uint32_t>::max(), 0>;
    using InHeIndex = TaggedInteger<8, uint32_t, std::numeric_limits<uint32_t>::max(), 0>;

    using NodeWeight = uint32_t;
    static constexpr NodeWeight invalidWeight = std::numeric_limits<NodeWeight>::max();
    using HyperedgeWeight = uint32_t;

    using Flow = int32_t;
    static constexpr Flow maxFlow = std::numeric_limits<int32_t>::max();

    static_assert(sizeof(Node) == sizeof(uint32_t));
    static_assert(sizeof(Hyperedge) == sizeof(uint32_t));
    static_assert(sizeof(PinIndex) == sizeof(uint32_t));
    static_assert(sizeof(InHeIndex) == sizeof(uint32_t));

    using HopDistance = int32_t;

    using Index = uint32_t;
    static constexpr Index invalidIndex = std::numeric_limits<uint32_t>::max();

} // namespace whfc
