// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
#include "repcut_serial.h"

#include <atomic>
#include <cassert>
#include <cstdint>
#include <limits>
#include <numeric>
#include <tbb/concurrent_vector.h>
#include <tbb/enumerable_thread_specific.h>
#include <tbb/parallel_for.h>
#include <tbb/parallel_scan.h>
#include <vector>

static void require(bool value)
{
    if (!value)
        throw std::runtime_error("Serial primitive test failed");
}
struct Scan
{
    std::vector<int>& values;
    int sum = 0;
    template <class Tag> void operator()(const tbb::blocked_range<size_t>& range, Tag)
    {
        require(Tag::is_final_scan());
        for (size_t i = range.begin(); i < range.end(); ++i) {
            sum += values[i];
            values[i] = sum;
        }
    }
};
struct Immovable
{
    std::atomic<int> count{7};
};
template <class T> static void checkReferences()
{
    for (const T initial : {std::numeric_limits<T>::min(), std::numeric_limits<T>::max(), T{0}, T{1}}) {
        for (const T delta : {std::numeric_limits<T>::min(), std::numeric_limits<T>::max(), T{0}, T{1}}) {
            T value = initial;
            const repcut_serial::Ref ref{value};
            std::atomic<T> atomic{initial};
            require(ref.fetch_add(delta) == atomic.fetch_add(delta));
            require(ref.load() == atomic.load());
            require(ref.fetch_sub(delta) == atomic.fetch_sub(delta));
            require(ref.load() == atomic.load());
            require(ref.fetch_xor(delta) == atomic.fetch_xor(delta));
            require(ref.load() == atomic.load());
            require(ref.exchange(initial) == atomic.exchange(initial));
            require(ref.load() == atomic.load());
            T expected = initial;
            require(ref.compare_exchange_strong(expected, delta, std::memory_order_acq_rel, std::memory_order_relaxed));
            require(expected == initial && value == delta);
            ref.store(initial, std::memory_order_release);
            require(ref.load(std::memory_order_acquire) == initial);
        }
    }
}
static void checkSerialReferences()
{
    checkReferences<int8_t>();
    checkReferences<uint8_t>();
    checkReferences<int16_t>();
    checkReferences<uint16_t>();
    checkReferences<int32_t>();
    checkReferences<uint32_t>();
    checkReferences<int64_t>();
    checkReferences<uint64_t>();
    enum class State : uint8_t { first, second, third };
    State value = State::first;
    const repcut_serial::Ref ref{value};
    const repcut_serial::Ref alias{value};
    State expected = State::second;
    require(!ref.compare_exchange_strong(expected, State::third));
    require(expected == State::first && value == State::first);
    require(ref.compare_exchange_strong(expected, State::second));
    require(expected == State::first && alias.load() == State::second);
    require(alias.exchange(State::third) == State::second && ref.load() == State::third);
}
static void checkBits()
{
    static_assert(repcut_serial::popcount64(0) == 0);
    static_assert(repcut_serial::popcount64(UINT64_MAX) == 64);
    static_assert(repcut_serial::countrZero64(0) == 64);
    static_assert(repcut_serial::countrZero64(UINT64_C(1) << 63) == 63);
    for (unsigned bit = 0; bit < 64; ++bit) {
        const uint64_t value = UINT64_C(1) << bit;
        require(repcut_serial::popcount64(value) == 1);
        require(repcut_serial::countrZero64(value) == static_cast<int>(bit));
        require(repcut_serial::popcount64(~value) == 63);
    }
    uint64_t state = 42;
    for (int i = 0; i < 1000; ++i) {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        int count = 0;
        for (uint64_t bits = state; bits; bits >>= 1)
            count += bits & 1;
        int zeros = 0;
        for (uint64_t bits = state; zeros < 64 && !(bits & 1); bits >>= 1)
            ++zeros;
        require(repcut_serial::popcount64(state) == count);
        require(repcut_serial::countrZero64(state) == zeros);
    }
}
int main()
{
    checkSerialReferences();
    checkBits();
    int total = 0;
    tbb::parallel_for(0, 5, [&](int i) { total += i; });
    tbb::parallel_for(0, 5, 2, [&](int i) { total += i; });
    require(total == 16);
    tbb::parallel_for(
        tbb::blocked_range<int>(0, 3), [&](auto& range) { total += range.size(); }, tbb::static_partitioner{});
    require(total == 19);
    std::vector<int> values{1, 2, 3, 4};
    Scan scan{values};
    tbb::parallel_scan(tbb::blocked_range<size_t>(0, values.size()), scan);
    require(values == std::vector<int>({1, 3, 6, 10}) && scan.sum == 10);
    require(tbb::parallel_reduce(
                tbb::blocked_range<int>(0, 5), 0,
                [](const auto& range, int sum) {
                    for (int i = range.begin(); i < range.end(); ++i)
                        sum += i;
                    return sum;
                },
                std::plus<>()) == 10);
    int creations = 0;
    tbb::enumerable_thread_specific<Immovable> local([&] {
        ++creations;
        return Immovable{};
    });
    require(local.empty());
    bool exists = true;
    require(local.local(exists).count == 7 && !exists && creations == 1);
    local.local(exists).count = 11;
    require(exists && local.size() == 1 && local.begin()->count == 11);
    local.clear();
    require(local.empty());
    require(local.local().count == 7 && creations == 2);
    tbb::concurrent_vector<Immovable> stable;
    stable.resize(1);
    auto* first = &stable[0];
    stable.resize(1000);
    require(first == &stable[0] && first->count == 7);
    tbb::concurrent_queue<int> queue;
    int result = 0;
    queue.push(3);
    queue.push(8);
    require(queue.try_pop(result) && result == 3);
    require(queue.try_pop(result) && result == 8 && !queue.try_pop(result));
    tbb::task_group tasks;
    tasks.run([&] { ++total; });
    tasks.wait();
    require(total == 20);
    require(tbb::this_task_arena::max_concurrency() == 1 && tbb::this_task_arena::current_thread_index() == 0);
    bool rejected = false;
    try {
        tbb::global_control guard(tbb::global_control::max_allowed_parallelism, 2);
    }
    catch (const std::invalid_argument&) {
        rejected = true;
    }
    require(rejected);
}
