// Serial execution primitives for the bundled Mt-KaHyPar build.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
// This is the subset used by the pinned partitioner, not a general TBB implementation.
// Only one partitioning call may be active; librepcut enforces that boundary.
#pragma once

#ifndef REPCUT_SERIAL_PARTITIONER
#error This adapter is only for the serial bundled partitioner
#endif

#include <algorithm>
#include <chrono>
#include <cstdlib>
#include <deque>
#include <functional>
#include <iterator>
#include <memory>
#include <stdexcept>
#include <tuple>
#include <type_traits>
#include <unordered_map>
#include <utility>

namespace tbb {
    struct split
    {
    };
    struct static_partitioner
    {
    };
    struct pre_scan_tag
    {
        static constexpr bool is_final_scan() { return false; }
    };
    struct final_scan_tag
    {
        static constexpr bool is_final_scan() { return true; }
    };

    template <class T> class blocked_range
    {
        T first_, last_;

    public:
        blocked_range(T first, T last, size_t = 1) : first_(first), last_(last) {}
        T begin() const { return first_; }
        T end() const { return last_; }
        size_t size() const { return static_cast<size_t>(last_ - first_); }
        bool empty() const { return first_ == last_; }
        bool is_divisible() const { return false; }
    };

    template <class Range, class Body, class... Policy, std::enable_if_t<!std::is_integral_v<Range>, int> = 0>
    void parallel_for(Range range, const Body& body, const Policy&...)
    {
        if (!range.empty())
            body(range);
    }
    template <class Index, class Body, class... Policy, std::enable_if_t<std::is_integral_v<Index>, int> = 0>
    void parallel_for(Index first, Index last, const Body& body, const Policy&...)
    {
        for (; first < last; ++first)
            body(first);
    }
    template <class Index, class Step, class Body, std::enable_if_t<std::is_integral_v<Step>, int> = 0>
    void parallel_for(Index first, Index last, Step step, const Body& body)
    {
        if (step <= 0)
            throw std::invalid_argument("Serial loop step must be positive");
        for (; first < last; first += step)
            body(first);
    }
    template <class Range, class Body> void parallel_for_each(Range& range, const Body& body)
    {
        for (auto& value : range)
            body(value);
    }
    template <class Iterator, class Body> void parallel_for_each(Iterator first, Iterator last, const Body& body)
    {
        for (; first != last; ++first)
            body(*first);
    }
    template <class... Body> void parallel_invoke(Body&&... body)
    {
        (body(), ...);
    }
    template <class Iterator, class... Compare> void parallel_sort(Iterator first, Iterator last, Compare... compare)
    {
        std::sort(first, last, compare...);
    }
    template <class Range, class... Compare>
    auto parallel_sort(Range& range, Compare... compare) -> decltype(std::begin(range), std::end(range), void())
    {
        std::sort(std::begin(range), std::end(range), compare...);
    }
    template <class Range, class T, class Body, class Join, class... Policy>
    T parallel_reduce(const Range& range, T identity, const Body& body, const Join&, const Policy&...)
    {
        return range.empty() ? identity : body(range, identity);
    }
    template <class... Args> auto parallel_deterministic_reduce(Args&&... args)
    {
        return parallel_reduce(std::forward<Args>(args)...);
    }
    template <class Range, class Body> void parallel_scan(const Range& range, Body& body)
    {
        if (!range.empty())
            body(range, final_scan_tag{});
    }
    template <class Range, class T, class Body, class Join>
    T parallel_scan(const Range& range, T identity, const Body& body, const Join&)
    {
        return range.empty() ? identity : body(range, identity, true);
    }

    // A distinct allocator type preserves overloads for Mt-KaHyPar's scalable vectors.
    template <class T> struct tbb_allocator
    {
        using value_type = T;
        using is_always_equal = std::true_type;
        using propagate_on_container_move_assignment = std::true_type;
        tbb_allocator() = default;
        template <class U> tbb_allocator(const tbb_allocator<U>&) {}
        T* allocate(size_t n) { return std::allocator<T>{}.allocate(n); }
        void deallocate(T* p, size_t n) { std::allocator<T>{}.deallocate(p, n); }
        template <class U> bool operator==(const tbb_allocator<U>&) const { return true; }
        template <class U> bool operator!=(const tbb_allocator<U>&) const { return false; }
    };
    template <class T> using scalable_allocator = tbb_allocator<T>;
    // Only used as an ETS policy; the serial ETS owns one normally aligned object.
    template <class T> using cache_aligned_allocator = tbb_allocator<T>;

    // Stable references during growth match the concurrent_vector operations used here.
    template <class T, class Allocator = tbb_allocator<T>> class concurrent_vector : public std::deque<T, Allocator>
    {
        using Base = std::deque<T, Allocator>;

    public:
        using Base::Base;
        void reserve(size_t) {}
        size_t capacity() const { return this->size(); }
        auto grow_by(size_t n)
        {
            const auto start = this->size();
            this->resize(start + n);
            return this->begin() + start;
        }
        auto grow_to_at_least(size_t n)
        {
            const auto start = this->size();
            if (n > start)
                this->resize(n);
            return this->begin() + std::min(start, n);
        }
    };
    template <class T> class concurrent_queue
    {
        std::deque<T> values_;

    public:
        template <class U> void push(U&& value) { values_.push_back(std::forward<U>(value)); }
        bool try_pop(T& value)
        {
            if (values_.empty())
                return false;
            value = std::move(values_.front());
            values_.pop_front();
            return true;
        }
        bool empty() const { return values_.empty(); }
        size_t unsafe_size() const { return values_.size(); }
        void clear() { values_.clear(); }
    };
    template <class Key, class T, class Hash = std::hash<Key>, class Equal = std::equal_to<Key>>
    using concurrent_unordered_map = std::unordered_map<Key, T, Hash, Equal>;

    enum ets_key_usage_type { ets_no_key, ets_key_per_instance };
    template <class T, class Allocator = tbb_allocator<T>, ets_key_usage_type = ets_no_key>
    class enumerable_thread_specific
    {
        std::function<std::unique_ptr<T>()> create_;
        std::unique_ptr<T> value_;
        template <class... Args> void initialize(Args&&... args)
        {
            create_ = [values = std::make_tuple(std::forward<Args>(args)...)] {
                return std::apply([](const auto&... values) { return std::make_unique<T>(values...); }, values);
            };
        }
        template <class U> class Iterator
        {
            U* value_;

        public:
            using iterator_category = std::forward_iterator_tag;
            using value_type = U;
            using difference_type = std::ptrdiff_t;
            using pointer = U*;
            using reference = U&;
            explicit Iterator(U* value = nullptr) : value_(value) {}
            U& operator*() const { return *value_; }
            U* operator->() const { return value_; }
            Iterator& operator++()
            {
                value_ = nullptr;
                return *this;
            }
            Iterator operator++(int)
            {
                Iterator old = *this;
                ++*this;
                return old;
            }
            bool operator==(const Iterator& other) const { return value_ == other.value_; }
            bool operator!=(const Iterator& other) const { return !(*this == other); }
            bool operator<(const Iterator& other) const { return value_ && !other.value_; }
            difference_type operator-(const Iterator& other) const
            {
                return static_cast<difference_type>(!value_) - static_cast<difference_type>(!other.value_);
            }
        };

    public:
        using iterator = Iterator<T>;
        using const_iterator = Iterator<const T>;
        using range_type = blocked_range<iterator>;
        using const_range_type = blocked_range<const_iterator>;
        range_type range() { return {begin(), end()}; }
        const_range_type range() const { return {begin(), end()}; }
        enumerable_thread_specific() { initialize(); }
        template <class Arg, std::enable_if_t<!std::is_same_v<std::decay_t<Arg>, enumerable_thread_specific>, int> = 0>
        enumerable_thread_specific(Arg&& arg)
        {
            if constexpr (std::is_invocable_r_v<T, Arg>)
                create_ = [factory = std::forward<Arg>(arg)] { return std::unique_ptr<T>(new T(factory())); };
            else
                initialize(std::forward<Arg>(arg));
        }
        template <class A, class B, class... Args> enumerable_thread_specific(A&& a, B&& b, Args&&... args)
        {
            initialize(std::forward<A>(a), std::forward<B>(b), std::forward<Args>(args)...);
        }
        enumerable_thread_specific(enumerable_thread_specific&&) = default;
        enumerable_thread_specific& operator=(enumerable_thread_specific&&) = default;
        enumerable_thread_specific(const enumerable_thread_specific& other) : create_(other.create_)
        {
            if (other.value_)
                value_ = std::make_unique<T>(*other.value_);
        }
        enumerable_thread_specific& operator=(const enumerable_thread_specific& other)
        {
            if (this != &other) {
                enumerable_thread_specific copy(other);
                swap(copy);
            }
            return *this;
        }
        T& local()
        {
            if (!value_)
                value_ = create_();
            return *value_;
        }
        T& local(bool& exists)
        {
            exists = static_cast<bool>(value_);
            return local();
        }
        void clear() { value_.reset(); }
        bool empty() const { return !value_; }
        size_t size() const { return value_ ? 1 : 0; }
        iterator begin() { return iterator(value_.get()); }
        iterator end() { return iterator(); }
        const_iterator begin() const { return const_iterator(value_.get()); }
        const_iterator end() const { return const_iterator(); }
        template <class F> T combine(F) { return value_ ? *value_ : T{}; }
        template <class F> void combine_each(F f)
        {
            if (value_)
                f(*value_);
        }
        void swap(enumerable_thread_specific& other)
        {
            create_.swap(other.create_);
            value_.swap(other.value_);
        }
    };

    class task_group
    {
    public:
        ~task_group() { wait(); }
        template <class F> void run(F&& f) { f(); }
        void wait() {}
        template <class F> void run_and_wait(F&& f) { f(); }
    };
    namespace this_task_arena {
        inline int current_thread_index()
        {
            return 0;
        }
        inline int max_concurrency()
        {
            return 1;
        }
        template <class F> decltype(auto) isolate(F&& f)
        {
            return f();
        }
    } // namespace this_task_arena
    class global_control
    {
    public:
        enum parameter { max_allowed_parallelism };
        global_control(parameter, size_t threads)
        {
            if (threads != 1)
                throw std::invalid_argument("The bundled partitioner requires one thread");
        }
        static size_t active_value(parameter) { return 1; }
    };
    class tick_count
    {
        using Clock = std::chrono::steady_clock;
        Clock::time_point value_;

    public:
        static tick_count now()
        {
            tick_count result;
            result.value_ = Clock::now();
            return result;
        }
        struct interval_t
        {
            Clock::duration value;
            double seconds() const { return std::chrono::duration<double>(value).count(); }
        };
        friend interval_t operator-(tick_count a, tick_count b) { return {a.value_ - b.value_}; }
    };
} // namespace tbb

inline void* scalable_malloc(size_t n)
{
    return std::malloc(n);
}
inline void* scalable_calloc(size_t n, size_t size)
{
    return std::calloc(n, size);
}
inline void scalable_free(void* p)
{
    std::free(p);
}
