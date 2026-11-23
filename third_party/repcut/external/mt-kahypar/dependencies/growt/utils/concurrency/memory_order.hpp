#pragma once

#include <atomic>

namespace utils_tm
{
namespace concurrency_tm
{
#ifndef MAKE_SEQ_CST // THIS SWITCH CAN CHANGE ALL MEMORY ORDERS TO SEQUENTIAL
                     // CONSISTENCY
static constexpr std::memory_order mo_relaxed = std::memory_order_relaxed;
static constexpr std::memory_order mo_acquire = std::memory_order_acquire;
static constexpr std::memory_order mo_release = std::memory_order_release;
static constexpr std::memory_order mo_acq_rel = std::memory_order_acq_rel;
static constexpr std::memory_order mo_seq_cst = std::memory_order_seq_cst;
#else
static constexpr std::memory_order mo_relaxed = std::memory_order_seq_cst;
static constexpr std::memory_order mo_acquire = std::memory_order_seq_cst;
static constexpr std::memory_order mo_release = std::memory_order_seq_cst;
static constexpr std::memory_order mo_acq_rel = std::memory_order_seq_cst;
static constexpr std::memory_order mo_seq_cst = std::memory_order_seq_cst;
#endif

struct conservative_memory_order_policy
{
    static constexpr std::memory_order relaxed = std::memory_order_seq_cst;
    static constexpr std::memory_order acquire = std::memory_order_seq_cst;
    static constexpr std::memory_order release = std::memory_order_seq_cst;
    static constexpr std::memory_order acq_rel = std::memory_order_seq_cst;
    static constexpr std::memory_order seq_cst = std::memory_order_seq_cst;
};

struct standard_memory_order_policy
{
    static constexpr std::memory_order relaxed = std::memory_order_relaxed;
    static constexpr std::memory_order acquire = std::memory_order_acquire;
    static constexpr std::memory_order release = std::memory_order_release;
    static constexpr std::memory_order acq_rel = std::memory_order_acq_rel;
    static constexpr std::memory_order seq_cst = std::memory_order_seq_cst;
};

struct relaxed_memory_order_policy
{
    static constexpr std::memory_order relaxed = std::memory_order_relaxed;
    static constexpr std::memory_order acquire = std::memory_order_relaxed;
    static constexpr std::memory_order release = std::memory_order_relaxed;
    static constexpr std::memory_order acq_rel = std::memory_order_relaxed;
    static constexpr std::memory_order seq_cst = std::memory_order_relaxed;
};

} // namespace concurrency_tm
} // namespace utils_tm
