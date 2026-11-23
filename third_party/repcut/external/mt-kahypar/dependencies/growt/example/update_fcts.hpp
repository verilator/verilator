#ifndef UPDATE_FCTS_H
#define UPDATE_FCTS_H

#include <atomic>
#include <cstdint>
#include <type_traits>

namespace growt
{
namespace example
{

struct Increment
{
    using mapped_type = uint64_t;

    mapped_type operator()(mapped_type& lhs, const mapped_type& rhs) const
    {
        return lhs += rhs;
    }

    // an atomic implementation can improve the performance of updates in .sGrow
    // this will be detected automatically
    mapped_type atomic(mapped_type& lhs, const mapped_type& rhs) const
    {
        return std::atomic_ref<mapped_type>(lhs).fetch_add(rhs);
    }

    // Only necessary for JunctionWrapper (not needed)
    using junction_compatible = std::false_type;
};

struct Overwrite
{
    using mapped_type = uint64_t;

    mapped_type operator()(mapped_type& lhs, const mapped_type& rhs) const
    {
        lhs = rhs;
        return rhs;
    }

    // an atomic implementation can improve the performance of updates in .sGrow
    // this will be detected automatically
    mapped_type atomic(mapped_type& lhs, const mapped_type& rhs) const
    {

        lhs = rhs;
        return rhs;
    }

    // Only necessary for JunctionWrapper (not needed)
    using junction_compatible = std::true_type;
};

} // namespace example
} // namespace growt

#endif // UPDATE_FCTS_H
