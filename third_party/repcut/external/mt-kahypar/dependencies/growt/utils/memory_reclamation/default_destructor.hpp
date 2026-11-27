#pragma once

namespace utils_tm
{
namespace reclamation_tm
{

template <class T>
class default_destructor
{
  public:
    template <class U>
    struct rebind
    {
        using other = default_destructor<U>;
    };

    template <class ReclHandle>
    void destroy(ReclHandle& h, T* ptr) const
    {
        h.delete_raw(ptr);
    }
};
} // namespace reclamation_tm
} // namespace utils_tm
