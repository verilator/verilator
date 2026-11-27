#pragma once

#include "cstddef"

enum class hmod : size_t
{
    neutral       = 0,
    growable      = 1,
    deletion      = 2,
    ref_integrity = 4,
    sync          = 8,
    circular_map  = 16,
    circular_prob = 32
};

template <hmod... Mods> class mod_aggregator
{
  public:
    static constexpr size_t mod_descriptor =
        (size_t(0) | ... | static_cast<size_t>(Mods));

  public:
    template <hmod Ask> static constexpr bool is()
    {
        auto ask = static_cast<size_t>(Ask);
        return mod_descriptor & ask;
    }

    template <hmod... Asks> static constexpr bool all()
    {
        using ask_aggregator            = mod_aggregator<Mods...>;
        constexpr size_t ask_descriptor = ask_aggregator::mod_descriptor;
        return (ask_descriptor & mod_descriptor) == ask_descriptor;
    }
};
