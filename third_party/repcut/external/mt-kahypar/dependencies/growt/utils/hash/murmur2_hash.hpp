#pragma once

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>


namespace utils_tm
{
namespace hash_tm
{

struct murmur2_hash
{
    static constexpr std::string_view name               = "murmur2";
    static constexpr size_t           significant_digits = 64;


    murmur2_hash(size_t s = 1203989050u) : seed(s) {}

    size_t seed;

    inline uint64_t
    MurmurHash64A(const void* key, int len, unsigned int seed) const
    {
        const uint64_t m = 0xc6a4a7935bd1e995;
        const int      r = 47;

        uint64_t h = seed ^ (len * m);

        const uint64_t* data = (const uint64_t*)key;
        const uint64_t* end  = data + (len / 8);

        while (data != end)
        {
            uint64_t k = *data++;

            k *= m;
            k ^= k >> r;
            k *= m;

            h ^= k;
            h *= m;
        }

        const unsigned char* data2 = (const unsigned char*)data;

        switch (len & 7)
        {
        case 7:
            h ^= uint64_t(data2[6]) << 48;
            [[fallthrough]];
        case 6:
            h ^= uint64_t(data2[5]) << 40;
            [[fallthrough]];
        case 5:
            h ^= uint64_t(data2[4]) << 32;
            [[fallthrough]];
        case 4:
            h ^= uint64_t(data2[3]) << 24;
            [[fallthrough]];
        case 3:
            h ^= uint64_t(data2[2]) << 16;
            [[fallthrough]];
        case 2:
            h ^= uint64_t(data2[1]) << 8;
            [[fallthrough]];
        case 1:
            h ^= uint64_t(data2[0]);
            h *= m;
        };

        h ^= h >> r;
        h *= m;
        h ^= h >> r;

        return h;
    }

    inline uint64_t operator()(const uint64_t k) const
    {
        auto local = k;
        return MurmurHash64A(&local, 8, seed);
    }

    inline uint64_t operator()(const uint32_t k) const
    {
        auto local = k;
        return MurmurHash64A(&local, 4, seed);
    }


    // targeted at string type classes i.e. data pointer + size
    template <class Type>
    inline uint64_t operator()(const Type& k) const
    {
        return MurmurHash64A(k.data(), k.size(), seed);
    }
};

} // namespace hash_tm
} // namespace utils_tm
