#pragma once

/*******************************************************************************
 * default_hash.hpp
 *
 * Here we choose one of the included wrappers for common hash functions
 * at compile time according to a defined variable
 *
 * If nothing else is defined, XXHash is chosen as default_hash function.
 *
 * If you have any problems with third party codes try defining MURMUR2.
 * (its implementation is offered with this library)
 *
 * Part of my utils library utils_tm - https://github.com/TooBiased/utils_tm.git
 *
 * Copyright (C) 2019 Tobias Maier <t.maier@kit.edu>
 *
 * All rights reserved. Published under the BSD-2 license in the LICENSE file.
 ******************************************************************************/

#if (!(defined(CRC) || defined(MURMUR2) || defined(MURMUR3) || \
       defined(XXHASH) || defined(XXH3)))
#define MURMUR2
#endif // NO HASH DEFINED

#ifdef CRC
#include "hash/crc_hash.hpp"
#define HASHFCT utils_tm::hash_tm::crc_hash
namespace utils_tm
{
namespace hash_tm
{
using default_hash = crc_hash;
}
} // namespace utils_tm
#endif // CRC


#ifdef MURMUR2
#include "hash/murmur2_hash.hpp"
#define HASHFCT utils_tm::hash_tm::murmur2_hash
namespace utils_tm
{
namespace hash_tm
{
using default_hash = murmur2_hash;
}
} // namespace utils_tm
#endif // MURMUR2


#ifdef MURMUR3
#include "hash/murmur3_hash.hpp"
#define HASHFCT utils_tm::hash_tm::murmur3_hash
namespace utils_tm
{
namespace hash_tm
{
using default_hash = murmur3_hash;
}
} // namespace utils_tm
#endif // MURMUR3


#ifdef XXHASH
#include "hash/xx_hash.hpp"
#define HASHFCT utils_tm::hash_tm::xx_hash
namespace utils_tm
{
namespace hash_tm
{
using default_hash = xx_hash;
}
} // namespace utils_tm
#endif // XXHASH


#ifdef XXH3
#include "hash/xx_h3.hpp"
#define HASHFCT utils_tm::hash_tm::xx_h3
namespace utils_tm
{
namespace hash_tm
{
using default_hash = xx_h3;
}
} // namespace utils_tm
#endif // XXH3
