// SPDX-FileCopyrightText: 2025 Yu-Sheng Lin <johnjohnlys@gmail.com>
// SPDX-License-Identifier: MIT
// Project: libfstwriter
// Website: https://github.com/gtkwave/libfstwriter
#pragma once
// direct include
// C system headers
// C++ standard library headers
#include <cstdlib>
#include <iostream>
#include <sstream>
// Other libraries' .h files.
// Your project's .h files.

#define FST_CHECK(a)                    \
	if (!(a)) [[unlikely]] {            \
		std::ostringstream oss;         \
		oss << "FST_CHECK failed: " #a; \
		const auto e = oss.str();       \
		std::cerr << e << std::endl;    \
		std::abort();                   \
	}

#define FST_CHECK_EQ(a, b)                           \
	if ((a) != (b)) [[unlikely]] {                   \
		std::ostringstream oss;                      \
		oss << "FST_CHECK_EQ failed: " #a " != " #b; \
		oss << " (" << (a) << " vs. " << (b) << ")"; \
		const auto e = oss.str();                    \
		std::cerr << e << std::endl;                 \
		std::abort();                                \
	}

#define FST_CHECK_NE(a, b)                           \
	if ((a) == (b)) [[unlikely]] {                   \
		std::ostringstream oss;                      \
		oss << "FST_CHECK_NE failed: " #a " == " #b; \
		oss << " (" << (a) << " vs. " << (b) << ")"; \
		const auto e = oss.str();                    \
		std::cerr << e << std::endl;                 \
		std::abort();                                \
	}

#define FST_CHECK_GT(a, b)                           \
	if ((a) <= (b)) [[unlikely]] {                   \
		std::ostringstream oss;                      \
		oss << "FST_CHECK_GT failed: " #a " <= " #b; \
		oss << " (" << (a) << " vs. " << (b) << ")"; \
		const auto e = oss.str();                    \
		std::cerr << e << std::endl;                 \
		std::abort();                                \
	}

#define FST_CHECK_GE(a, b)                           \
	if ((a) < (b)) [[unlikely]] {                    \
		std::ostringstream oss;                      \
		oss << "FST_CHECK_GE failed: " #a " < " #b;  \
		oss << " (" << (a) << " vs. " << (b) << ")"; \
		const auto e = oss.str();                    \
		std::cerr << e << std::endl;                 \
		std::abort();                                \
	}

#define FST_CHECK_LT(a, b)                           \
	if ((a) >= (b)) [[unlikely]] {                   \
		std::ostringstream oss;                      \
		oss << "FST_CHECK_LT failed: " #a " >= " #b; \
		oss << " (" << (a) << " vs. " << (b) << ")"; \
		const auto e = oss.str();                    \
		std::cerr << e << std::endl;                 \
		std::abort();                                \
	}

#define FST_CHECK_LE(a, b)                           \
	if ((a) > (b)) [[unlikely]] {                    \
		std::ostringstream oss;                      \
		oss << "FST_CHECK_LE failed: " #a " > " #b;  \
		oss << " (" << (a) << " vs. " << (b) << ")"; \
		const auto e = oss.str();                    \
		std::cerr << e << std::endl;                 \
		std::abort();                                \
	}

// We turn on all DCHECKs to CHECKs temporarily for better safety.
#if 1
#	define FST_DCHECK(a) FST_CHECK(a)
#	define FST_DCHECK_EQ(a, b) FST_CHECK_EQ(a, b)
#	define FST_DCHECK_NE(a, b) FST_CHECK_NE(a, b)
#	define FST_DCHECK_GT(a, b) FST_CHECK_GT(a, b)
#	define FST_DCHECK_GE(a, b) FST_CHECK_GE(a, b)
#	define FST_DCHECK_LT(a, b) FST_CHECK_LT(a, b)
#	define FST_DCHECK_LE(a, b) FST_CHECK_LE(a, b)
#else
#	define FST_DCHECK(a)
#	define FST_DCHECK_EQ(a, b)
#	define FST_DCHECK_NE(a, b)
#	define FST_DCHECK_GT(a, b)
#	define FST_DCHECK_GE(a, b)
#	define FST_DCHECK_LT(a, b)
#	define FST_DCHECK_LE(a, b)
#endif

// Compatibility layer for unreachable code hint
#if defined(__cplusplus) && __cplusplus >= 202302L
#	include <utility>
#	define FST_UNREACHABLE std::unreachable()
#elif USE_GCC_INTRINSIC
#	define FST_UNREACHABLE __builtin_unreachable()
// TODO: implement MSVC version
// #elif USE_MSVC_INTRINSIC
#else
#	define FST_UNREACHABLE std::abort()
#endif
