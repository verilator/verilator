// SPDX-FileCopyrightText: 2025 Yu-Sheng Lin <johnjohnlys@gmail.com>
// SPDX-License-Identifier: MIT
#pragma once
// direct include
// C system headers
// C++ standard library headers
#include <iostream>
#include <sstream>
#include <stdexcept>
// Other libraries' .h files.
// Your project's .h files.

#define FST_CHECK(a)                    \
	if (!(a)) [[unlikely]] {            \
		std::ostringstream oss;         \
		oss << "FST_CHECK failed: " #a; \
		const auto e = oss.str();       \
		std::cerr << e << std::endl;    \
		throw std::runtime_error(e);    \
	}

#define FST_CHECK_EQ(a, b)                           \
	if ((a) != (b)) [[unlikely]] {                   \
		std::ostringstream oss;                      \
		oss << "FST_CHECK_EQ failed: " #a " != " #b; \
		oss << " (" << (a) << " vs. " << (b) << ")"; \
		const auto e = oss.str();                    \
		std::cerr << e << std::endl;                 \
		throw std::runtime_error(e);                 \
	}

#define FST_CHECK_NE(a, b)                           \
	if ((a) == (b)) [[unlikely]] {                   \
		std::ostringstream oss;                      \
		oss << "FST_CHECK_NE failed: " #a " == " #b; \
		oss << " (" << (a) << " vs. " << (b) << ")"; \
		const auto e = oss.str();                    \
		std::cerr << e << std::endl;                 \
		throw std::runtime_error(e);                 \
	}

#define FST_CHECK_GT(a, b)                           \
	if ((a) <= (b)) [[unlikely]] {                   \
		std::ostringstream oss;                      \
		oss << "FST_CHECK_GT failed: " #a " <= " #b; \
		oss << " (" << (a) << " vs. " << (b) << ")"; \
		const auto e = oss.str();                    \
		std::cerr << e << std::endl;                 \
		throw std::runtime_error(e);                 \
	}

// We turn on all DCHECKs to CHECKs temporarily for better safety.
#if 1
#	define FST_DCHECK(a) FST_CHECK(a)
#	define FST_DCHECK_EQ(a, b) FST_CHECK_EQ(a, b)
#	define FST_DCHECK_NE(a, b) FST_CHECK_NE(a, b)
#	define FST_DCHECK_GT(a, b) FST_CHECK_GT(a, b)
#else
#	define FST_DCHECK(a)
#	define FST_DCHECK_EQ(a, b)
#	define FST_DCHECK_NE(a, b)
#	define FST_DCHECK_GT(a, b)
#endif

// Compatibility layer for unreachable code hint
#if defined(__cplusplus) && __cplusplus >= 202302L
// Prefer the standard library version if available
#	include <utility>
#	define FST_UNREACHABLE std::unreachable()
#elif defined(__GNUC__) || defined(__clang__)
// --- GCC / Clang ---
#	define FST_UNREACHABLE __builtin_unreachable()
#elif defined(_MSC_VER)
// --- MSVC ---
#	define FST_UNREACHABLE __assume(0)
#else
// --- Fallback ---
#	define FST_UNREACHABLE std::abort()
#endif
