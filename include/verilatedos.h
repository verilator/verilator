// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2003-2015 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License.
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************
///
/// \file
/// \brief Verilator: Common include for OS portability (verilated & verilator)
///
///	This header is used by both the Verilator source code (run on the
///	build and host system), and the Verilated output (run on the target
///	system).  Code needed by only the host system goes into
///	config_build.h.in, code needed by Verilated code only goes into
///	verilated.h, and code needed by both goes here (verilatedos.h).
///
/// Code available from: http://www.veripool.org/verilator
///
//*************************************************************************


#ifndef _VERILATEDOS_H_
#define _VERILATEDOS_H_ 1 ///< Header Guard

//=========================================================================
// Compiler pragma abstraction

#ifdef __GNUC__
# define VL_ATTR_ALIGNED(alignment) __attribute__ ((aligned (alignment)))
# define VL_ATTR_ALWINLINE __attribute__ ((always_inline))
# define VL_ATTR_NORETURN __attribute__ ((noreturn))
# ifdef _WIN32
#  define VL_ATTR_PRINTF(fmtArgNum)  // GCC with MS runtime will fool the print arg checker
# else
#  define VL_ATTR_PRINTF(fmtArgNum) __attribute__ ((format (printf, fmtArgNum, fmtArgNum+1)))
# endif
# define VL_ATTR_UNUSED __attribute__ ((unused))
# define VL_FUNC  __func__
# define VL_LIKELY(x)	__builtin_expect(!!(x), 1)
# define VL_UNLIKELY(x)	__builtin_expect(!!(x), 0)
# define VL_PREFETCH_RD(p) __builtin_prefetch((p),0)
# define VL_PREFETCH_RW(p) __builtin_prefetch((p),1)
#elif defined(_MSC_VER)
# define VL_ATTR_ALIGNED(alignment)
# define VL_ATTR_ALWINLINE
# define VL_ATTR_NORETURN
# define VL_ATTR_PRINTF(fmtArgNum)
# define VL_ATTR_UNUSED
# define VL_FUNC  __FUNCTION__
# define VL_LIKELY(x)	(!!(x))
# define VL_UNLIKELY(x)	(!!(x))
# define VL_PREFETCH_RD(p)
# define VL_PREFETCH_RW(p)
#else
# define VL_ATTR_ALIGNED(alignment)	///< Align structure to specified byte alignment
# define VL_ATTR_ALWINLINE		///< Inline, even when not optimizing
# define VL_ATTR_NORETURN		///< Function does not ever return
# define VL_ATTR_PRINTF(fmtArgNum)	///< Function with printf format checking
# define VL_ATTR_UNUSED			///< Function that may be never used
# define VL_FUNC "__func__"		///< Name of current function for error macros
# define VL_LIKELY(x)	(!!(x))		///< Boolean expression more often true than false
# define VL_UNLIKELY(x)	(!!(x))		///< Boolean expression more often false than true
# define VL_PREFETCH_RD(p)		///< Prefetch data with read intent
# define VL_PREFETCH_RW(p)		///< Prefetch data with read/write intent
#endif

#ifdef VL_THREADED
# ifdef __GNUC__
#  define VL_THREAD	__thread	///< Storage class for thread-local storage
# else
#  error "Unsupported compiler for VL_THREADED: No thread-local declarator"
# endif
# define VL_STATIC_OR_THREAD		///< Static if unthreaded, as some strings can be faster
//					///< if non-dynamic and can't do "static VL_THREAD string"
#else
# define VL_THREAD			///< Storage class for thread-local storage
# define VL_STATIC_OR_THREAD static	///< Static if unthreaded, as some strings can be faster
//					///< if non-dynamic and can't do "static VL_THREAD string"
#endif

#ifdef _MSC_VER
# define VL_ULL(c) (c##ui64)	///< Add appropriate suffix to 64-bit constant
#else
# define VL_ULL(c) (c##ULL)	///< Add appropriate suffix to 64-bit constant
#endif

// This is not necessarily the same as #UL, depending on what the IData typedef is.
#define VL_UL(c) ((IData)(c##UL))	///< Add appropriate suffix to 32-bit constant

//=========================================================================
// C++-2011

#if __cplusplus >= 201103L || defined(__GXX_EXPERIMENTAL_CXX0X__)
# define VL_HAS_UNIQUE_PTR
# define VL_UNIQUE_PTR unique_ptr
#else
# define VL_UNIQUE_PTR auto_ptr
#endif

//=========================================================================
// Optimization

#ifndef VL_INLINE_OPT
# define VL_INLINE_OPT		///< "inline" if compiling all objects in single compiler run
#endif

//=========================================================================
// Warning disabled

#ifndef VL_WARNINGS
# ifdef _MSC_VER
#  pragma warning(disable:4099)	// C4099: type name first seen using 'class' now seen using 'struct' (V3AstNode)
#  pragma warning(disable:4100)	// C4100: unreferenced formal parameter (L4)
#  pragma warning(disable:4127)	// C4127: conditional expression is constant (L4)
#  pragma warning(disable:4146)	// C4146: unary minus operator applied to unsigned type, result still unsigned
#  pragma warning(disable:4189)	// C4189: local variable is initialized but not referenced (L4)
#  pragma warning(disable:4244)	// C4244: conversion from 'uint64_t' to 'uint_32_t', possible loss of data
#  pragma warning(disable:4245)	// C4245: conversion from 'int' to 'unsigned', signed/unsigned mismatch
#  pragma warning(disable:4996)	// C4996: sscanf/fopen/etc may be unsafe
# endif
#endif

//=========================================================================
// Basic integer types

#ifdef VL_UINTS_DEFINED
#elif defined(__CYGWIN__)

# include <stdint.h>
typedef unsigned char           uint8_t;	///< 8-bit unsigned type (backward compatibility)
typedef unsigned short int      uint16_t;	///< 16-bit unsigned type (backward compatibility)
typedef unsigned char           vluint8_t;	///< 8-bit unsigned type
typedef unsigned short int      vluint16_t;	///< 16-bit unsigned type
# if defined(__uint32_t_defined) || defined(___int32_t_defined)    // Newer Cygwin uint32_t in stdint.h as an unsigned int
typedef int32_t			vlsint32_t;	///< 32-bit signed type
typedef uint32_t		vluint32_t;	///< 32-bit unsigned type
# else				 		// Older Cygwin has long==uint32_t
typedef unsigned long		uint32_t;	///< 32-bit unsigned type (backward compatibility)
typedef long			vlsint32_t;	///< 32-bit signed type
typedef unsigned long		vluint32_t;	///< 32-bit unsigned type
# endif
# if defined(__WORDSIZE) && (__WORDSIZE == 64)
typedef long			vlsint64_t;	///< 64-bit signed type
typedef unsigned long		vluint64_t;	///< 64-bit unsigned type
# else
typedef long long		vlsint64_t;	///< 64-bit signed type
typedef unsigned long long	vluint64_t;	///< 64-bit unsigned type
# endif

#elif defined(_WIN32) && defined(_MSC_VER)

typedef unsigned __int8		uint8_t;	///< 8-bit unsigned type (backward compatibility)
typedef unsigned __int16	uint16_t;	///< 16-bit unsigned type (backward compatibility)
typedef unsigned __int32	uint32_t;	///< 32-bit unsigned type (backward compatibility)
typedef unsigned __int8		vluint8_t;	///< 8-bit unsigned type
typedef unsigned __int16	vluint16_t;	///< 16-bit unsigned type
typedef signed   __int32	vlsint32_t;	///< 32-bit signed type
typedef unsigned __int32	vluint32_t;	///< 32-bit unsigned type
typedef signed   __int64	vlsint64_t;	///< 64-bit signed type
typedef unsigned __int64	vluint64_t;	///< 64-bit unsigned type

# ifndef _SSIZE_T_DEFINED
#  ifdef  _WIN64
typedef signed   __int64        ssize_t;        ///< signed size_t; returned from read()
#  else
typedef signed   __int32        ssize_t;        ///< signed size_t; returned from read()
#  endif
# endif

#else // Linux or compliant Unix flavors, -m64

# include <stdint.h>	// Linux and most flavors
# include <unistd.h>	// Linux ssize_t
# include <inttypes.h>	// Solaris
typedef uint8_t			vluint8_t;	///< 32-bit unsigned type
typedef uint16_t		vluint16_t;	///< 32-bit unsigned type
typedef int			vlsint32_t;	///< 32-bit signed type
typedef uint32_t		vluint32_t;	///< 32-bit signed type
# if defined(__WORDSIZE) && (__WORDSIZE == 64)
typedef long			vlsint64_t;	///< 64-bit signed type
typedef unsigned long		vluint64_t;	///< 64-bit unsigned type
# else
typedef long long		vlsint64_t;	///< 64-bit signed type
typedef unsigned long long	vluint64_t;	///< 64-bit unsigned type
# endif
#endif

//=========================================================================
// Printing printf/scanf formats
// Alas cinttypes isn't that standard yet

#ifdef _WIN32
# define VL_PRI64 "I64"
#else // Linux or compliant Unix flavors
# if defined(__WORDSIZE) && (__WORDSIZE == 64)
#  define VL_PRI64 "l"
# else
#  define VL_PRI64 "ll"
# endif
#endif

#if defined(_WIN32) && defined(_MSC_VER)
# if (_MSC_VER < 1900)
#  define VL_SNPRINTF _snprintf
# else
#  define VL_SNPRINTF snprintf
# endif
# define VL_VSNPRINTF vsnprintf
#else
# define VL_SNPRINTF snprintf
# define VL_VSNPRINTF vsnprintf
#endif

//=========================================================================
// File system functions

#ifdef _WIN32
# define VL_DEV_NULL "nul"
#else // Linux or compliant Unix flavors
# define VL_DEV_NULL "/dev/null"
#endif

//=========================================================================
// Integer size macros

#define VL_BYTESIZE 8			///< Bits in a byte
#define VL_SHORTSIZE 16			///< Bits in a short
#define VL_WORDSIZE 32			///< Bits in a word
#define VL_QUADSIZE 64			///< Bits in a quadword
#define VL_WORDSIZE_LOG2 5		///< log2(VL_WORDSIZE)

/// Bytes this number of bits needs (1 bit=1 byte)
#define VL_BYTES_I(nbits) (((nbits)+(VL_BYTESIZE-1))/VL_BYTESIZE)
/// Words this number of bits needs (1 bit=1 word)
#define VL_WORDS_I(nbits) (((nbits)+(VL_WORDSIZE-1))/VL_WORDSIZE)

//=========================================================================
// Verilated function size macros

#define VL_MULS_MAX_WORDS 16		///< Max size in words of MULS operation
#define VL_TO_STRING_MAX_WORDS 64	///< Max size in words of String conversion operation

//=========================================================================
// Base macros

#define VL_SIZEBITS_I (VL_WORDSIZE-1)	///< Bit mask for bits in a word
#define VL_SIZEBITS_Q (VL_QUADSIZE-1)	///< Bit mask for bits in a quad

/// Mask for words with 1's where relevant bits are (0=all bits)
#define VL_MASK_I(nbits)  (((nbits) & VL_SIZEBITS_I) \
			 ? ((1U << ((nbits) & VL_SIZEBITS_I) )-1) : ~0)
/// Mask for quads with 1's where relevant bits are (0=all bits)
#define VL_MASK_Q(nbits)  (((nbits) & VL_SIZEBITS_Q) \
			 ? ((VL_ULL(1) << ((nbits) & VL_SIZEBITS_Q) )-VL_ULL(1)) : VL_ULL(~0))
#define VL_BITWORD_I(bit)	((bit)/VL_WORDSIZE)	///< Word number for a wide quantity
#define VL_BITBIT_I(bit)	((bit)&VL_SIZEBITS_I)	///< Bit number for a bit in a long
#define VL_BITBIT_Q(bit)	((bit)&VL_SIZEBITS_Q)	///< Bit number for a bit in a quad

//=========================================================================
// Floating point
// #defines, to avoid requiring math.h on all compile runs

#ifdef _MSC_VER
# define VL_TRUNC(n) (((n)<0) ? ceil((n))     : floor((n)))
# define VL_ROUND(n) (((n)<0) ? ceil((n)-0.5) : floor((n)+0.5))
#else
# define VL_TRUNC(n) trunc(n)
# define VL_ROUND(n) round(n)
#endif

//=========================================================================

#endif /*guard*/
