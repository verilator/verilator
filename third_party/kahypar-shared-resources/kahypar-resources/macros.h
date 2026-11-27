/*******************************************************************************
 * MIT License
 *
 * This file is part of KaHyPar.
 *
 * Copyright (C) 2015 Sebastian Schlag <sebastian.schlag@kit.edu>
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 ******************************************************************************/

#pragma once

#ifndef NDEBUG
#ifndef KAHYPAR_DISABLE_ASSERTIONS
#define KAHYPAR_USE_ASSERTIONS
#endif
#include <cstdlib>
#endif

#include <cstring>
#include <iostream>

#include "kahypar-resources/utils/logger.h"

#if defined(__GNUC__) || defined(__clang__)
// branch prediction
#define likely(x)      __builtin_expect(!!(x), 1)
#define unlikely(x)    __builtin_expect(!!(x), 0)
#else
#define likely(x)   x
#define unlikely(x) x
#endif

#define __FILENAME__ (strrchr(__FILE__, '/') ? strrchr(__FILE__, '/') + 1 : __FILE__)

// http://stackoverflow.com/questions/195975/how-to-make-a-char-string-from-a-c-macros-value#196093
#define QUOTE(name) #name
#define STR(macro) QUOTE(macro)

#define  JOIN(a, b)       a ## b

// Logging inspired by https://github.com/thrill/thrill/blob/master/thrill/common/logger.hpp
/*!

\brief LOG and DBG

This is a short description of how to use \ref LOG and \ref DBG.

kahypar::Logger is not used directly.
Instead there are the macros: \ref LOG and \ref DBG that can be used as such:
\code
LOG << "This will be printed with a newline";
DBG << "This will be printed with a newline";
\endcode

DBG macros only print the lines if the boolean variable **debug** is
true. This variable is searched for in the scope of the LOG, which means it can
be set or overridden in the function scope, the class scope, from **inherited
classes**, or even the global scope.

LLOG and LDBG macros can used to force line-based output, i.e., the logger does
not print a newline at the end.

\code
class MyClass
{
    static constexpr bool debug = true;

    void func1()
    {
        LOG  << "This will always be printed";

        LOG0 << "This is temporarily disabled.";
        DBG0 << "This is temporarily disabled.";

        DBG  << "This is printed because debug is true";
        DBGC(true == true) << "DBGC statements will be printed iff debug == true"
                           << "and the conditions are true."

        for(int i = 0; i < 10; ++i) {
          LLOG << i; // will print: 1 2 3 4 5 ...
        }
    }

    void func2()
    {
        static constexpr bool debug = false;
        LOG << "This is still printed";
        DBG  << "This is not printed anymore.";
        DBGC(true == true) << "This is not printed anymore.";
        DBG1 << "This will still be printed."
    }
};
\endcode

After a module works as intended, one can just set `debug = false`, and all
debug output will disappear.
 */

// ! Explicitly specify the condition for debug statements
#define LOGCC(cond, newline) \
  !(cond) ? (void)0 :        \
  kahypar::LoggerVoidify() & kahypar::Logger(newline)

// ! Explicitly specify the condition for logging
#define DBGCC(cond, newline) \
  !(cond) ? (void)0 :        \
  kahypar::LoggerVoidify() & kahypar::Logger(newline, __FILENAME__, __FUNCTION__, __LINE__)

// ! Override default output: never or always output debug statements.
#define LOG0 LOGCC(false, true)
#define LOG LOGCC(true, true)

// ! Default debug method: output if the local debug variable is true.
#define DBG  DBGCC(debug, true)
// ! Override default output: never or always output debug.
#define DBG0 DBGCC(false, true)
#define DBG1 DBGCC(true, true)

// ! Line-based versions that do not print a newline on destruction.
#define LLOG0 LOGCC(false, false)
#define LLOG LOGCC(true, false)
#define LDBG  DBGCC(debug, false)
#define LDBG0 DBGCC(false, false)
#define LDBG1 DBGCC(true, false)

// ! Allow DBG to take an additional condition
#define DBGC(condition) DBGCC(debug && (condition), true)

#define V(X) #X << "=" << X

#define EXPAND(X) X
#define NARG(...) EXPAND(NARG_(__VA_ARGS__, RSEQ_N()))
#define NARG_(...) EXPAND(ARG_N(__VA_ARGS__))
#define ARG_N(_1, _2, N, ...) N
#define RSEQ_N() 2, 1, 0

#if defined(_MSC_VER)
#define __PRETTY_FUNCTION__ __FUNCTION__
#endif

#ifdef KAHYPAR_USE_ASSERTIONS
#ifdef KAHYPAR_USE_STANDARD_ASSERTIONS
#define ASSERT_2(cond, msg) \
  assert(cond)
#else
#define ASSERT_2(cond, msg)                   \
  do {                                        \
    if (!(cond)) {                            \
      DBG1 << "Assertion `" #cond "` failed:" \
           << msg;                            \
      std::abort();                           \
    }                                         \
  } while (0)
#endif

  #define ASSERT_1(cond) ASSERT_2(cond, "")
#else
  #define ASSERT_2(cond, msg)
  #define ASSERT_1(cond)
#endif

#define ASSERT_(N) ASSERT_ ## N
#define ASSERT_EVAL(N) ASSERT_(N)
#define ASSERT(...) EXPAND(ASSERT_EVAL(EXPAND(NARG(__VA_ARGS__)))(__VA_ARGS__))

// *** an always-on ASSERT
#ifdef KAHYPAR_USE_STANDARD_ASSERTIONS
#define ALWAYS_ASSERT_2(cond, msg) \
  assert(cond)
# else
#define ALWAYS_ASSERT_2(cond, msg)            \
  do {                                        \
    if (!(cond)) {                            \
      DBG1 << "Assertion `" #cond "` failed:" \
           << msg;                            \
      std::abort();                           \
    }                                         \
  } while (0)
#endif

#define ALWAYS_ASSERT_1(cond) ALWAYS_ASSERT_2(cond, "")

#define ALWAYS_ASSERT_(N) ALWAYS_ASSERT_ ## N
#define ALWAYS_ASSERT_EVAL(N) ALWAYS_ASSERT_(N)
#define ALWAYS_ASSERT(...) EXPAND(ALWAYS_ASSERT_EVAL(EXPAND(NARG(__VA_ARGS__)))(__VA_ARGS__))

// definitions for heavy assertions
#define HEAVY_ASSERT0(cond) \
  !(enable_heavy_assert) ? (void)0 : [&]() { ASSERT(cond); } ()
#define HEAVY_ASSERT1(cond, msg) \
  !(enable_heavy_assert) ? (void)0 : [&]() { ASSERT(cond, msg); } ()

#ifdef KAHYPAR_ENABLE_HEAVY_DATA_STRUCTURE_ASSERTIONS
  #define HEAVY_DATA_STRUCTURE_ASSERT_1(cond) ASSERT(cond)
  #define HEAVY_DATA_STRUCTURE_ASSERT_2(cond, msg) ASSERT(cond, msg)
#else
  #define HEAVY_DATA_STRUCTURE_ASSERT_1(cond) HEAVY_ASSERT0(cond)
  #define HEAVY_DATA_STRUCTURE_ASSERT_2(cond, msg) HEAVY_ASSERT1(cond, msg)
#endif


#ifdef KAHYPAR_ENABLE_HEAVY_PREPROCESSING_ASSERTIONS
  #define HEAVY_PREPROCESSING_ASSERT_1(cond) ASSERT(cond)
  #define HEAVY_PREPROCESSING_ASSERT_2(cond, msg) ASSERT(cond, msg)
#else
  #define HEAVY_PREPROCESSING_ASSERT_1(cond) HEAVY_ASSERT0(cond)
  #define HEAVY_PREPROCESSING_ASSERT_2(cond, msg) HEAVY_ASSERT1(cond, msg)
#endif

#ifdef KAHYPAR_ENABLE_HEAVY_COARSENING_ASSERTIONS
  #define HEAVY_COARSENING_ASSERT_1(cond) ASSERT(cond)
  #define HEAVY_COARSENING_ASSERT_2(cond, msg) ASSERT(cond, msg)
#else
  #define HEAVY_COARSENING_ASSERT_1(cond) HEAVY_ASSERT0(cond)
  #define HEAVY_COARSENING_ASSERT_2(cond, msg) HEAVY_ASSERT1(cond, msg)
#endif

#ifdef KAHYPAR_ENABLE_HEAVY_INITIAL_PARTITIONING_ASSERTIONS
  #define HEAVY_INITIAL_PARTITIONING_ASSERT_1(cond) ASSERT(cond)
  #define HEAVY_INITIAL_PARTITIONING_ASSERT_2(cond, msg) ASSERT(cond, msg)
#else
  #define HEAVY_INITIAL_PARTITIONING_ASSERT_1(cond) HEAVY_ASSERT0(cond)
  #define HEAVY_INITIAL_PARTITIONING_ASSERT_2(cond, msg) HEAVY_ASSERT1(cond, msg)
#endif

#ifdef KAHYPAR_ENABLE_HEAVY_REFINEMENT_ASSERTIONS
  #define HEAVY_REFINEMENT_ASSERT_1(cond) ASSERT(cond)
  #define HEAVY_REFINEMENT_ASSERT_2(cond, msg) ASSERT(cond, msg)
#else
  #define HEAVY_REFINEMENT_ASSERT_1(cond) HEAVY_ASSERT0(cond)
  #define HEAVY_REFINEMENT_ASSERT_2(cond, msg) HEAVY_ASSERT1(cond, msg)
#endif

#define HEAVY_ASSERT_(TYPE, N) HEAVY_ ## TYPE ## _ASSERT_ ## N
#define HEAVY_ASSERT_EVAL(TYPE, N) HEAVY_ASSERT_(TYPE, N)

// Heavy assertions are assertions which increase the complexity of the scope
// which they are executed in by an polynomial factor. In debug mode you are often only
// interested in certain phase of the multilevel paradigm. However, when enabling all assertions
// it can take a while to reach the point which you are really interested in, because heavy assertions
// radicaly downgrade the performance of the application. Therefore such assertions should be packed
// in a heavy assertion macro. Heavy assertions can be enabled via cmake flag for specific phase or for
// specific scope by adding
// static constexpr bool enable_heavy_assert = false;
// to the corresponding scope.
#define HEAVY_DATA_STRUCTURE_ASSERT(...) EXPAND(HEAVY_ASSERT_EVAL(DATA_STRUCTURE, EXPAND(NARG(__VA_ARGS__)))(__VA_ARGS__))
#define HEAVY_PREPROCESSING_ASSERT(...) EXPAND(HEAVY_ASSERT_EVAL(PREPROCESSING, EXPAND(NARG(__VA_ARGS__)))(__VA_ARGS__))
#define HEAVY_COARSENING_ASSERT(...) EXPAND(HEAVY_ASSERT_EVAL(COARSENING, EXPAND(NARG(__VA_ARGS__)))(__VA_ARGS__))
#define HEAVY_INITIAL_PARTITIONING_ASSERT(...) EXPAND(HEAVY_ASSERT_EVAL(INITIAL_PARTITIONING, EXPAND(NARG(__VA_ARGS__)))(__VA_ARGS__))
#define HEAVY_REFINEMENT_ASSERT(...) EXPAND(HEAVY_ASSERT_EVAL(REFINEMENT, EXPAND(NARG(__VA_ARGS__)))(__VA_ARGS__))

#define ONLYDEBUG(x) ((void)x)
#define UNUSED_FUNCTION(x) ((void)x)

#if defined(__GNUC__) || defined(__clang__)
#define UTILS_UNUSED __attribute__ ((unused))
#define UNUSED(name) unused_ ## name UTILS_UNUSED
#else
#define UNUSED(name) name
#endif

template <typename T>
void unused(T&&) {
  // Used to avoid warnings of unused variables
}

#if defined(__GNUC__) || defined(__clang__)
#define KAHYPAR_ATTRIBUTE_ALWAYS_INLINE __attribute__ ((always_inline))
#else
#define KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
#endif

#if (defined(_M_AMD64) || defined(__x86_64__))
#define KAHYPAR_HAS_BITSCAN64
#endif

#if defined(__GNUC__) && __GNUC__ >= 7
#define KAHYPAR_ATTRIBUTE_FALLTHROUGH __attribute__ ((fallthrough))
#elif defined(__clang__)
#define KAHYPAR_ATTRIBUTE_FALLTHROUGH [[clang::fallthrough]]
#else
#define KAHYPAR_ATTRIBUTE_FALLTHROUGH
#endif

// Shell Color Codes
#define GREEN "\033[1;92m"
#define CYAN "\033[1;96m"
#define YELLOW "\033[1;93m"
#define RED "\033[1;91m"
#define BOLD "\033[1m"
#define END "\033[0m"

// Errors, warnings and input validation
#define MESSAGE_1(msg) msg
#define MESSAGE_2(msg, line_number) msg << " (line " << static_cast<size_t>(line_number) << ")"

#define MESSAGE_(N) MESSAGE_ ## N
#define MESSAGE_EVAL(N) MESSAGE_(N)
#define MESSAGE(...) EXPAND(MESSAGE_EVAL(EXPAND(NARG(__VA_ARGS__)))(__VA_ARGS__))

#define ERROR(...) std::cerr << "Error: " << MESSAGE(__VA_ARGS__) << std::endl; std::exit(1)

#ifdef KAHYPAR_INPUT_VALIDATION
  #define VALIDATE_INPUT true
#else
  #define VALIDATE_INPUT false
#endif

#ifdef KAHYPAR_INPUT_VALIDATION_PROMOTE_WARNINGS_TO_ERRORS
  #define PROMOTE_WARNINGS_TO_ERRORS true
  #define WARNING(...) ERROR(__VA_ARGS__)
#else
  #define PROMOTE_WARNINGS_TO_ERRORS false
  #define WARNING(...) std::cerr << "Warning: " << MESSAGE(__VA_ARGS__) << std::endl
#endif
