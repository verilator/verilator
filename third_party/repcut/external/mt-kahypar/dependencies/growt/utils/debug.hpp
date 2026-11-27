#pragma once

/*******************************************************************************
 * debug.hpp
 *
 * Some functions for onvenient Debugging
 *
 * dout(): returns output object for debug messages (switchable to file out ...)
 *
 * counter: defines a counter type that won't do anything if debug is turned of
 *          (note that it still consumes 1byte)
 * checker: rai encapsulates a size_t counter and checks if the counter has the
 *          expected value when the checker is destroyed
 *          (used for checking the number of acquired/released smartpointers
 *           within a function)
 *
 * Part of my utils library utils_tm - https://github.com/TooBiased/utils_tm.git
 *
 * Copyright (C) 2019 Tobias Maier <t.maier@kit.edu>
 *
 * All rights reserved. Published under the BSD-2 license in the LICENSE file.
 ******************************************************************************/

#include <atomic>
#include <iostream>
#include <string>

#ifndef NO_EXCEPT
#include <exception>
#endif

#include "output.hpp"

namespace utils_tm
{
namespace debug_tm
{

#ifdef DEBUG
constexpr bool debug_mode   = true;
constexpr bool verbose_mode = false;
#else
constexpr bool debug_mode   = false;
constexpr bool verbose_mode = false;
#endif

inline out_tm::output_type& dout()
{
    static out_tm::output_type static_dout;
    return static_dout;
}

// DEBUG OUTPUTS *** only print if debug_mode is on ************************
// outputs a message (in yellow) if in debug mode and condition is true
inline void
if_debug(const std::string& str, [[maybe_unused]] bool condition = true)
{
    if constexpr (debug_mode)
    {
        if (condition)
        {
            dout() << out_tm::color::yellow << str << out_tm::color::reset
                   << std::endl;
        }
    }
}

// outputs an error message (in red) and exits if in debug mode and condition is
// true
inline void if_debug_critical(const std::string&      str,
                              [[maybe_unused]] bool   condition  = true,
                              [[maybe_unused]] size_t error_code = 42)
{
    if constexpr (debug_mode)
    {
        if (condition)
        {
            dout() << out_tm::color::red << str << out_tm::color::reset
                   << std::endl;
#ifdef NO_EXCEPT
            exit(error_code);
#else
            throw std::runtime_error(str);
#endif
        }
    }
}

// outputs the message (in blue) if in verbose mode
inline void if_verbose(const std::string& str)
{
    if constexpr (verbose_mode)
    {
        dout() << out_tm::color::blue << str << out_tm::color::reset
               << std::endl;
    }
}



// COUNTER *** (either atomic_size_t or dummy_counter) *********************
// either an atomic counter or a dummy that does nothing
class dummy_counter
{
  public:
    dummy_counter(size_t = 0) {}
    inline void   store(size_t) const {}
    inline size_t load() const { return 0; }
    inline size_t operator++(int) const { return 0; }
};

using counter =
    std::conditional<debug_mode, std::atomic<size_t>, dummy_counter>::type;


// CHECKER *** (either real_checker or dummy_checker) **********************
// on destructor checks wether the given counter has the expected difference
// used to sanity check the number of protected hazard counters
// two implementations real and dummy (debug mode or not)
class real_checker
{
  private:
    using ctype = size_t;
    const ctype& _counter;
    size_t       _start;
    size_t       _exp_diff;
    std::string  _message;

  public:
    real_checker(const ctype& counter, const std::string& msg,
                 size_t exp_diff = 0)
        : _counter(counter), _start(counter), _exp_diff(exp_diff), _message(msg)
    {
    }

    ~real_checker()
    {
        auto temp = _counter;
        if (temp != _start + _exp_diff)
            dout() << _message << " -- expected " << _exp_diff << " got "
                   << temp - _start << std::endl;
    }

    void add_message(const std::string& str) { _message.append(str); }

    void check(const std::string& msg, size_t exp_diff = 0)
    {
        auto temp = _counter;
        if (temp != _start + exp_diff)
            dout() << msg << " -- expected " << exp_diff << " got "
                   << temp - _start << std::endl;
    }

    void change_exp_diff(size_t diff) { _exp_diff = diff; }
};

class dummy_checker
{
  public:
    dummy_checker(const std::atomic_size_t&, const std::string&, size_t = 0) {}

    void add_message(const std::string&) {}

    void check(const std::string&, size_t = 0) {}

    void change_exp_diff(size_t = 0) {}
};

using checker = std::conditional<debug_mode, real_checker, dummy_checker>::type;
} // namespace debug_tm
} // namespace utils_tm
