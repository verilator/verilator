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

#include <tuple>

namespace kahypar {
namespace meta {
// based on: http://stackoverflow.com/questions/7943525/is-it-possible-to-figure-out-the-parameter-type-and-return-type-of-a-lambda

template <typename T>
struct FunctionTraits : FunctionTraits<decltype(& T::operator())>{ };
// For generic types, directly use the result of the signature of its 'operator()'

template <typename ClassType, typename ReturnType, typename ... Args>
struct FunctionTraits<ReturnType (ClassType::*)(Args ...)>{
  // we specialize for pointers to member function
  enum { arity = sizeof ... (Args) };
  // arity is the number of arguments.

  using result_type = ReturnType;

  template <size_t i>
  using arg = typename std::tuple_element<i, std::tuple<Args ...> >::type;
  // the i-th argument is equivalent to the i-th tuple element of a tuple
  // composed of those arguments.
};

template <typename ReturnType, typename ... Args>
struct FunctionTraits<ReturnType (*)(Args ...)>{
  // we specialize for functions
  enum { arity = sizeof ... (Args) };
  // arity is the number of arguments.

  using result_type = ReturnType;

  template <size_t i>
  using arg = typename std::tuple_element<i, std::tuple<Args ...> >::type;
  // the i-th argument is equivalent to the i-th tuple element of a tuple
  // composed of those arguments.

  using args = std::tuple<Args ...>;
};
}  // namespace meta
}  // namespace kahypar
