/*******************************************************************************
 * MIT License
 *
 * This file is part of KaHyPar.
 *
 * Copyright (C) 2015-2016 Sebastian Schlag <sebastian.schlag@kit.edu>
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

namespace kahypar {
namespace meta {
class NullType { };
// default variadic template
template <typename ... Args>
struct Typelist {
  using Head = NullType;
  using Tail = NullType;
};

// Typelist with only one type
template <typename T>
struct Typelist<T>{
  using Head = T;
  using Tail = NullType;
};

// typelist with > 1 type
template <typename T, typename ... Args>
struct Typelist<T, Args ...>{
  using Head = T;
  using Tail = Typelist<Args ...>;
};

using EmptyTypelist = Typelist<>;


// Typelist concatenation and flatMapping

template <class ResultList,
          class OriginalLists>
struct concat_impl;

template <typename ... Rs,
          typename ... Ts>
struct concat_impl<Typelist<Rs ...>, Typelist<Ts ...> >{
  using type = Typelist<Rs ..., Ts ...>;
};

template <typename ... Rs,
          typename ... Ts,
          typename ... Rests>
struct concat_impl<Typelist<Rs ...>, Typelist<Typelist<Ts ...>, Rests ...> >{
  using type = typename concat_impl<Typelist<Rs ..., Ts ...>,
                                    Typelist<Rests ...> >::type;
};


template <class ListOfLists>
struct flatMap;

template <typename ... Lists>
struct flatMap<Typelist<Lists ...> >{
  using type = typename concat_impl<Typelist<>, Typelist<Lists ...> >::type;
};

template <typename ... Lists>
struct concat {
  using type = typename flatMap<Typelist<Lists ...> >::type;
};
}  // namespace meta
}  // namespace kahypar
