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

#include "kahypar-resources/meta/mandatory.h"
#include "kahypar-resources/meta/typelist.h"

namespace kahypar {
namespace meta {
template <
  class Executor = Mandatory,
  class TypesLhs = Mandatory,
  class TypesRhs = TypesLhs,
  typename ResultType = void
  >
class StaticDoubleDispatchFactory {
  using Head = typename TypesLhs::Head;
  using Tail = typename TypesLhs::Tail;

 public:
  template <typename BaseTypeLhs,
            typename BaseTypeRhs,
            typename ... Parameters>
  static ResultType go(BaseTypeLhs&& lhs, BaseTypeRhs&& rhs, Executor exec,
                       Parameters&& ... parameters) {
    if (auto* p1 = dynamic_cast<Head*>(&lhs)) {
      return StaticDoubleDispatchFactory<Executor, TypesLhs, TypesRhs,
                                         ResultType>::dispatchRhs(
        *p1, rhs, exec,
        std::forward<Parameters>(parameters) ...);
    } else {
      return StaticDoubleDispatchFactory<Executor, Tail, TypesRhs,
                                         ResultType>::go(
        lhs, rhs, exec,
        std::forward<Parameters>(parameters) ...);
    }
  }

  template <class SomeLhs,
            typename BaseTypeRhs,
            typename ... Parameters>
  static ResultType dispatchRhs(SomeLhs&& lhs, BaseTypeRhs&& rhs, Executor exec,
                                Parameters&& ... parameters) {
    using Head = typename TypesRhs::Head;
    using Tail = typename TypesRhs::Tail;
    if (auto* p2 = dynamic_cast<Head*>(&rhs)) {
      return exec.fire(lhs, *p2, std::forward<Parameters>(parameters) ...);
    } else {
      return StaticDoubleDispatchFactory<Executor, TypesLhs, Tail,
                                         ResultType>::dispatchRhs(
        lhs, rhs, exec,
        std::forward<Parameters>(parameters) ...);
    }
  }
};

template <
  class Executor,
  class TypesRhs,
  typename ResultType>
class StaticDoubleDispatchFactory<Executor, NullType, TypesRhs, ResultType>{
 public:
  template <typename BaseTypeLhs,
            typename BaseTypeRhs,
            typename ... Parameters>
  static ResultType go(BaseTypeLhs&& lhs, BaseTypeRhs&& rhs, Executor exec,
                       Parameters&& ... parameters) {
    return exec.onError(lhs, rhs, std::forward<Parameters>(parameters) ...);
  }
};

template <
  class Executor,
  class TypesLhs,
  typename ResultType>
class StaticDoubleDispatchFactory<Executor, TypesLhs, NullType, ResultType>{
 public:
  template <typename BaseTypeLhs,
            typename BaseTypeRhs,
            typename ... Parameters>
  static ResultType dispatchRhs(BaseTypeLhs& lhs, BaseTypeRhs& rhs, Executor exec,
                                Parameters&& ... parameters) {
    return exec.onError(lhs, rhs, std::forward<Parameters>(parameters) ...);
  }
};
}  // namespace meta
}  // namespace kahypar
