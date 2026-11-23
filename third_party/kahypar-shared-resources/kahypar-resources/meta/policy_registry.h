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

#include <memory>
#include <string>
#include <unordered_map>

#include "kahypar-resources/macros.h"

namespace kahypar {
namespace meta {
class PolicyBase {
 public:
  PolicyBase() = default;

  PolicyBase(const PolicyBase&) = default;
  PolicyBase& operator= (const PolicyBase&) = default;

  PolicyBase(PolicyBase&&) = default;
  PolicyBase& operator= (PolicyBase&&) = default;

  virtual ~PolicyBase() = default;
};

template <typename IDType>
class PolicyRegistry {
 private:
  using PolicyBasePtr = std::unique_ptr<PolicyBase>;
  using UnderlyingIDType = typename std::underlying_type_t<IDType>;
  using PolicyMap = std::unordered_map<UnderlyingIDType, PolicyBasePtr>;

 public:
  bool registerObject(const IDType& name, PolicyBase* policy) {
    return _policies.emplace(
      static_cast<UnderlyingIDType>(name), PolicyBasePtr(policy)).second;
  }
  static PolicyRegistry & getInstance() {
    static PolicyRegistry instance;
    return instance;
  }

  PolicyBase & getPolicy(const IDType& name) {
    const auto it = _policies.find(static_cast<UnderlyingIDType>(name));
    if (it != _policies.end()) {
      return *(it->second.get());
    }
    LOG << "Invalid policy identifier";
    std::exit(-1);
  }

 private:
  PolicyRegistry() :
    _policies() { }
  PolicyMap _policies;
};
}  // namespace meta
}  // namespace kahypar
