/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2025 Nikolai Maas <nikolai.maas@kit.edu>
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
#include <unordered_map>
#include <mutex>
#include <sstream>
#include <type_traits>

#include "kahypar-resources/meta/policy_registry.h"
#include "kahypar-resources/meta/template_parameter_to_string.h"

#include "mt-kahypar/utils/exception.h"


namespace mt_kahypar {
template <typename IDType>
class ThreadSafePolicyRegistry {
 private:
  using PolicyBase = kahypar::meta::PolicyBase;
  using PolicyBasePtr = std::unique_ptr<PolicyBase>;
  using UnderlyingIDType = typename std::underlying_type_t<IDType>;
  using PolicyMap = std::unordered_map<UnderlyingIDType, PolicyBasePtr>;

 public:
  bool registerObject(const IDType& name, PolicyBase* policy) {
    static std::mutex lock;

    std::lock_guard<std::mutex> guard(lock);
    return _policies.emplace(
      static_cast<UnderlyingIDType>(name), PolicyBasePtr(policy)).second;
  }

  static ThreadSafePolicyRegistry & getInstance() {
    static ThreadSafePolicyRegistry _registry_instance;
    return _registry_instance;
  }

  PolicyBase & getPolicy(const IDType& name) {
    const auto it = _policies.find(static_cast<UnderlyingIDType>(name));
    if (it != _policies.end()) {
      return *(it->second.get());
    }
    std::stringstream ss;
    ss << "Invalid policy identifier " << kahypar::meta::templateToString<IDType>() << ": " << name << std::endl;
    ss << "Please check your .ini config file.";
    throw InvalidParameterException(ss.str());
  }

 private:
  ThreadSafePolicyRegistry() :
    _policies() { }

  PolicyMap _policies;
};
}  // namespace mtkahypar
