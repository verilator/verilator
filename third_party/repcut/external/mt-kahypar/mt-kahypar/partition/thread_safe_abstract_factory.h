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

#include "kahypar-resources/meta/function_traits.h"
#include "kahypar-resources/meta/template_parameter_to_string.h"

#include "mt-kahypar/utils/exception.h"


namespace mt_kahypar {
template <typename IdentifierType, typename ProductCreator>
class ThreadSafeFactory {
 private:
  using AbstractProduct = typename std::remove_pointer_t<
    typename kahypar::meta::FunctionTraits<ProductCreator>::result_type>;
  using AbstractProductPtr = std::unique_ptr<AbstractProduct>;
  using UnderlyingIdentifierType = typename std::underlying_type_t<IdentifierType>;
  using CallbackMap = std::unordered_map<UnderlyingIdentifierType, ProductCreator>;

 public:
  ThreadSafeFactory(const ThreadSafeFactory&) = delete;
  ThreadSafeFactory(ThreadSafeFactory&&) = delete;
  ThreadSafeFactory& operator= (const ThreadSafeFactory&) = delete;
  ThreadSafeFactory& operator= (ThreadSafeFactory&&) = delete;

  ~ThreadSafeFactory() = default;

  template <typename I, typename ... ProductParameters>
  AbstractProductPtr createObject(const I& id, ProductParameters&& ... params) {
    const auto creator = _callbacks.find(static_cast<UnderlyingIdentifierType>(id));
    if (creator != _callbacks.end()) {
      return AbstractProductPtr((creator->second)(std::forward<ProductParameters>(params) ...));
    }
    std::stringstream ss;
    ss << "Could not load " << kahypar::meta::templateToString<IdentifierType>() << ": " << id << std::endl;
    ss << "Please check your .ini config file.";
    throw InvalidParameterException(ss.str());
  }

  static ThreadSafeFactory & getInstance() {
    static ThreadSafeFactory _factory_instance;
    return _factory_instance;
  }

  bool registerObject(const IdentifierType& id, ProductCreator creator) {
    static std::mutex lock;

    std::lock_guard<std::mutex> guard(lock);
    return _callbacks.insert({ static_cast<UnderlyingIdentifierType>(id), creator }).second;
  }

 private:

  ThreadSafeFactory() :
    _callbacks() { }

  CallbackMap _callbacks;
};
}  // namespace mtkahypar
