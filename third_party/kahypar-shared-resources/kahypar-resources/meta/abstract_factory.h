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
#include <unordered_map>

#include "kahypar-resources/macros.h"
#include "kahypar-resources/meta/function_traits.h"
#include "kahypar-resources/meta/mandatory.h"
#include "kahypar-resources/meta/template_parameter_to_string.h"


namespace kahypar {
namespace meta {
template <typename IdentifierType = Mandatory,
          typename ProductCreator = Mandatory>
class Factory {
 private:
  using AbstractProduct = typename std::remove_pointer_t<
    typename FunctionTraits<ProductCreator>::result_type>;
  using AbstractProductPtr = std::unique_ptr<AbstractProduct>;
  using UnderlyingIdentifierType = typename std::underlying_type_t<IdentifierType>;
  using CallbackMap = std::unordered_map<UnderlyingIdentifierType,
                                         ProductCreator>;

 public:
  Factory(const Factory&) = delete;
  Factory(Factory&&) = delete;
  Factory& operator= (const Factory&) = delete;
  Factory& operator= (Factory&&) = delete;

  ~Factory() = default;

  bool registerObject(const IdentifierType& id, ProductCreator creator) {
    return _callbacks.insert({ static_cast<UnderlyingIdentifierType>(id), creator }).second;
  }

  bool unregisterObject(const IdentifierType& id) {
    return _callbacks.erase(static_cast<UnderlyingIdentifierType>(id)) == 1;
  }

  template <typename I, typename ... ProductParameters>
  AbstractProductPtr createObject(const I& id, ProductParameters&& ... params) {
    const auto creator = _callbacks.find(static_cast<UnderlyingIdentifierType>(id));
    if (creator != _callbacks.end()) {
      return AbstractProductPtr((creator->second)(std::forward<ProductParameters>(params) ...));
    }
    LOG << "Could not load" << templateToString<IdentifierType>() << ": " << id;
    LOG << "Please check your .ini config file.";
    std::exit(-1);
  }

  static Factory & getInstance() {
    static Factory _factory_instance;
    return _factory_instance;
  }

 private:
  Factory() :
    _callbacks() { }
  CallbackMap _callbacks;
};
}  // namespace meta
}  // namespace kahypar
