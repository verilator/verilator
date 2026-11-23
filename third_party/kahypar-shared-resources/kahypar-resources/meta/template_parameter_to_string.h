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

#include <algorithm>
#include <cstdlib>
#include <locale>
#include <memory>
#include <string>
#include <typeinfo>

// based on http://stackoverflow.com/questions/281818/unmangling-the-result-of-stdtype-infoname
#ifdef __GNUG__
#include <cxxabi.h>

namespace kahypar {
namespace meta {
template <typename T>
std::string templateToString() {
  std::string ret = std::unique_ptr<char, void (*)(void*)>{
    abi::__cxa_demangle(typeid(T).name(), nullptr, nullptr, nullptr),
    std::free
  }.get();
  ret.erase(std::remove_if(ret.begin(), ret.end(), ::isspace), ret.end());
  return ret;
}
}  // namespace meta
}  // namespace kahypar
#else
namespace kahypar {
namespace meta {
template <typename T>
std::string templateToString() {
  std::string ret(typeid(T).name());
  ret.erase(std::remove_if(ret.begin(), ret.end(), ::isspace), ret.end());
  return ret;
}
}  // namespace meta
}  // namespace kahypar
#endif

namespace kahypar {
namespace meta {
template <bool value>
std::string templateToString() {
  if (value) {
    return std::string("true");
  }
  return std::string("false");
}
}  // namespace meta
}  // namespace kahypar
