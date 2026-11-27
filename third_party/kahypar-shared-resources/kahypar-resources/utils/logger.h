/*******************************************************************************
 * MIT License
 *
 * This file is part of KaHyPar.
 *
 * Copyright (C) 2015-2017 Sebastian Schlag <sebastian.schlag@kit.edu>
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

#include <iomanip>
#include <iostream>
#include <sstream>
#include <string>

#include "kahypar-resources/meta/pack_expand.h"

namespace kahypar {
class Logger {
 public:
  explicit Logger(const bool newline) :
    _newline(newline),
    _oss() { }

  template <typename Arg, typename ... Args>
  Logger(const bool newline, Arg&& arg, Args&& ... args) :
    _newline(newline),
    _oss() {
    _oss << "[" << std::forward<Arg>(arg);
    meta::expandPack((_oss << ":" << std::forward<Args>(args)) ...);
    _oss << "]: ";
  }

  template <typename T>
  Logger& operator<< (const T& output) {
    _oss << output << ' ';
    return *this;
  }

  template <typename T>
  Logger& operator<< (const T* output) {
    _oss << output << ' ';
    return *this;
  }


  Logger& operator<< (decltype(std::left)& output) {
    _oss << output;
    return *this;
  }

  Logger& operator<< (const decltype(std::setw(1))& output) {
    _oss << output;
    return *this;
  }

  ~Logger() {
    std::cout << _oss.str();
    if (_newline) {
      std::cout << std::endl;
    } else {
      std::cout << ' ';
    }
  }

 private:
  bool _newline;
  std::ostringstream _oss;
};

class LoggerVoidify {
 public:
  void operator& (Logger&) { }
};
}  // namespace kahypar
