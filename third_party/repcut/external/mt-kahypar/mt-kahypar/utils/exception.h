/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2023 Tobias Heuer <tobias.heuer@kit.edu>
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

#include <exception>
#include <string>
#include <sstream>

#include "mt-kahypar/macros.h"

namespace mt_kahypar {

template<class Derived>
class MtKaHyParException : public std::exception {

 public:
  MtKaHyParException(const std::string& what) :
    _what("") {
    std::stringstream ss;
    ss << RED << "[" << Derived::TYPE << "] " << END << " " << what;
    _what = ss.str();
  }

  const char * what () const throw () {
    return _what.c_str();
  }

 private:
  std::string _what;
};

class InvalidInputException : public MtKaHyParException<InvalidInputException> {

  using Base = MtKaHyParException<InvalidInputException>;

 public:
  static constexpr char TYPE[] = "Invalid Input";

  InvalidInputException(const std::string& what) :
    Base(what) { }
};

class InvalidParameterException : public MtKaHyParException<InvalidParameterException> {

  using Base = MtKaHyParException<InvalidParameterException>;

 public:
  static constexpr char TYPE[] = "Invalid Parameter";

  InvalidParameterException(const std::string& what) :
    Base(what) { }
};

class UnsupportedOperationException : public MtKaHyParException<UnsupportedOperationException> {

  using Base = MtKaHyParException<UnsupportedOperationException>;

 public:
  static constexpr char TYPE[] = "Unsupported Operation";

  UnsupportedOperationException(const std::string& what) :
    Base(what) { }
};

class SystemException : public MtKaHyParException<SystemException> {

  using Base = MtKaHyParException<SystemException>;

 public:
  static constexpr char TYPE[] = "System Error";

  SystemException(const std::string& what) :
    Base(what) { }
};

}  // namespace mt_kahypar