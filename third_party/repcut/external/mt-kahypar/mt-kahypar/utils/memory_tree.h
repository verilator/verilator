/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2019 Tobias Heuer <tobias.heuer@kit.edu>
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

#include <map>
#include <string>
#include <memory>
#include <cstdint>

namespace mt_kahypar::utils {

enum class OutputType : uint8_t {
  BYTES = 0,
  KILOBYTE = 1,
  MEGABYTE = 2,
  PERCENTAGE = 3
};

class MemoryTreeNode {

 using map_type = std::map<std::string, std::unique_ptr<MemoryTreeNode>>;

 public:
  MemoryTreeNode(const std::string& name, const OutputType& output_type = OutputType::MEGABYTE);

  MemoryTreeNode* addChild(const std::string& name, const size_t size_in_bytes = 0);

  void updateSize(const size_t delta) {
    _size_in_bytes += delta;
  }

  void finalize();

 private:

  void dfs(std::ostream& str, const size_t parent_size_in_bytes, int level) const ;
  void print(std::ostream& str, const size_t parent_size_in_bytes, int level) const ;

  friend std::ostream& operator<<(std::ostream& str, const MemoryTreeNode& root);

  std::string _name;
  size_t _size_in_bytes;
  OutputType _output_type;
  map_type _children;
};


std::ostream & operator<< (std::ostream& str, const MemoryTreeNode& root);

}  // namespace mt_kahypar