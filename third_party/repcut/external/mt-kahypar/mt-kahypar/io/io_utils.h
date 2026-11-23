/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2019 Lars Gottesbüren <lars.gottesbueren@kit.edu>
 * Copyright (C) 2019 Tobias Heuer <tobias.heuer@kit.edu>
 * Copyright (C) 2026 Nikolai Maas <nikolai.maas@kit.edu>
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

#include <fcntl.h>
#include <string>
#include <string_view>
#include <thread>
#include <sys/stat.h>

#if _WIN32
#include <windows.h>
#else
#include <sys/mman.h>
#include <unistd.h>
#endif

#include <tbb/parallel_for.h>

#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/utils/exception.h"

namespace mt_kahypar {
namespace io {

#if _WIN32
struct FileHandle {
  HANDLE hFile;
  HANDLE hMem;
  char* mapped_file;
  size_t length;

  void closeHandle() {
    CloseHandle(hFile);
    CloseHandle(hMem);
  }
};
#else
struct FileHandle {
  int fd;
  char* mapped_file;
  size_t length;

  void closeHandle() {
    close(fd);
  }
};
#endif

size_t file_size(const std::string& filename) {
  struct stat stat_buf;
  const int res = stat( filename.c_str(), &stat_buf);
  if (res < 0) {
    throw InvalidInputException("Could not open: " + filename);
  }
  return static_cast<size_t>(stat_buf.st_size);
}

FileHandle mmap_file(const std::string& filename) {
  FileHandle handle;
  handle.length = file_size(filename);

  #ifdef _WIN32
    PSECURITY_DESCRIPTOR pSD;
    SECURITY_ATTRIBUTES  sa;

    /* create security descriptor (needed for Windows NT) */
    pSD = (PSECURITY_DESCRIPTOR) malloc( SECURITY_DESCRIPTOR_MIN_LENGTH );
    if( pSD == NULL ) {
      throw SystemException("Error while creating security descriptor!");
    }

    InitializeSecurityDescriptor(pSD, SECURITY_DESCRIPTOR_REVISION);
    SetSecurityDescriptorDacl(pSD, TRUE, (PACL) NULL, FALSE);

    sa.nLength = sizeof(sa);
    sa.lpSecurityDescriptor = pSD;
    sa.bInheritHandle = TRUE;

    // open file
    handle.hFile = CreateFile ( filename.c_str(), GENERIC_READ, FILE_SHARE_READ,
      &sa, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);

    if (handle.hFile == INVALID_HANDLE_VALUE) {
      free( pSD);
      throw InvalidInputException("Invalid file handle when opening: " + filename);
    }

    // Create file mapping
    handle.hMem = CreateFileMapping( handle.hFile, &sa, PAGE_READONLY, 0, handle.length, NULL);
    free(pSD);
    if (handle.hMem == NULL) {
      throw InvalidInputException("Invalid file mapping when opening: " + filename);
    }

    // map file to memory
    handle.mapped_file = (char*) MapViewOfFile(handle.hMem, FILE_MAP_READ, 0, 0, 0);
    if ( handle.mapped_file == NULL ) {
      throw SystemException("Failed to map file to main memory:" + filename);
    }
  #else
    handle.fd = open(filename.c_str(), O_RDONLY);
    if ( handle.fd < -1 ) {
      throw InvalidInputException("Could not open: " + filename);
    }
    handle.mapped_file = (char*) mmap(0, handle.length, PROT_READ, MAP_PRIVATE, handle.fd, 0);
    if ( handle.mapped_file == MAP_FAILED ) {
      close(handle.fd);
      throw SystemException("Error while mapping file to memory");
    }
  #endif

  return handle;
}

void munmap_file(FileHandle& handle) {
  #ifdef _WIN32
  UnmapViewOfFile(handle.mapped_file);
  #else
  munmap(handle.mapped_file, handle.length);
  #endif
  handle.closeHandle();
}

void parsing_exception(const std::string& msg) {
  throw InvalidInputException("input file: " + msg);
}

void parsing_exception(size_t line, const std::string& msg) {
  throw InvalidInputException("input file (line " + STR(line) + "): " + msg);
}

MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
bool is_line_ending(char* mapped_file, size_t pos) {
  return mapped_file[pos] == '\r' || mapped_file[pos] == '\n' || mapped_file[pos] == '\0';
}

MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
void do_line_ending(char* mapped_file, size_t& pos, size_t& current_line) {
  if (!is_line_ending(mapped_file, pos)) {
    parsing_exception(current_line, "unexpected content at end of line");
  }

  if (mapped_file[pos] != '\0') {
    if (mapped_file[pos] == '\r') {     // windows line ending
      ++pos;
      if (mapped_file[pos] != '\n') {
        parsing_exception(current_line, "invalid symbol (carriage return without newline)");
      }
    }
    ++pos;
    ++current_line;
  }
}

MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
void goto_next_line(char* mapped_file, size_t& pos, size_t& current_line, const size_t length) {
  unused(length);
  for ( ; ; ++pos ) {
    ASSERT(pos < length || mapped_file[pos] == '\0');
    if ( is_line_ending(mapped_file, pos) ) {
      do_line_ending(mapped_file, pos, current_line);
      break;
    }
  }
}

MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
void goto_next_line_unchecked(char* mapped_file, size_t& pos, size_t& current_line, const size_t length) {
  std::string_view sv(mapped_file + pos, length - pos);
  size_t offset = sv.find('\n');  // compiles to memchr

  if (offset != std::string_view::npos) {
    ASSERT(is_line_ending(mapped_file, pos + offset));
    pos += (offset + 1);
    ++current_line;
  } else {
    pos = length;
  }
}

template<typename ResultType>
MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
ResultType read_number(char* mapped_file, size_t& pos, const size_t current_line, const size_t length, const char* expected_type) {
  while ( mapped_file[pos] == ' ' ) {
    ++pos;
  }
  if ( is_line_ending(mapped_file, pos) ) {
    parsing_exception(current_line, std::string("expected to find ") + expected_type + ", but line already ends");
  }

  ResultType number = 0;
  for ( ; pos < length; ++pos ) {
    if ( mapped_file[pos] == ' ' || is_line_ending(mapped_file, pos) ) {
      while ( mapped_file[pos] == ' ' ) {
        ++pos;
      }
      break;
    }
    if (mapped_file[pos] < '0' || mapped_file[pos] > '9') {
      parsing_exception(current_line, "invalid symbol: " + std::string(1, mapped_file[pos]));
    }

    ResultType digit = mapped_file[pos] - '0';
    if (number > (std::numeric_limits<ResultType>::max() - digit) / 10) {
      // if the number would overflow, read the whole number and return a nice error message
      std::string number_as_string = STR(number);
      for ( ; mapped_file[pos] != ' ' && !is_line_ending(mapped_file, pos); ++pos ) {
        number_as_string += mapped_file[pos];
      }
      std::string msg = std::string("number overflows input range for ") + expected_type + ": " + number_as_string;
      if constexpr (sizeof(ResultType) < 8) {
        msg += " (build with -DKAHYPAR_USE_64_BIT_IDS=ON to support larger ID ranges)";
      }
      parsing_exception(current_line, msg);
    }
    number = number * 10 + (mapped_file[pos] - '0');
  }
  return number;
}

struct LineRange {
  const size_t start;
  const size_t end;
  const size_t line_start_index;
  const size_t num_lines;
  const size_t first_line_number_in_file;
};

size_t num_parallel_ranges() {
  return 2 * std::thread::hardware_concurrency();
}

vec<LineRange> split_lines(char* mapped_file,
                           size_t& pos,
                           size_t& current_line,
                           const size_t length,
                           const size_t expected_num_lines) {
  const size_t initial_pos = pos;
  vec<std::pair<size_t, size_t>> line_positions;
  line_positions.reserve(expected_num_lines + 1);

  // find line endings very fast
  line_positions.emplace_back(pos, current_line);
  while ( true ) {
    // skip comments
    while ( mapped_file[pos] == '%' && pos < length ) {
      goto_next_line_unchecked(mapped_file, pos, current_line, length);
    }

    if ( line_positions.size() > expected_num_lines || pos >= length ) break;

    goto_next_line_unchecked(mapped_file, pos, current_line, length);
    line_positions.emplace_back(pos, current_line);
  }
  if ( line_positions.size() < expected_num_lines + 1 && mapped_file[pos - 1] == '\n' ) {
    // special case for last line that is not terminated by a newline (might be end of file or empty line)
    line_positions.emplace_back(pos, current_line);
  }

  if ( line_positions.size() < expected_num_lines + 1 ) {  // note: +1 for header line
    parsing_exception("expected " + STR(expected_num_lines + 1) + " lines, but there are only " +
                      STR(line_positions.size()) + " lines (excluding comments)");
  }

  // split the lines into ranges that can be processed in parallel
  const size_t num_ranges = num_parallel_ranges();
  const size_t bytes_per_range = (pos - initial_pos) / num_ranges + 1;

  vec<LineRange> result;
  result.reserve(num_ranges);
  size_t line_index = 0;
  while (line_index + 1 < line_positions.size()) {
    const size_t start_index = line_index;
    const auto [start_pos, line_in_file] = line_positions[start_index];

    size_t delta_pos = 0;
    do {
      ++line_index;
      delta_pos = line_positions[line_index].first - start_pos;
    } while (line_index + 1 < line_positions.size() && delta_pos < bytes_per_range);

    if (delta_pos > 0) {
      result.push_back(LineRange{ start_pos, start_pos + delta_pos, start_index, line_index - start_index, line_in_file });
    }
  }
  ASSERT(result.size() <= num_ranges);
  ASSERT(result.empty() || result.back().end == line_positions.back().first);
  return result;
}

template<typename T>
size_t copy_to_global_list(const vec<vec<T>>& source, vec<T>& target) {
  vec<size_t> prefix_sum;
  prefix_sum.reserve(source.size() + 1);
  prefix_sum.push_back(0);
  size_t sum = 0;
  for (const auto& local_list: source) {
    sum += local_list.size();
    prefix_sum.push_back(sum);
  }

  tbb::parallel_for(UL(0), source.size(), [&](const size_t i) {
    const size_t start = prefix_sum[i];
    const size_t end = prefix_sum[i + 1];
    for (size_t j = 0; start + j < std::min(end, target.size()); ++j) {
      ASSERT(j < source[i].size());
      target[start + j] = source[i][j];
    }
  });
  return prefix_sum.back();
}

}  // namespace io
}  // namespace mt_kahypar
