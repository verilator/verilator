// SPDX-FileCopyrightText: 2026 Yu-Sheng Lin <johnjohnlys@gmail.com>
// SPDX-License-Identifier: MIT
// Project: libfstwriter
// Website: https://github.com/gtkwave/libfstwriter
// direct include
#include "fstcpp/fstcpp_variable_info.h"
// C system headers
// C++ standard library headers
#include <algorithm>
// Other libraries' .h files.
// Your project's .h files.

namespace fst {

// I don't know why I need to define them here, but StackOverflow says it
constexpr uint64_t VariableInfo::kCapacityBaseShift;
constexpr uint64_t VariableInfo::kCapacityBase;

void VariableInfo::reallocate(uint64_t new_size) {
	// Allocate new memory
	const uint32_t new_capacity_log2 =
		std::max(platform::clog2(new_size), kCapacityBaseShift) - kCapacityBaseShift;
	uint8_t *new_data = new uint8_t[kCapacityBase << new_capacity_log2];
	// Copy old data to new memory
	if (data != nullptr) {
		const uint64_t old_size = size();
		std::copy_n(data, old_size, new_data);
		delete[] data;
	}
	data = new_data;
	capacity_log2(new_capacity_log2);
}

}  // namespace fst
