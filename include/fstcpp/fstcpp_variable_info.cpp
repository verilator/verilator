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
	const uint32_t new_capacity_log2{
		std::max(
			static_cast<uint32_t>(platform::clog2(new_size)),
			static_cast<uint32_t>(kCapacityBaseShift)
		) -
		static_cast<uint32_t>(kCapacityBaseShift)
	};
	uint8_t *new_data{new uint8_t[kCapacityBase << new_capacity_log2]};
	// Copy old data to new memory
	if (m_data != nullptr) {
		const uint64_t old_size{size()};
		std::copy_n(m_data, old_size, new_data);
		delete[] m_data;
	}
	m_data = new_data;
	capacity_log2(new_capacity_log2);
}

}  // namespace fst
