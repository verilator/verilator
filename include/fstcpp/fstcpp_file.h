// SPDX-FileCopyrightText: 2025-2026 Yu-Sheng Lin <johnjohnlys@gmail.com>
// SPDX-FileCopyrightText: 2025-2026 Yoda Lee <lc85301@gmail.com>
// SPDX-License-Identifier: MIT
#pragma once
// direct include
// C system headers
// C++ standard library headers
#include <cstdint>
// Other libraries' .h files.
// Your project's .h files.

namespace fst {

// Original block types from fstapi.h
// FST_BL_HDR = 0,
// FST_BL_VCDATA = 1,
// FST_BL_BLACKOUT = 2,
// FST_BL_GEOM = 3,
// FST_BL_HIER = 4,
// FST_BL_VCDATA_DYN_ALIAS = 5,
// FST_BL_HIER_LZ4 = 6,
// FST_BL_HIER_LZ4DUO = 7,
// FST_BL_VCDATA_DYN_ALIAS2 = 8,
// FST_BL_ZWRAPPER = 254,
// FST_BL_SKIP = 255
enum class BlockType : uint8_t {
	HEADER = 0,
	WAVE_DATA_VERSION1 = 1,  // not implemented
	BLACKOUT = 2,
	GEOMETRY = 3,
	HIERARCHY_GZ_COMPRESSED = 4,  // not implemented
	WAVE_DATA_VERSION2 = 5,       // not implemented
	HIERARCHY_LZ4_COMPRESSED = 6,
	HIERARCHY_LZ4_COMPRESSED_TWICE = 7,  // not implemented
	WAVE_DATA_VERSION3 = 8,

	ZWRAPPER = 254,  // not implemented
	SKIP = 255       // not implemented
};

constexpr unsigned kSharedBlockHeaderSize = 1 /* BlockType */ + 8 /* size (u64) */;

struct HeaderInfo {
	struct Size {
		static constexpr unsigned start_time = 0;
		static constexpr unsigned end_time = 8;
		static constexpr unsigned real_endianness = 8;
		static constexpr unsigned writer_memory_use = 8;
		static constexpr unsigned num_scopes = 8;
		static constexpr unsigned num_vars = 8;
		static constexpr unsigned num_handles = 8;
		static constexpr unsigned num_wave_data_blocks = 8;
		static constexpr unsigned timescale = 1;
		static constexpr unsigned writer = 128;
		static constexpr unsigned date = 26;
		static constexpr unsigned reserved = 93;
		static constexpr unsigned filetype = 1;
		static constexpr unsigned timezero = 8;
	};
	struct Offset {
		static constexpr unsigned start_time = 0;
		static constexpr unsigned end_time = start_time + Size::end_time;
		static constexpr unsigned real_endianness = end_time + Size::real_endianness;
		static constexpr unsigned writer_memory_use = real_endianness + Size::writer_memory_use;
		static constexpr unsigned num_scopes = writer_memory_use + Size::num_scopes;
		static constexpr unsigned num_vars = num_scopes + Size::num_vars;
		static constexpr unsigned num_handles = num_vars + Size::num_vars;
		static constexpr unsigned num_wave_data_blocks = num_handles + Size::num_handles;
		static constexpr unsigned timescale = num_wave_data_blocks + Size::num_wave_data_blocks;
		static constexpr unsigned writer = timescale + Size::timescale;
		static constexpr unsigned date = writer + Size::writer;
		static constexpr unsigned reserved = date + Size::date;
		static constexpr unsigned filetype = reserved + Size::reserved;
		static constexpr unsigned timezero = filetype + Size::filetype;
	};
	static constexpr unsigned total_size = Offset::timezero + Size::timezero;
	static constexpr double kEndianessMagicIdentifier = 2.7182818284590452354;
	static_assert(total_size == 321, "Total size of HeaderInfo must be 321 bytes");
};

}  // namespace fst
