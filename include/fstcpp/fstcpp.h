// SPDX-FileCopyrightText: 2025-2026 Yu-Sheng Lin <johnjohnlys@gmail.com>
// SPDX-FileCopyrightText: 2025-2026 Yoda Lee <lc85301@gmail.com>
// SPDX-License-Identifier: MIT
#pragma once
// direct include
// C system headers
// C++ standard library headers
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <utility>
// Other libraries' .h files.
// Your project's .h files.

// Remove these when we upgrade to C++20
#pragma GCC diagnostic ignored "-Wpragmas"
#pragma GCC diagnostic ignored "-Wc++17-attribute-extensions"
#pragma GCC diagnostic ignored "-Wc++20-attribute-extensions"

namespace fst {

typedef uint32_t Handle;
typedef uint32_t EnumHandle;
using string_view_pair = std::pair<const char *, std::size_t>;

[[maybe_unused]]
static inline string_view_pair make_string_view_pair(const char *data) {
	if (not data) {
		return {nullptr, 0};
	}
	return {data, std::strlen(data)};
}
[[maybe_unused]]
static inline string_view_pair make_string_view_pair(const char *data, std::size_t size) {
	return {data, size};
}

enum class WriterPackType : uint8_t {
	ZLIB = 0,    // not supported
	FASTLZ = 1,  // not supported
	LZ4 = 2,
	// usually for testing, you should use eLz4
	// This will turn off compression for geometry/hierarchy/wave data
	NO_COMPRESSION = 3,
};

enum class FileType : uint8_t {
	VERILOG = 0,
	VHDL,
	VERILOG_VHDL,
};

enum class EncodingType : uint8_t {
	BINARY = 0,   // 1 bit per bit to represent 0,1
	VERILOG = 1,  // 2 bits per bit to represent X,Z
	VHDL = 2,     // 4 bits per bit to represent H,U,W,L,-,?
};
[[maybe_unused]]
static inline constexpr unsigned BitPerEncodedBit(EncodingType type) {
	return 1 << static_cast<uint8_t>(type);
}
[[maybe_unused]]
static const char* kEncodedBitToCharTable = (
	"01" // Binary
	"xzhu" // Verilog
	"wl-?    " // Vhdl (padded with ' ')
);

struct Hierarchy {
	enum class ScopeType : uint8_t {
		VCD_MODULE = 0,
		VCD_TASK = 1,
		VCD_FUNCTION = 2,
		VCD_BEGIN = 3,
		VCD_FORK = 4,
		VCD_GENERATE = 5,
		VCD_STRUCT = 6,
		VCD_UNION = 7,
		VCD_CLASS = 8,
		VCD_INTERFACE = 9,
		VCD_PACKAGE = 10,
		VCD_PROGRAM = 11,
		VHDL_ARCHITECTURE = 12,
		VHDL_PROCEDURE = 13,
		VHDL_FUNCTION = 14,
		VHDL_RECORD = 15,
		VHDL_PROCESS = 16,
		VHDL_BLOCK = 17,
		VHDL_FORGENERATE = 18,
		VHDL_IFGENERATE = 19,
		VHDL_GENERATE = 20,
		VHDL_PACKAGE = 21,
	};

	enum class ScopeControlType : uint8_t {
		GEN_ATTR_BEGIN = 252,
		GEN_ATTR_END = 253,
		VCD_SCOPE = 254,
		VCD_UPSCOPE = 255,
	};

	enum class VarType : uint8_t {
		VCD_EVENT = 0,
		VCD_INTEGER = 1,
		VCD_PARAMETER = 2,
		VCD_REAL = 3,
		VCD_REAL_PARAMETER = 4,
		VCD_REG = 5,
		VCD_SUPPLY0 = 6,
		VCD_SUPPLY1 = 7,
		VCD_TIME = 8,
		VCD_TRI = 9,
		VCD_TRIAND = 10,
		VCD_TRIOR = 11,
		VCD_TRIREG = 12,
		VCD_TRI0 = 13,
		VCD_TRI1 = 14,
		VCD_WAND = 15,
		VCD_WIRE = 16,
		VCD_WOR = 17,
		VCD_PORT = 18,
		VCD_SPARRAY = 19,
		VCD_REALTIME = 20,
		GEN_STRING = 21,
		SV_BIT = 22,
		SV_LOGIC = 23,
		SV_INT = 24,
		SV_SHORTINT = 25,
		SV_LONGINT = 26,
		SV_BYTE = 27,
		SV_ENUM = 28,
		SV_SHORTREAL = 29,
	};

	enum class VarDirection : uint8_t {
		MIN = 0,

		IMPLICIT = 0,
		INPUT = 1,
		OUTPUT = 2,
		INOUT = 3,
		BUFFER = 4,
		LINKAGE = 5,

		MAX = 5,
	};

	enum class AttrType : uint8_t {
		MIN = 0,
		MISC = 0,
		ARRAY = 1,
		ENUM = 2,
		PACK = 3,
		MAX = 3,
	};

	enum class AttrSubType : uint8_t {
		// For AttrType::eMisc
		MISC_MIN = 0,
		MISC_COMMENT = 0,
		MISC_ENVVAR = 1,
		MISC_SUPVAR = 2,
		MISC_PATHNAME = 3,
		MISC_SOURCESTEM = 4,
		MISC_SOURCEISTEM = 5,
		MISC_VALUELIST = 6,
		MISC_ENUMTABLE = 7,
		MISC_UNKNOWN = 8,
		MISC_MAX = 8,

		// For AttrType::eArray
		ARRAY_MIN = 0,
		ARRAY_NONE = 0,
		ARRAY_UNPACKED = 1,
		ARRAY_PACKED = 2,
		ARRAY_SPARSE = 3,
		ARRAY_MAX = 3,

		// For AttrType::eEnum
		ENUM_MIN = 0,
		ENUM_SV_INTEGER = 0,
		ENUM_SV_BIT = 1,
		ENUM_SV_LOGIC = 2,
		ENUM_SV_INT = 3,
		ENUM_SV_SHORTINT = 4,
		ENUM_SV_LONGINT = 5,
		ENUM_SV_BYTE = 6,
		ENUM_SV_UNSIGNED_INTEGER = 7,
		ENUM_SV_UNSIGNED_BIT = 8,
		ENUM_SV_UNSIGNED_LOGIC = 9,
		ENUM_SV_UNSIGNED_INT = 10,
		ENUM_SV_UNSIGNED_SHORTINT = 11,
		ENUM_SV_UNSIGNED_LONGINT = 12,
		ENUM_SV_UNSIGNED_BYTE = 13,
		ENUM_REG = 14,
		ENUM_TIME = 15,
		ENUM_MAX = 15,

		// For AttrType::ePack
		PACK_MIN = 0,
		PACK_NONE = 0,
		PACK_UNPACKED = 1,
		PACK_PACKED = 2,
		PACK_SPARSE = 3,
		PACK_MAX = 3,
	};

	enum class SupplementalVarType : uint8_t {};

	enum class SupplementalDataType : uint8_t {};
};

struct Header {
	uint64_t start_time = uint64_t(-1);
	uint64_t end_time = 0;
	int64_t timezero = 0;
	// Match the original fstapi.c. Just for information, not used in FST.
	uint64_t writer_memory_use = 1ull << 27;
	uint64_t num_scopes = 0;
	uint64_t num_vars = 0;     // #CreateVar calls, including aliases
	uint64_t num_handles = 0;  // #unique handles, excluding aliases, shall be <= num_vars
	uint64_t num_value_change_data_blocks = 0;
	char writer[128]{};
	char date[26]{};
	FileType filetype = FileType::VERILOG;
	int8_t timescale = -9;
};

static constexpr uint64_t kInvalidTime = uint64_t(-1);

}  // namespace fst
