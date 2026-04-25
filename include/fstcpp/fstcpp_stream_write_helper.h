// SPDX-FileCopyrightText: 2025-2026 Yu-Sheng Lin <johnjohnlys@gmail.com>
// SPDX-FileCopyrightText: 2025-2026 Yoda Lee <lc85301@gmail.com>
// SPDX-License-Identifier: MIT
// Project: libfstwriter
// Website: https://github.com/gtkwave/libfstwriter
#pragma once
// direct include
// C system headers
// C++ standard library headers
#if defined(__cplusplus) && __cplusplus >= 202302L
#	include <bit>
#endif
#include <cstdint>
#include <cstring>
#include <vector>
// Other libraries' .h files.
// Your project's .h files.
#include "fstcpp/fstcpp.h"
#include "fstcpp/fstcpp_file.h"

namespace fst {

namespace platform {

// For C++14
// Can remove once C++23 is required
#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
// clang-format off
template <typename U> U to_big_endian(U u) { return u; }
#else
#if defined(__cplusplus) && __cplusplus >= 202302L
template <typename U, size_t S>
U to_big_endian(U u, std::integral_constant<size_t, S>) {
	return std::byteswap(u);
}
#elif USE_GCC_INTRINSIC
template<typename U> U to_big_endian(U u, std::integral_constant<size_t, 1>) { return u; }
template<typename U> U to_big_endian(U u, std::integral_constant<size_t, 2>) { return __builtin_bswap16(u); }
template<typename U> U to_big_endian(U u, std::integral_constant<size_t, 4>) { return __builtin_bswap32(u); }
template<typename U> U to_big_endian(U u, std::integral_constant<size_t, 8>) { return __builtin_bswap64(u); }
// TODO: implement MSVC version
// #elif USE_MSVC_INTRINSIC
#else
template <typename U, size_t S>
U to_big_endian(U u, std::integral_constant<size_t, S>) {
	U ret{0};
	for (size_t i = 0; i < S; ++i) {
		ret = (ret << 8) | (u & 0xff);
		u >>= 8;
	}
	return ret;
}
#endif
// clang-format on
template <typename U>
U to_big_endian(U u) {
	return platform::to_big_endian(u, std::integral_constant<size_t, sizeof(U)>());
}
#endif

}  // namespace platform

struct StreamWriteHelper {
	std::ostream *m_os{nullptr};

	StreamWriteHelper(std::ostream &os_) : m_os{&os_} {}
	StreamWriteHelper(std::ostream *os_) : m_os{os_} {}

	// Write the entire uint, big-endian
	// We do not provide little-endian version since FST only uses big-endian
	template <typename U>
	StreamWriteHelper &writeUInt(U u) {
		u = platform::to_big_endian(u);
		m_os->write(reinterpret_cast<const char *>(&u), sizeof(u));
		return *this;
	}

	// Write the uint, big-endian, left-aligned but only (bitwidth+7)/8 bytes
	// This is a very special case for value changes
	// For example, if the value is 10-bits (e.g. logic [9:0] in Verilog),
	// then the first byte will be [9-:8], then {[1:0], 6'b0}.
	template <typename U>
	StreamWriteHelper &writeUIntPartialForValueChange(U u, size_t bitwidth) {
		// Shift left to align the MSB to the MSB of the uint
		u <<= sizeof(u) * 8 - bitwidth;
		// Write the first (bitwidth+7)/8 bytes
		u = platform::to_big_endian(u);
		m_os->write(reinterpret_cast<const char *>(&u), (bitwidth + 7) / 8);
		return *this;
	}

	StreamWriteHelper &writeLEB128(uint64_t v) {
		// Just reuse the logic from fstapi.c, is there a better way?
		uint64_t nxt{0};
		unsigned char buf[10]{}; /* ceil(64/7) = 10 */
		unsigned char *pnt{buf};
		int len{0};
		while ((nxt = v >> 7)) {
			*(pnt++) = ((unsigned char)v) | 0x80;
			v = nxt;
		}
		*(pnt++) = (unsigned char)v;
		len = static_cast<int>(pnt - buf);
		m_os->write(reinterpret_cast<const char *>(buf), len);
		return *this;
	}

	StreamWriteHelper &writeLEB128Signed(int64_t v) {
		// Just reuse the logic from fstapi.c, is there a better way?
		unsigned char buf[15]{}; /* ceil(64/7) = 10 + sign byte padded way up */
		unsigned char byt{0};
		unsigned char *pnt{buf};
		int more{1};
		int len{0};
		do {
			byt = static_cast<unsigned char>(v | 0x80);
			v >>= 7;

			if (((!v) && (!(byt & 0x40))) || ((v == -1) && (byt & 0x40))) {
				more = 0;
				byt &= 0x7f;
			}

			*(pnt++) = byt;
		} while (more);
		len = static_cast<int>(pnt - buf);
		m_os->write(reinterpret_cast<const char *>(buf), len);
		return *this;
	}

	template <typename F>
	StreamWriteHelper &writeFloat(F f) {
		// Always write in native endianness
		m_os->write(reinterpret_cast<const char *>(&f), sizeof(f));
		return *this;
	}

	StreamWriteHelper &writeBlockHeader(fst::BlockType block_type, uint64_t block_length) {
		return (
			this  //
				->writeUInt(static_cast<uint8_t>(block_type))
				.writeUInt(
					block_length + 8
				)  // The 8 is required by FST, which is the size of this uint64_t
		);
	}

	// Write the string, non-null-terminated
	StreamWriteHelper &writeString(const fst::string_view_pair str) {
		m_os->write(str.m_data, str.m_size);
		return *this;
	}

	// Write the string, null-terminated
	StreamWriteHelper &writeString0(const fst::string_view_pair str) {
		m_os->write(str.m_data, str.m_size).put('\0');
		return *this;
	}
	StreamWriteHelper &writeString(const std::string &str) {
		return writeString0(fst::make_string_view_pair(str.c_str(), str.size()));
	}
	StreamWriteHelper &writeString(const char *str) {
		return writeString0(fst::make_string_view_pair(str));
	}

	StreamWriteHelper &write(const char *ptr, size_t size) {
		m_os->write(ptr, size);
		return *this;
	}

	StreamWriteHelper &write(const uint8_t *ptr, size_t size) {
		m_os->write(reinterpret_cast<const char *>(ptr), size);
		return *this;
	}

	StreamWriteHelper &seek(std::streamoff pos, std::ios_base::seekdir dir) {
		m_os->seekp(pos, dir);
		return *this;
	}

	StreamWriteHelper &fill(char fill_char, size_t size) {
		if (size > 32) {
			// optimize large fills
			constexpr unsigned s_kChunkSize = 16;
			char buf[s_kChunkSize]{};
			std::memset(buf, fill_char, s_kChunkSize);
			for (size_t i{0}; i < size / s_kChunkSize; ++i) {
				m_os->write(buf, s_kChunkSize);
			}
			size %= s_kChunkSize;
		}
		for (size_t i{0}; i < size; ++i) {
			m_os->put(fill_char);
		}
		return *this;
	}

	// Handy functions for writing variable length data, you can
	// cascade multiple write() calls after RecordOffset(), then
	// call DiffOffset() to get the total number of bytes written.

	// (1)
	// std::streamoff diff;
	// h
	// .beginOffset(diff)
	// .write(...)
	// ... do other stuff ...
	// .endOffset(&diff); <-- diff will be set to the number of bytes written
	// (2)
	// std::streamoff pos, diff;
	// h
	// .beginOffset(pos)
	// .write(...)
	// ... do other stuff ...
	// .endOffset(&diff, pos); <-- diff will be set to the number of bytes written

	// The API uses pointer on purpose to prevent you pass (pos, diff) as arguments
	// to endOffset(), which is a common mistake.

	StreamWriteHelper &beginOffset(std::streamoff &pos) {
		pos = m_os->tellp();
		return *this;
	}

	StreamWriteHelper &endOffset(std::streamoff *diff) {
		// diff shall store previous position before calling this function
		*diff = m_os->tellp() - *diff;
		return *this;
	}

	StreamWriteHelper &endOffset(std::streamoff *diff, std::streamoff pos) {
		*diff = m_os->tellp() - pos;
		return *this;
	}
};

struct StreamVectorWriteHelper {
	std::vector<uint8_t> &m_vec;

	StreamVectorWriteHelper(std::vector<uint8_t> &vec_) : m_vec{vec_} {}

	template <typename T>
	StreamVectorWriteHelper &write(T u) {
		const size_t s = sizeof(u);
		m_vec.resize(m_vec.size() + s);
		std::memcpy(m_vec.data() + m_vec.size() - s, &u, s);
		return *this;
	}

	template <typename T>
	StreamVectorWriteHelper &fill(T u, size_t count) {
		const size_t s = sizeof(u) * count;
		m_vec.resize(m_vec.size() + s);
		for (size_t i{0}; i < count; ++i) {
			std::memcpy(m_vec.data() + m_vec.size() - s + i * sizeof(u), &u, sizeof(u));
		}
		return *this;
	}

	template <typename T>
	StreamVectorWriteHelper &write(T *u, size_t size) {
		const size_t s = sizeof(u) * size;
		m_vec.resize(m_vec.size() + s);
		std::memcpy(m_vec.data() + m_vec.size() - s, u, s);
		return *this;
	}

	template <typename E>
	StreamVectorWriteHelper &writeU8Enum(E e) {
		m_vec.push_back(static_cast<uint8_t>(e));
		return *this;
	}

	// Write the entire uint, big-endian
	// We do not provide little-endian version since FST only uses big-endian
	template <typename U>
	StreamVectorWriteHelper &writeUIntBE(U u) {
		u = platform::to_big_endian(u);
		const size_t s = sizeof(u);
		m_vec.resize(m_vec.size() + s);
		std::memcpy(m_vec.data() + m_vec.size() - s, &u, s);
		return *this;
	}

	// Write the uint, big-endian, left-aligned but only (bitwidth+7)/8 bytes
	// This is a very special case for value changes
	// For example, if the value is 10-bits (e.g. logic [9:0] in Verilog),
	// then the first byte will be [9-:8], then {[1:0], 6'b0}.
	template <typename U>
	StreamVectorWriteHelper &writeUIntPartialForValueChange(U u, size_t bitwidth) {
		// Shift left to align the MSB to the MSB of the uint
		u <<= sizeof(u) * 8 - bitwidth;
		// Write the first (bitwidth+7)/8 bytes
		u = platform::to_big_endian(u);
		const size_t s = (bitwidth + 7) / 8;
		m_vec.resize(m_vec.size() + s);
		std::memcpy(m_vec.data() + m_vec.size() - s, &u, s);
		return *this;
	}

	StreamVectorWriteHelper &writeLEB128(uint64_t v) {
		// Just reuse the logic from fstapi.c, is there a better way?
		uint64_t nxt{0};
		unsigned char buf[10]{}; /* ceil(64/7) = 10 */
		unsigned char *pnt{buf};
		int len{0};
		while ((nxt = v >> 7)) {
			*(pnt++) = ((unsigned char)v) | 0x80;
			v = nxt;
		}
		*(pnt++) = (unsigned char)v;
		len = static_cast<int>(pnt - buf);

		const size_t cur = m_vec.size();
		m_vec.resize(cur + len);
		std::memcpy(m_vec.data() + cur, buf, len);
		return *this;
	}

	StreamVectorWriteHelper &writeLEB128Signed(int64_t v) {
		// Just reuse the logic from fstapi.c, is there a better way?
		unsigned char buf[15]{}; /* ceil(64/7) = 10 + sign byte padded way up */
		unsigned char byt{0};
		unsigned char *pnt{buf};
		int more{1};
		int len{0};
		do {
			byt = static_cast<unsigned char>(v | 0x80);
			v >>= 7;

			if (((!v) && (!(byt & 0x40))) || ((v == -1) && (byt & 0x40))) {
				more = 0;
				byt &= 0x7f;
			}

			*(pnt++) = byt;
		} while (more);
		len = static_cast<int>(pnt - buf);

		const size_t cur = m_vec.size();
		m_vec.resize(cur + len);
		std::memcpy(m_vec.data() + cur, buf, len);
		return *this;
	}

	StreamVectorWriteHelper &writeBlockHeader(fst::BlockType block_type, uint64_t block_length) {
		return (
			this  //
				->writeUIntBE(static_cast<uint8_t>(block_type))
				.writeUIntBE(
					block_length + 8
				)  // The 8 is required by FST, which is the size of this uint64_t
		);
	}

	// Write the string, non-null-terminated
	StreamVectorWriteHelper &writeString(const fst::string_view_pair str) {
		if (str.m_size != 0) {
			const size_t len = str.m_size;
			const size_t cur = m_vec.size();
			m_vec.resize(cur + len);
			std::memcpy(m_vec.data() + cur, str.m_data, len);
		}
		return *this;
	}

	// Write the string, null-terminated
	StreamVectorWriteHelper &writeString0(const fst::string_view_pair str) {
		if (str.m_size != 0) {
			const size_t len = str.m_size;
			const size_t cur = m_vec.size();
			m_vec.resize(cur + len + 1);
			std::memcpy(m_vec.data() + cur, str.m_data, len);
			m_vec[cur + len] = '\0';
		} else {
			m_vec.push_back('\0');
		}
		return *this;
	}
	StreamVectorWriteHelper &writeString(const std::string &str) {
		return writeString0(fst::make_string_view_pair(str.c_str(), str.size()));
	}
	StreamVectorWriteHelper &writeString(const char *str) {
		return writeString0(fst::make_string_view_pair(str));
	}
};

}  // namespace fst
