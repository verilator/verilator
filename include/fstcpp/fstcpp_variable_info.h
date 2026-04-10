// SPDX-FileCopyrightText: 2025-2026 Yu-Sheng Lin <johnjohnlys@gmail.com>
// SPDX-FileCopyrightText: 2025-2026 Yoda Lee <lc85301@gmail.com>
// SPDX-License-Identifier: MIT
// Project: libfstwriter
// Website: https://github.com/gtkwave/libfstwriter
#pragma once
// direct include
#include "fstcpp/fstcpp.h"
// C system headers
// C++ standard library headers
#if defined(__cplusplus) && __cplusplus >= 202002L
#	include <bit>
#endif
#include <algorithm>
#include <cstdint>
#include <limits>
#include <vector>
// Other libraries' .h files.
// Your project's .h files.
#include "fstcpp/fstcpp_assertion.h"
#include "fstcpp/fstcpp_stream_write_helper.h"

namespace fst {

namespace platform {

// Can be replaced with std::bit_width when C++20 is available
inline uint64_t clog2(uint64_t x) {
	if (x <= 1) return 0;
#if defined(__cplusplus) && __cplusplus >= 202002L
	return std::bit_width(x - 1);
#elif USE_GCC_INTRINSIC
	return 64 - __builtin_clzll(x - 1);
// TODO: implement MSVC version
// #elif USE_MSVC_INTRINSIC
#else
	uint64_t r = 0;
	x -= 1;
	auto CheckAndShift = [&](uint64_t shift) {
		if (x >> shift) {
			r += shift;
			x >>= shift;
		}
	};
	CheckAndShift(32);
	CheckAndShift(16);
	CheckAndShift(8);
	CheckAndShift(4);
	CheckAndShift(2);
	CheckAndShift(1);
	r += x;
	return r;
#endif
}

inline constexpr uint32_t gen_mask_safe(unsigned width) {
	// works even when width == 32
	return ((uint32_t(1) << (width - 1)) << 1) - 1;
}

inline uint32_t read_field(const uint32_t src, unsigned width, unsigned offset) {
	const uint32_t mask = gen_mask_safe(width);
	return (src >> offset) & mask;
}

inline void write_field(uint32_t &dst, const uint32_t src, unsigned width, unsigned offset) {
	const uint32_t mask = gen_mask_safe(width) << offset;
	dst = (dst & ~mask) | ((src << offset) & mask);
}

}  // namespace platform

class VariableInfo final {
public:
	static constexpr uint32_t kMaxSupportedBitwidth = 0x7fffff;

private:
	static constexpr uint64_t kCapacityBaseShift = 5;
	static constexpr uint64_t kCapacityBase = 1 << kCapacityBaseShift;

	// To maximize cache efficiency, we compact the data members into 16 bytes.
	// We make use of bitfields to store multiple pieces of information in a single integer.
	// But standard does not guarantee the layout of bitfields (the `int x : N;` syntax),
	// so we use helper functions to access bitfields.

	// begin of data members
	// 1. 8B pointer (assume 64-bit architecture), its size can be:
	//   - 0 if m_data is nullptr
	//   - `kCapacityBase * pow(2, m_capacity_log2)` if m_data is not nullptr
	//   - If we want more bits, we can use the `kCapacityBaseShift` LSB for other purposes.
	uint8_t *m_data{nullptr};
	// 2. 4B size. The same as vector.size(), but we only need 32b.
	uint32_t m_size{0};
	// 3. 4B misc. Highly compacted information for max cache efficiency.
	//    - 6b capacity_log2
	//    - 2b last_encoding_type
	//    - 23b bitwidth
	//    - 1b is_real
	uint32_t m_misc{0};
	// end of data members

	// Note: optimization possibility (not implemented)
	//    - real is always 64-bit double, so we can use 24 bits to encode
	//      is_real and bitwidth together, and bitwidth = (1<<24-1) is a special
	//      value to indicate that the variable is a real.
	//    - Currently bitwidth is whatever you pass to Writer::createVar.
	//    - Not implemented since nobody needs 16M-bit over 8M-bit bitwidth IMO.
	static constexpr uint32_t kIsRealWidth = 1;
	static constexpr uint32_t kBitwidthWidth = 23;
	static constexpr uint32_t kLastEncodingTypeWidth = 2;
	static constexpr uint32_t kCapacityLog2Width = 6;

	static constexpr uint32_t kIsRealOffset = 0;
	static constexpr uint32_t kBitwidthOffset = kIsRealOffset + kIsRealWidth;
	static constexpr uint32_t kLastEncodingTypeOffset = kBitwidthOffset + kBitwidthWidth;
	static constexpr uint32_t kCapacityLog2Offset =
		kLastEncodingTypeOffset + kLastEncodingTypeWidth;

	void capacity_log2(uint32_t capacity_log2_) {
		platform::write_field(m_misc, capacity_log2_, kCapacityLog2Width, kCapacityLog2Offset);
	}
	uint32_t capacity() const {
		if (m_data == nullptr) {
			return 0;
		}
		return kCapacityBase << platform::read_field(
				   m_misc, kCapacityLog2Width, kCapacityLog2Offset
			   );
	}

	bool need_reallocate(uint64_t new_size) const { return capacity() < new_size; }
	// This function is cold, so we don't inline it
	void reallocate(uint64_t new_size);

	void size(uint64_t s) { m_size = static_cast<uint32_t>(s); }

public:
	uint64_t size() const { return m_size; }
	uint32_t bitwidth() const {
		return platform::read_field(m_misc, kBitwidthWidth, kBitwidthOffset);
	}
	bool is_real() const { return bool(platform::read_field(m_misc, kIsRealWidth, kIsRealOffset)); }
	void last_written_encode_type(EncodingType encoding_) {
		platform::write_field(
			m_misc,
			static_cast<uint32_t>(encoding_),
			kLastEncodingTypeWidth,
			kLastEncodingTypeOffset
		);
	}
	EncodingType last_written_encode_type() const {
		return static_cast<EncodingType>(
			platform::read_field(m_misc, kLastEncodingTypeWidth, kLastEncodingTypeOffset)
		);
	}
	uint64_t last_written_bytes() const;

	template <typename Callable, typename... Args>
	auto dispatchHelper(Callable &&callable, Args &&...args) const;

	VariableInfo(uint32_t bitwidth_, bool is_real_ = false);
	~VariableInfo() {
		if (data_ptr() != nullptr) {
			// don't delete data directly for better abstraction
			// we might use the LSB of data in the future as LSB is
			// always aligned to kCapacityBase
			delete[] data_ptr();
		}
	}
	VariableInfo(VariableInfo &&rhs) {
		m_data = rhs.m_data;
		rhs.m_data = nullptr;
		m_misc = rhs.m_misc;
		m_size = rhs.m_size;
	}

	uint32_t emitValueChange(uint64_t current_time_index, const uint64_t val);
	uint32_t emitValueChange(
		uint64_t current_time_index, const uint32_t *val, EncodingType encoding
	);
	uint32_t emitValueChange(
		uint64_t current_time_index, const uint64_t *val, EncodingType encoding
	);

	void keepOnlyTheLatestValue() {
		const uint64_t last_written_bytes_ = last_written_bytes();
		uint8_t *data_ptr_ = data_ptr();
		std::copy_n(data_ptr_ + size() - last_written_bytes_, last_written_bytes_, data_ptr_);
		size(last_written_bytes_);
	}
	void dumpInitialBits(std::vector<uint8_t> &buf) const;
	void dumpValueChanges(std::vector<uint8_t> &buf) const;

	// We only need to make this class compatible with vector
	// delete copy constructor and assignment operator
	VariableInfo(const VariableInfo &) = delete;
	VariableInfo &operator=(const VariableInfo &) = delete;
	VariableInfo &operator=(VariableInfo &&) = delete;

	void resize(size_t new_size) {
		if (need_reallocate(new_size)) {
			reallocate(new_size);
		}
		size(new_size);
	}
	void add_size(size_t added_size) { resize(size() + added_size); }
	uint8_t *data_ptr() { return m_data; }
};
static_assert(
	sizeof(VariableInfo) != 12,
	"We don't support 32-bit architecture, comment out the assertions and take the risk"
);
static_assert(sizeof(VariableInfo) == 16, "VariableInfo should be small");

namespace detail {

constexpr size_t kEmitTimeIndexAndEncodingSize = sizeof(uint64_t) + sizeof(fst::EncodingType);

// EmitReaderHelper and EmitWriterHelper are very optimized for emit functions
// User must ensure the pointer points to the valid memory region
struct EmitReaderHelper {
	const uint8_t *ptr;
	EmitReaderHelper(const uint8_t *ptr_) : ptr(ptr_) {}

	std::pair<uint64_t, fst::EncodingType> readTimeIndexAndEncoding() {
		const auto time_index = read<uint64_t>();
		const auto encoding = read<fst::EncodingType>();
		return std::make_pair(time_index, encoding);
	}

	template <typename T>
	T read() {
		const size_t s = sizeof(T);
		T u;
		std::memcpy(&u, ptr, s);
		ptr += s;
		return u;
	}

	void skip(size_t count) { ptr += count; }

	template <typename T>
	T peek(size_t i = 0) {
		const size_t s = sizeof(T);
		T u;
		std::memcpy(&u, ptr + i * s, s);
		return u;
	}
};

struct EmitWriterHelper {
	uint8_t *ptr;

	EmitWriterHelper(uint8_t *ptr_) : ptr(ptr_) {}

	EmitWriterHelper &writeTimeIndexAndEncoding(uint64_t time_index, fst::EncodingType encoding) {
		write(time_index);
		write(encoding);
		return *this;
	}

	template <typename T>
	EmitWriterHelper &write(T u) {
		const size_t s = sizeof(u);
		std::memcpy(ptr, &u, s);
		ptr += s;
		return *this;
	}

	template <typename T>
	EmitWriterHelper &fill(T u, size_t count) {
		for (size_t i = 0; i < count; ++i) {
			std::memcpy(ptr, &u, sizeof(u));
			ptr += sizeof(u);
		}
		return *this;
	}

	template <typename T>
	EmitWriterHelper &write(T *u, size_t size) {
		for (size_t i = 0; i < size; ++i) {
			std::memcpy(ptr, u + i, sizeof(T));
			ptr += sizeof(T);
		}
		return *this;
	}
};

class VariableInfoDouble {
	VariableInfo &info;

public:
	VariableInfoDouble(VariableInfo &info_) : info(info_) {}

public:
	inline size_t computeBytesNeeded(EncodingType encoding) const {
		(void)encoding;
		return kEmitTimeIndexAndEncodingSize + sizeof(double);
	}

	inline EmitWriterHelper emitValueChangeCommonPart(
		uint64_t current_time_index, EncodingType encoding
	) {
		if (current_time_index + 1 == 0) {
			info.resize(0);
		}
		// For Double, value is always 8 bytes (sizeof(double) or uint64_t)
		const size_t added_size = computeBytesNeeded(encoding);
		const size_t old_size = info.size();
		info.add_size(added_size);

		EmitWriterHelper wh(info.data_ptr() + old_size);
		wh.writeTimeIndexAndEncoding(current_time_index, encoding);
		return wh;
	}

public:
	void construct() {
		const size_t needed = computeBytesNeeded(EncodingType::BINARY);
		info.resize(needed);
		EmitWriterHelper wh(info.data_ptr());
		const double nan_val = std::numeric_limits<double>::quiet_NaN();
		uint64_t nan_val_u64;
		std::memcpy(&nan_val_u64, &nan_val, sizeof(nan_val_u64));
		wh.writeTimeIndexAndEncoding(0, EncodingType::BINARY).write<uint64_t>(nan_val_u64);
	}

	void emitValueChange(uint64_t current_time_index, const uint64_t val) {
		auto wh = emitValueChangeCommonPart(current_time_index, EncodingType::BINARY);
		// Note, do not use write<double> here since the uint64_t is
		// already bit_cast'ed from double
		wh.write<uint64_t>(val);
	}

	// Double variables should not use these array-based emitValueChange overloads.
	// We implement them to satisfy the VairableInfo::dispatchHelper template instantiation.
	void emitValueChange(uint64_t, const uint32_t *, EncodingType) {
		throw std::runtime_error("emitValueChange(uint32_t*) not supported for Double");
	}
	void emitValueChange(uint64_t, const uint64_t *, EncodingType) {
		throw std::runtime_error("emitValueChange(uint64_t*) not supported for Double");
	}

	void dumpInitialBits(std::vector<uint8_t> &buf) const {
		FST_DCHECK_GT(info.size(), kEmitTimeIndexAndEncodingSize);
		EmitReaderHelper rh(info.data_ptr());
		StreamVectorWriteHelper wh(buf);
		(void)rh.readTimeIndexAndEncoding();
		auto v = rh.read<double>();
		wh.write<double>(v);
	}

	void dumpValueChanges(std::vector<uint8_t> &buf) const {
		StreamVectorWriteHelper wh(buf);
		EmitReaderHelper rh(info.data_ptr());
		const uint8_t *tail = info.data_ptr() + info.size();

		bool first = true;
		uint64_t prev_time_index = 0;

		while (true) {
			if (rh.ptr == tail) break;
			FST_CHECK_GT(tail, rh.ptr);
			const auto time_index = rh.read<uint64_t>();
			const auto enc = rh.read<EncodingType>();
			const auto num_byte = sizeof(double);
			if (first) {
				// Note: [0] is initial value, which is already dumped in dumpInitialBits()
				first = false;
			} else {
				FST_CHECK(enc == EncodingType::BINARY);
				const uint64_t delta_time_index = time_index - prev_time_index;
				prev_time_index = time_index;
				// Double shall be treated as non-binary
				const bool has_non_binary = true;
				wh  //
					.writeLEB128((delta_time_index << 1) | has_non_binary)
					.write<double>(rh.peek<double>());
			}
			rh.skip(num_byte);
		}
	}
};

template <typename T>
class VariableInfoScalarInt {
	VariableInfo &info;

public:
	VariableInfoScalarInt(VariableInfo &info_) : info(info_) {}

public:
	size_t computeBytesNeeded(EncodingType encoding) const {
		return kEmitTimeIndexAndEncodingSize + sizeof(T) * bitPerEncodedBit(encoding);
	}

	// The returning address points to the first byte of the value
	EmitWriterHelper emitValueChangeCommonPart(uint64_t current_time_index, EncodingType encoding) {
		if (current_time_index + 1 == 0) {
			// This is the first value change, we need to remove everything
			// and then add the new value
			info.resize(0);
		}
		const size_t added_size = computeBytesNeeded(encoding);
		const size_t old_size = info.size();
		info.add_size(added_size);
		EmitWriterHelper wh(info.data_ptr() + old_size);
		wh.writeTimeIndexAndEncoding(current_time_index, encoding);
		return wh;
	}

public:
	void construct() {
		info.resize(computeBytesNeeded(EncodingType::VERILOG));
		EmitWriterHelper wh(info.data_ptr());
		wh.writeTimeIndexAndEncoding(0, EncodingType::VERILOG).write(T(0)).write(T(-1));
	}

	void emitValueChange(uint64_t current_time_index, const uint64_t val) {
		auto wh = emitValueChangeCommonPart(current_time_index, EncodingType::BINARY);
		wh.template write<T>(val);
	}

	void emitValueChange(uint64_t current_time_index, const uint32_t *val, EncodingType encoding) {
		auto wh = emitValueChangeCommonPart(current_time_index, encoding);
		for (unsigned i = 0; i < bitPerEncodedBit(encoding); ++i) {
			// C++17: replace this with if constexpr
			if (sizeof(T) == 8) {
				uint64_t v = val[1];  // high bits
				v <<= 32;
				v |= val[0];  // low bits
				wh.template write<uint64_t>(v);
				val += 2;
			} else {
				wh.template write<T>(val[0]);
				val += 1;
			}
		}
	}

	void emitValueChange(uint64_t current_time_index, const uint64_t *val, EncodingType encoding) {
		auto wh = emitValueChangeCommonPart(current_time_index, encoding);
		for (unsigned i = 0; i < bitPerEncodedBit(encoding); ++i) {
			wh.template write<T>(val[i]);
		}
	}

	void dumpInitialBits(std::vector<uint8_t> &buf) const {
		// FST requires initial bits present
		FST_DCHECK_GT(info.size(), kEmitTimeIndexAndEncodingSize);
		EmitReaderHelper rh(info.data_ptr());
		const auto time_index_enc = rh.readTimeIndexAndEncoding();
		const auto enc = time_index_enc.second;
		const auto bitwidth = info.bitwidth();

		switch (enc) {
		case EncodingType::BINARY: {
			auto v0 = rh.read<T>();
			for (unsigned i = bitwidth; i-- > 0;) {
				const char c = ((v0 >> i) & T(1)) ? '1' : '0';
				buf.push_back(c);
			}
			break;
		}

		case EncodingType::VERILOG: {
			auto v0 = rh.read<T>();
			auto v1 = rh.read<T>();
			for (unsigned i = bitwidth; i-- > 0;) {
				const T b1 = ((v1 >> i) & T(1));
				const T b0 = ((v0 >> i) & T(1));
				const char c = kEncodedBitToCharTable[(b1 << 1) | b0];
				buf.push_back(c);
			}
			break;
		}
		// Not supporting VHDL now
		// LCOV_EXCL_START
		default:
		case EncodingType::VHDL: {
			auto v0 = rh.read<T>();
			auto v1 = rh.read<T>();
			auto v2 = rh.read<T>();
			for (unsigned i = bitwidth; i-- > 0;) {
				const T b2 = ((v2 >> i) & T(1));
				const T b1 = ((v1 >> i) & T(1));
				const T b0 = ((v0 >> i) & T(1));
				const char c = kEncodedBitToCharTable[(b2 << 2) | (b1 << 1) | b0];
				buf.push_back(c);
			}
			break;
		}
		}
		// LCOV_EXCL_STOP
	}

	void dumpValueChanges(std::vector<uint8_t> &buf) const {
		StreamVectorWriteHelper h(buf);
		EmitReaderHelper rh(info.data_ptr());
		const uint8_t *tail = info.data_ptr() + info.size();
		const auto bitwidth = info.bitwidth();
		bool first = true;
		uint64_t prev_time_index = 0;
		if (bitwidth == 1) {
			while (true) {
				if (rh.ptr == tail) {
					break;
				}
				FST_DCHECK_GT(tail, rh.ptr);
				const auto time_index = rh.read<uint64_t>();
				const auto enc = rh.read<EncodingType>();
				const auto num_element = bitPerEncodedBit(enc);
				const auto num_byte = num_element * sizeof(T);
				if (first) {
					// Note: [0] is initial value, which is already dumped in dumpInitialBits()
					first = false;
				} else {
					unsigned val = 0;
					for (unsigned i = 0; i < num_element; ++i) {
						val |= rh.peek<T>(i);
					}
					uint64_t delta_time_index = time_index - prev_time_index;
					prev_time_index = time_index;
					switch (val) {
						// clang-format off
					case 0: delta_time_index = (delta_time_index<<2) | (0<<1) | 0; break; // '0'
					case 1: delta_time_index = (delta_time_index<<2) | (1<<1) | 0; break; // '1'
					case 2: delta_time_index = (delta_time_index<<4) | (0<<1) | 1; break; // 'X'
					case 3: delta_time_index = (delta_time_index<<4) | (1<<1) | 1; break; // 'Z'
					// Not supporting VHDL now
					// LCOV_EXCL_START
					case 4: delta_time_index = (delta_time_index<<4) | (2<<1) | 1; break; // 'H'
					case 5: delta_time_index = (delta_time_index<<4) | (3<<1) | 1; break; // 'U'
					case 6: delta_time_index = (delta_time_index<<4) | (4<<1) | 1; break; // 'W'
					case 7: delta_time_index = (delta_time_index<<4) | (5<<1) | 1; break; // 'L'
					case 8: delta_time_index = (delta_time_index<<4) | (6<<1) | 1; break; // '-'
					case 9: delta_time_index = (delta_time_index<<4) | (7<<1) | 1; break; // '?'
					default: break;
					// LCOV_EXCL_STOP
						// clang-format on
					}
					h.writeLEB128(delta_time_index);
				}
				rh.skip(num_byte);
			}
		} else {
			while (true) {
				if (rh.ptr == tail) {
					break;
				}
				FST_CHECK_GT(tail, rh.ptr);
				const auto time_index = rh.read<uint64_t>();
				const auto enc = rh.read<EncodingType>();
				const auto num_element = bitPerEncodedBit(enc);
				const auto num_byte = num_element * sizeof(T);
				if (first) {
					first = false;
				} else {
					FST_CHECK(enc == EncodingType::BINARY);  // TODO
					const bool has_non_binary = enc != EncodingType::BINARY;
					const uint64_t delta_time_index = time_index - prev_time_index;
					prev_time_index = time_index;
					h  //
						.writeLEB128((delta_time_index << 1) | has_non_binary)
						.writeUIntPartialForValueChange(rh.peek<T>(), bitwidth);
				}
				rh.skip(num_byte);
			}
		}
	}
};

class VariableInfoLongInt {
	VariableInfo &info;
	unsigned num_words() const { return (info.bitwidth() + 63) / 64; }

public:
	VariableInfoLongInt(VariableInfo &info_) : info(info_) {}

public:
	size_t computeBytesNeeded(EncodingType encoding) const {
		return (
			kEmitTimeIndexAndEncodingSize +
			num_words() * sizeof(uint64_t) * bitPerEncodedBit(encoding)
		);
	}

	EmitWriterHelper emitValueChangeCommonPart(uint64_t current_time_index, EncodingType encoding) {
		if (current_time_index + 1 == 0) {
			info.resize(0);
		}
		const size_t added_size = computeBytesNeeded(encoding);
		const size_t old_size = info.size();
		info.add_size(added_size);

		EmitWriterHelper wh(info.data_ptr() + old_size);
		wh.writeTimeIndexAndEncoding(current_time_index, encoding);
		return wh;
	}

public:
	void construct() {
		const size_t nw = num_words();
		info.resize(computeBytesNeeded(EncodingType::VERILOG));
		EmitWriterHelper wh(info.data_ptr());
		wh  //
			.writeTimeIndexAndEncoding(0, EncodingType::VERILOG)
			.fill(uint64_t(0), nw)
			.fill(uint64_t(-1), nw);
	}

	void emitValueChange(uint64_t current_time_index, const uint64_t val) {
		const unsigned nw = num_words();
		auto wh = emitValueChangeCommonPart(current_time_index, EncodingType::BINARY);
		wh.write(val).fill(uint64_t(0), nw - 1);
	}

	void emitValueChange(uint64_t current_time_index, const uint32_t *val, EncodingType encoding) {
		const unsigned nw32 = (info.bitwidth() + 31) / 32;
		const unsigned bpb = bitPerEncodedBit(encoding);

		auto wh = emitValueChangeCommonPart(current_time_index, encoding);

		for (unsigned i = 0; i < bpb; ++i) {
			for (unsigned j = 0; j < nw32 / 2; ++j) {
				uint64_t v = val[1];  // high bits
				v <<= 32;
				v |= val[0];  // low bits
				wh.write(v);
				val += 2;
			}
			if (nw32 % 2 != 0) {
				uint64_t v = val[0];
				wh.write(v);
				val += 1;
			}
		}
	}

	void emitValueChange(uint64_t current_time_index, const uint64_t *val, EncodingType encoding) {
		const unsigned nw_encoded = num_words() * bitPerEncodedBit(encoding);
		auto wh = emitValueChangeCommonPart(current_time_index, encoding);
		wh.write(val, nw_encoded);
	}

	void dumpInitialBits(std::vector<uint8_t> &buf) const {
		FST_DCHECK_GT(info.size(), kEmitTimeIndexAndEncodingSize);
		EmitReaderHelper rh(info.data_ptr());
		const auto time_index_enc = rh.readTimeIndexAndEncoding();
		const auto enc = time_index_enc.second;
		const unsigned nw = num_words();
		switch (enc) {
		case EncodingType::BINARY: {
			for (unsigned word_index = nw; word_index-- > 0;) {
				const uint64_t v0 = rh.peek<uint64_t>(word_index);
				const unsigned num_bit =
					(word_index * 64 + 64 > info.bitwidth()) ? (info.bitwidth() % 64) : 64;
				for (unsigned bit_index = num_bit; bit_index-- > 0;) {
					const char c = ((v0 >> bit_index) & uint64_t(1)) ? '1' : '0';
					buf.push_back(c);
				}
			}
			break;
		}
		case EncodingType::VERILOG: {
			for (unsigned word_index = nw; word_index-- > 0;) {
				const uint64_t v0 = rh.peek<uint64_t>(nw * 0 + word_index);
				const uint64_t v1 = rh.peek<uint64_t>(nw * 1 + word_index);
				const unsigned num_bit =
					(word_index * 64 + 64 > info.bitwidth()) ? (info.bitwidth() % 64) : 64;
				for (unsigned bit_index = num_bit; bit_index-- > 0;) {
					const bool b0 = ((v0 >> bit_index) & uint64_t(1));
					const bool b1 = ((v1 >> bit_index) & uint64_t(1));
					const char c = kEncodedBitToCharTable[(b1 << 1) | b0];
					buf.push_back(c);
				}
			}
			break;
		}
		default:
		case EncodingType::VHDL: {
			// Not supporting VHDL now
			// LCOV_EXCL_START
			for (unsigned word_index = nw; word_index-- > 0;) {
				const uint64_t v0 = rh.peek<uint64_t>(nw * 0 + word_index);
				const uint64_t v1 = rh.peek<uint64_t>(nw * 1 + word_index);
				const uint64_t v2 = rh.peek<uint64_t>(nw * 2 + word_index);
				const unsigned num_bit =
					(word_index * 64 + 64 > info.bitwidth()) ? (info.bitwidth() % 64) : 64;
				for (unsigned bit_index = num_bit; bit_index-- > 0;) {
					const bool b0 = ((v0 >> bit_index) & uint64_t(1));
					const bool b1 = ((v1 >> bit_index) & uint64_t(1));
					const bool b2 = ((v2 >> bit_index) & uint64_t(1));
					const char c = kEncodedBitToCharTable[(b2 << 2) | (b1 << 1) | b0];
					buf.push_back(c);
				}
			}
			break;
			// LCOV_EXCL_STOP
		}
			rh.skip(sizeof(uint64_t) * nw * bitPerEncodedBit(enc));
		}
	}

	void dumpValueChanges(std::vector<uint8_t> &buf) const {
		StreamVectorWriteHelper h(buf);
		EmitReaderHelper rh(info.data_ptr());
		const uint8_t *tail = info.data_ptr() + info.size();
		const unsigned nw = num_words();
		const unsigned bitwidth = info.bitwidth();  // Local copy for lambda capture/usage if needed

		bool first = true;
		uint64_t prev_time_index = 0;

		while (true) {
			if (rh.ptr == tail) break;
			FST_DCHECK_GT(tail, rh.ptr);
			const auto time_index = rh.read<uint64_t>();
			const auto enc = rh.read<EncodingType>();
			const auto num_element = bitPerEncodedBit(enc);
			const auto num_byte = num_element * nw * sizeof(uint64_t);
			if (first) {
				// Note: [0] is initial value, which is already dumped in dumpInitialBits()
				first = false;
			} else {
				FST_CHECK(enc == EncodingType::BINARY);  // TODO
				const bool has_non_binary = enc != EncodingType::BINARY;
				const uint64_t delta_time_index = time_index - prev_time_index;
				prev_time_index = time_index;
				h.writeLEB128((delta_time_index << 1) | has_non_binary);
				if (bitwidth % 64 != 0) {
					const unsigned remaining = bitwidth % 64;
					uint64_t hi64 = rh.peek<uint64_t>(nw - 1);
					// write from nw-1 to 1
					for (unsigned j = nw - 1; j > 0; --j) {
						uint64_t lo64 = rh.peek<uint64_t>(j - 1);
						h.writeUIntBE((hi64 << (64 - remaining)) | (lo64 >> remaining));
						hi64 = lo64;
					}
					// write 0
					h.writeUIntPartialForValueChange(hi64, remaining);
				} else {
					// write from nw-1 to 0
					for (unsigned j = nw; j-- > 0;) {
						h.writeUIntBE(rh.peek<uint64_t>(j));
					}
				}
			}
			rh.skip(num_byte);
		}
	}
};

}  // namespace detail

template <typename Callable, typename... Args>
auto VariableInfo::dispatchHelper(Callable &&callable, Args &&...args) const {
	const uint32_t bitwidth = this->bitwidth();
	const bool is_real = this->is_real();
	if (!is_real) {
		// Decision: the branch miss is too expensive for large design, so we only use 3 types of
		// int
		if (bitwidth <= 8) {
			return callable(
				detail::VariableInfoScalarInt<uint8_t>(const_cast<VariableInfo &>(*this)),
				std::forward<Args>(args)...
			);
		} else if (bitwidth <= 64) {
			return callable(
				detail::VariableInfoScalarInt<uint64_t>(const_cast<VariableInfo &>(*this)),
				std::forward<Args>(args)...
			);
		} else {
			return callable(
				detail::VariableInfoLongInt(const_cast<VariableInfo &>(*this)),
				std::forward<Args>(args)...
			);
		}
	}
	return callable(
		detail::VariableInfoDouble(const_cast<VariableInfo &>(*this)), std::forward<Args>(args)...
	);
}

inline VariableInfo::VariableInfo(uint32_t bitwidth_, bool is_real_) {
	platform::write_field(m_misc, bitwidth_, kBitwidthWidth, kBitwidthOffset);
	platform::write_field(m_misc, is_real_, kIsRealWidth, kIsRealOffset);
	dispatchHelper([](auto obj) { obj.construct(); });
	last_written_encode_type(EncodingType::BINARY);
}

inline uint32_t VariableInfo::emitValueChange(uint64_t current_time_index, const uint64_t val) {
	const uint64_t old_size = size();
	dispatchHelper([=](auto obj) { obj.emitValueChange(current_time_index, val); });
	last_written_encode_type(EncodingType::BINARY);
	return static_cast<uint32_t>(size() - old_size);
}

inline uint32_t VariableInfo::emitValueChange(
	uint64_t current_time_index, const uint32_t *val, EncodingType encoding
) {
	const uint64_t old_size = size();
	dispatchHelper([=](auto obj) { obj.emitValueChange(current_time_index, val, encoding); });
	last_written_encode_type(encoding);
	return static_cast<uint32_t>(size() - old_size);
}

inline uint32_t VariableInfo::emitValueChange(
	uint64_t current_time_index, const uint64_t *val, EncodingType encoding
) {
	const uint64_t old_size = size();
	dispatchHelper([=](auto obj) { obj.emitValueChange(current_time_index, val, encoding); });
	last_written_encode_type(encoding);
	return static_cast<uint32_t>(size() - old_size);
}

inline void VariableInfo::dumpInitialBits(std::vector<uint8_t> &buf) const {
	dispatchHelper([&](auto obj) { obj.dumpInitialBits(buf); });
}

inline void VariableInfo::dumpValueChanges(std::vector<uint8_t> &buf) const {
	dispatchHelper([&](auto obj) { obj.dumpValueChanges(buf); });
}

inline uint64_t VariableInfo::last_written_bytes() const {
	const EncodingType encoding = last_written_encode_type();
	return dispatchHelper([encoding](auto obj) { return obj.computeBytesNeeded(encoding); });
}

}  // namespace fst
