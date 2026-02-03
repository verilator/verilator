// SPDX-FileCopyrightText: 2025-2026 Yu-Sheng Lin <johnjohnlys@gmail.com>
// SPDX-FileCopyrightText: 2025-2026 Yoda Lee <lc85301@gmail.com>
// SPDX-License-Identifier: MIT
#pragma once
// direct include
#include "fstcpp/fstcpp.h"
// C system headers
// C++ standard library headers
#include <algorithm>
#include <cstdint>
// #include <cstdlib>
// #include <string>
#include <vector>
// Other libraries' .h files.
// Your project's .h files.
#include "fstcpp/fstcpp_assertion.h"
#include "fstcpp/fstcpp_stream_write_helper.h"

namespace fst {

namespace platform {

// Can be replaced with std::bit_width when C++20 is available
inline uint64_t clog2(uint64_t x) {
	return 64 - __builtin_clzll(x - 1);
}

}  // namespace platform

class VariableInfo final {
	static constexpr uint64_t kCapacityBaseShift = 5;
	static constexpr uint64_t kCapacityBase = 1 << kCapacityBaseShift;

	// begin of data members
	// 1. 8B pointer, its size can be:
	//   - 0 if data is nullptr
	//   - `kCapacityBase * pow(2, capacity_log2)` if data is not nullptr
	//   - (TODO) Always aligned to kCapacityBase (will be changed to 64B)
	//     so we can use the LSB for capacity_log2
	uint8_t *data = nullptr;
	// 2. 8B misc:
	//   - 33b size (TODO: maybe 32b is enough, who needs a single variable
	//     larger than 4G in a block?)
	//   - 6b capacity_log2 (offset by -kCapacityBaseShift)
	//   - 12b last_written_bytes
	//     (TODO: can be calculated from only EncodingType, which is only 2b)
	//   - 12b bitwidth
	//   - 1b is_real
	uint64_t misc = 0;
	// end of data members

	inline bool need_reallocate(uint64_t new_size) const {
		const uint64_t capacity = data == nullptr ? 0 : (kCapacityBase << ((misc >> 25) & 0x3f));
		return capacity < new_size;
	}
	// This function is cold, so we don't inline it
	void reallocate(uint64_t new_size);

	inline void BuildMisc(uint32_t bitwidth_, bool is_real_) {
		misc = bitwidth_;
		misc <<= 1;
		misc |= is_real_;
	}

	inline void size(uint64_t size_) { misc = (misc << 33 >> 33) | size_ << 33; }

public:
	inline uint64_t size() const { return misc >> 33; }
	inline uint16_t bitwidth() const { return (misc >> 1) & 0xfff; }
	inline bool is_real() const { return misc & 1; }
	inline void last_written_bytes(uint64_t last_written_bytes_) {
		const uint64_t mask = ~(uint64_t(0xfff) << 13);
		misc = (misc & mask) | (last_written_bytes_ << 13);
	}
	inline uint64_t last_written_bytes() const { return (misc >> 13) & 0xfff; }

	template <typename Callable, typename... Args>
	auto DispatchHelper(Callable &&callable, Args &&...args) const;

	VariableInfo(uint16_t bitwidth_, bool is_real_ = false);
	~VariableInfo() {
		if (data_ptr() != nullptr) {
			// don't delete data directly for better abstraction
			// we might use the LSB of data in the future as LSB is
			// always aligned to kCapacityBase
			delete[] data_ptr();
		}
	}
	VariableInfo(VariableInfo &&rhs) {
		data = rhs.data;
		rhs.data = nullptr;
		misc = rhs.misc;
		// rhs.misc = 0;
	}

	uint32_t emitValueChange(uint64_t current_time_index, const uint64_t val);
	uint32_t emitValueChange(
		uint64_t current_time_index, const uint32_t *val, EncodingType encoding
	);
	uint32_t emitValueChange(
		uint64_t current_time_index, const uint64_t *val, EncodingType encoding
	);

	void KeepOnlyTheLatestValue() {
		const auto last_written_bytes_ = last_written_bytes();
		const auto data_ptr_ = data_ptr();
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
	uint8_t *data_ptr() { return data; }
};
static_assert(sizeof(VariableInfo) == 16, "VariableInfoBase should be small");

namespace detail {

constexpr size_t kEmitTimeIndexAndEncodingSize = sizeof(uint64_t) + sizeof(fst::EncodingType);

// EmitReaderHelper and EmitWriterHelper are very optimized for emit functions
// User must ensure the pointer points to the valid memory region
struct EmitReaderHelper {
	const uint8_t *ptr;
	EmitReaderHelper(const uint8_t *ptr_) : ptr(ptr_) {}

	std::pair<uint64_t, fst::EncodingType> ReadTimeIndexAndEncoding() {
		const auto time_index = Read<uint64_t>();
		const auto encoding = Read<fst::EncodingType>();
		return std::make_pair(time_index, encoding);
	}

	template <typename T>
	T Read() {
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

private:
	inline size_t addedSize(EncodingType encoding) const {
		(void)encoding;
		return kEmitTimeIndexAndEncodingSize + sizeof(double);
	}

	// first: its pointer to the first byte of the value
	// second: size of the time index+encoding type+value
	inline std::pair<EmitWriterHelper, size_t> emitValueChangeCommonPart(
		uint64_t current_time_index, EncodingType encoding
	) {
		if (current_time_index + 1 == 0) {
			info.resize(0);
		}
		// For Double, value is always 8 bytes (sizeof(double) or uint64_t)
		const size_t added_size = addedSize(encoding);
		const size_t old_size = info.size();
		info.add_size(added_size);

		EmitWriterHelper wh(info.data_ptr() + old_size);
		wh.writeTimeIndexAndEncoding(current_time_index, encoding);
		return std::make_pair(wh, added_size);
	}

public:
	void construct() {
		const size_t needed = addedSize(EncodingType::BINARY);
		info.resize(needed);
		EmitWriterHelper wh(info.data_ptr());
		wh.writeTimeIndexAndEncoding(0, EncodingType::BINARY).write<double>(0.0);
	}

	uint64_t emitValueChange(uint64_t current_time_index, const uint64_t val) {
		auto wh_added = emitValueChangeCommonPart(current_time_index, EncodingType::BINARY);
		auto wh = wh_added.first;
		auto added_size = wh_added.second;
		// Note, do not use write<double> here since the uint64_t is
		// already bit_cast'ed from double
		wh.write<uint64_t>(val);
		return added_size;
	}

	// Double variables should not use these array-based emitValueChange overloads.
	// We implement them to satisfy the VairableInfo::DispatchHelper template instantiation.
	uint64_t emitValueChange(uint64_t, const uint32_t *, EncodingType) {
		throw std::runtime_error("emitValueChange(uint32_t*) not supported for Double");
	}
	uint64_t emitValueChange(uint64_t, const uint64_t *, EncodingType) {
		throw std::runtime_error("emitValueChange(uint64_t*) not supported for Double");
	}

	void dumpInitialBits(std::vector<uint8_t> &buf) const {
		FST_DCHECK_GT(info.size(), kEmitTimeIndexAndEncodingSize);
		EmitReaderHelper rh(info.data_ptr());
		StreamVectorWriteHelper wh(buf);
		(void)rh.ReadTimeIndexAndEncoding();
		auto v = rh.Read<double>();
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
			const auto time_index = rh.Read<uint64_t>();
			const auto enc = rh.Read<EncodingType>();
			const auto num_byte = sizeof(double);
			if (first) {
				// Note: [0] is initial value, which is already dumped in dumpInitialBits()
				first = false;
			} else {
				FST_CHECK(enc == EncodingType::BINARY);
				const uint64_t delta_time_index = time_index - prev_time_index;
				prev_time_index = time_index;
				wh.writeLEB128(delta_time_index).write<double>(rh.peek<double>());
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

private:
	inline size_t addedSize(EncodingType encoding) const {
		return kEmitTimeIndexAndEncodingSize + sizeof(T) * BitPerEncodedBit(encoding);
	}

	// The returning address points to the first byte of the value
	// .first: its pointer to the first byte of the value
	// .second: size of the time index+encoding type+value
	inline std::pair<EmitWriterHelper, size_t> emitValueChangeCommonPart(
		uint64_t current_time_index, EncodingType encoding
	) {
		if (current_time_index + 1 == 0) {
			// This is the first value change, we need to remove everything
			// and then add the new value
			info.resize(0);
		}
		const size_t added_size = addedSize(encoding);
		const size_t old_size = info.size();
		info.add_size(added_size);
		EmitWriterHelper wh(info.data_ptr() + old_size);
		wh.writeTimeIndexAndEncoding(current_time_index, encoding);
		return std::make_pair(wh, added_size);
	}

public:
	void construct() {
		info.resize(addedSize(EncodingType::VERILOG));
		EmitWriterHelper wh(info.data_ptr());
		wh.writeTimeIndexAndEncoding(0, EncodingType::VERILOG).write(T(0)).write(T(-1));
	}

	uint64_t emitValueChange(uint64_t current_time_index, const uint64_t val) {
		auto wh_added = emitValueChangeCommonPart(current_time_index, EncodingType::BINARY);
		auto wh = wh_added.first;
		auto added_size = wh_added.second;
		wh.template write<T>(val);
		return added_size;
	}

	uint64_t emitValueChange(
		uint64_t current_time_index, const uint32_t *val, EncodingType encoding
	) {
		auto wh_added = emitValueChangeCommonPart(current_time_index, encoding);
		auto wh = wh_added.first;
		auto added_size = wh_added.second;
		for (unsigned i = 0; i < BitPerEncodedBit(encoding); ++i) {
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
		return added_size;
	}

	uint64_t emitValueChange(
		uint64_t current_time_index, const uint64_t *val, EncodingType encoding
	) {
		auto wh_added = emitValueChangeCommonPart(current_time_index, encoding);
		auto wh = wh_added.first;
		auto added_size = wh_added.second;
		for (unsigned i = 0; i < BitPerEncodedBit(encoding); ++i) {
			wh.template write<T>(val[i]);
		}
		return added_size;
	}

	void dumpInitialBits(std::vector<uint8_t> &buf) const {
		// FST requires initial bits present
		FST_DCHECK_GT(info.size(), kEmitTimeIndexAndEncodingSize);
		EmitReaderHelper rh(info.data_ptr());
		const auto time_index_enc = rh.ReadTimeIndexAndEncoding();
		const auto enc = time_index_enc.second;
		const auto bitwidth = info.bitwidth();

		switch (enc) {
		case EncodingType::BINARY: {
			auto v0 = rh.Read<T>();
			for (unsigned i = bitwidth; i-- > 0;) {
				const char c = ((v0 >> i) & T(1)) ? '1' : '0';
				buf.push_back(c);
			}
			break;
		}

		case EncodingType::VERILOG: {
			auto v0 = rh.Read<T>();
			auto v1 = rh.Read<T>();
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
			auto v0 = rh.Read<T>();
			auto v1 = rh.Read<T>();
			auto v2 = rh.Read<T>();
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
				const auto time_index = rh.Read<uint64_t>();
				const auto enc = rh.Read<EncodingType>();
				const auto num_element = BitPerEncodedBit(enc);
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
				const auto time_index = rh.Read<uint64_t>();
				const auto enc = rh.Read<EncodingType>();
				const auto num_element = BitPerEncodedBit(enc);
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

private:
	inline size_t addedSize(EncodingType encoding) const {
		return (
			kEmitTimeIndexAndEncodingSize +
			num_words() * sizeof(uint64_t) * BitPerEncodedBit(encoding)
		);
	}

	inline std::pair<EmitWriterHelper, size_t> emitValueChangeCommonPart(
		uint64_t current_time_index, EncodingType encoding
	) {
		if (current_time_index + 1 == 0) {
			info.resize(0);
		}
		const size_t added_size = addedSize(encoding);
		const size_t old_size = info.size();
		info.add_size(added_size);

		EmitWriterHelper wh(info.data_ptr() + old_size);
		wh.writeTimeIndexAndEncoding(current_time_index, encoding);
		return std::make_pair(wh, added_size);
	}

public:
	void construct() {
		const size_t nw = num_words();
		info.resize(addedSize(EncodingType::VERILOG));
		EmitWriterHelper wh(info.data_ptr());
		wh  //
			.writeTimeIndexAndEncoding(0, EncodingType::VERILOG)
			.fill(uint64_t(0), nw)
			.fill(uint64_t(-1), nw);
	}

	uint64_t emitValueChange(uint64_t current_time_index, const uint64_t val) {
		const unsigned nw = num_words();
		auto wh_added = emitValueChangeCommonPart(current_time_index, EncodingType::BINARY);
		auto wh = wh_added.first;
		auto added_size = wh_added.second;
		wh.write(val).fill(uint64_t(0), nw - 1);
		return added_size;
	}

	uint64_t emitValueChange(
		uint64_t current_time_index, const uint32_t *val, EncodingType encoding
	) {
		const unsigned nw32 = (info.bitwidth() + 31) / 32;
		const unsigned bpb = BitPerEncodedBit(encoding);

		auto wh_added = emitValueChangeCommonPart(current_time_index, encoding);
		auto wh = wh_added.first;
		auto added_size = wh_added.second;

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
		return added_size;
	}

	uint64_t emitValueChange(
		uint64_t current_time_index, const uint64_t *val, EncodingType encoding
	) {
		const unsigned nw_encoded = num_words() * BitPerEncodedBit(encoding);
		auto wh_added = emitValueChangeCommonPart(current_time_index, encoding);
		auto wh = wh_added.first;
		wh.write(val, nw_encoded);
		return wh_added.second;
	}

	void dumpInitialBits(std::vector<uint8_t> &buf) const {
		FST_DCHECK_GT(info.size(), kEmitTimeIndexAndEncodingSize);
		EmitReaderHelper rh(info.data_ptr());
		const auto time_index_enc = rh.ReadTimeIndexAndEncoding();
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
			rh.skip(sizeof(uint64_t) * nw * BitPerEncodedBit(enc));
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
			const auto time_index = rh.Read<uint64_t>();
			const auto enc = rh.Read<EncodingType>();
			const auto num_element = BitPerEncodedBit(enc);
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
auto VariableInfo::DispatchHelper(Callable &&callable, Args &&...args) const {
	const auto bitwidth = this->bitwidth();
	const auto is_real = this->is_real();
	if (not is_real) {
		// Decision: the branch miss is too expensive for large design, so we only use 3 types of
		// int
		if (bitwidth <= 8) {
			return callable(
				detail::VariableInfoScalarInt<uint8_t>(const_cast<VariableInfo &>(*this)),
				std::forward<Args>(args)...
			);
			// } else if (bitwidth <= 16) {
			// 	return
			// callable(detail::VariableInfoScalarInt<uint16_t>(const_cast<VariableInfo&>(*this)),
			// std::forward<Args>(args)...); } else if (bitwidth <= 32) { 	return
			// callable(detail::VariableInfoScalarInt<uint32_t>(const_cast<VariableInfo&>(*this)),
			// std::forward<Args>(args)...);
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

inline VariableInfo::VariableInfo(uint16_t bitwidth_, bool is_real_) {
	BuildMisc(bitwidth_, is_real_);
	DispatchHelper([this](auto obj) {
		obj.construct();
		last_written_bytes(size());
	});
}

inline uint32_t VariableInfo::emitValueChange(uint64_t current_time_index, const uint64_t val) {
	const auto last_written_bytes_ =
		DispatchHelper([=](auto obj) { return obj.emitValueChange(current_time_index, val); });
	last_written_bytes(last_written_bytes_);
	return last_written_bytes_;
}

inline uint32_t VariableInfo::emitValueChange(
	uint64_t current_time_index, const uint32_t *val, EncodingType encoding
) {
	const auto last_written_bytes_ = DispatchHelper([=](auto obj) {
		return obj.emitValueChange(current_time_index, val, encoding);
	});
	last_written_bytes(last_written_bytes_);
	return last_written_bytes_;
}

inline uint32_t VariableInfo::emitValueChange(
	uint64_t current_time_index, const uint64_t *val, EncodingType encoding
) {
	const auto last_written_bytes_ = DispatchHelper([=](auto obj) {
		return obj.emitValueChange(current_time_index, val, encoding);
	});
	last_written_bytes(last_written_bytes_);
	return last_written_bytes_;
}

inline void VariableInfo::dumpInitialBits(std::vector<uint8_t> &buf) const {
	DispatchHelper([&](auto obj) { obj.dumpInitialBits(buf); });
}

inline void VariableInfo::dumpValueChanges(std::vector<uint8_t> &buf) const {
	DispatchHelper([&](auto obj) { obj.dumpValueChanges(buf); });
}

}  // namespace fst
