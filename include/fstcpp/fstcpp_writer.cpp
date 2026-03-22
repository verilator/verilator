// SPDX-FileCopyrightText: 2025-2026 Yu-Sheng Lin <johnjohnlys@gmail.com>
// SPDX-FileCopyrightText: 2025-2026 Yoda Lee <lc85301@gmail.com>
// SPDX-License-Identifier: MIT
// Project: libfstwriter
// Website: https://github.com/gtkwave/libfstwriter
// direct include
#include "fstcpp/fstcpp_writer.h"
// C system headers
// C++ standard library headers
#include <cstdio>
#include <cstring>
#include <numeric>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>
// Other libraries' .h files.
#include <lz4.h>
#include <zlib.h>
// Your project's .h files.
#include "fstcpp/fstcpp.h"
#include "fstcpp/fstcpp_assertion.h"
#include "fstcpp/fstcpp_stream_write_helper.h"
#include "fstcpp/fstcpp_variable_info.h"

// AT(vec, x) is used to access vector at index x, and it will throw exception if out of bound
// in debug mode, but in release mode, it will not throw exception
// Usually you should only need AT(vec, x) only at very hot code path.
#ifndef NDEBUG
#	define AT(vec, x) (vec.at(x))
#else
#	define AT(vec, x) (vec[x])
#endif

namespace fst {

namespace detail {

void BlackoutData::emitDumpActive(uint64_t current_timestamp, bool enable) {
	StreamVectorWriteHelper h(m_buffer);
	h.writeUIntBE<uint8_t>(enable).writeLEB128(current_timestamp - m_previous_timestamp);
	++m_count;
}

ValueChangeData::ValueChangeData() {
	m_variable_infos.reserve(1024);
}

ValueChangeData::~ValueChangeData() = default;

void ValueChangeData::keepOnlyTheLatestValue() {
	for (VariableInfo &v : m_variable_infos) {
		v.keepOnlyTheLatestValue();
	}
	FST_CHECK(!m_timestamps.empty());
	m_timestamps.front() = m_timestamps.back();
	m_timestamps.resize(1);
}

}  // namespace detail

void Writer::open(const string_view_pair name) {
	FST_CHECK(!m_main_fst_file_.is_open());
	m_main_fst_file_.open(std::string(name.m_data, name.m_size), std::ios::binary);
	// reserve space for header, we will write it at Close(), append geometry and hierarchy at the
	// end wave data will be flushed in between
	m_main_fst_file_.seekp(kSharedBlockHeaderSize + HeaderInfo::total_size, std::ios_base::beg);
}

void Writer::close() {
	if (!m_main_fst_file_.is_open()) return;
	// Finalize header fields
	if (m_header_.m_date[0] == '\0') {
		// date is not set yet, set to the current date
		setDate();
	}
	if (m_header_.m_start_time == kInvalidTime) {
		m_header_.m_start_time = 0;
	}
	flushValueChangeData_(m_value_change_data_, m_main_fst_file_);
	appendGeometry_(m_main_fst_file_);
	appendHierarchy_(m_main_fst_file_);
	appendBlackout_(m_main_fst_file_);
	// Note: write header seek to 0, so we need to do
	// this after all append operations
	writeHeader_(m_header_, m_main_fst_file_);
	m_main_fst_file_.close();
}

/////////////////////////////////////////
// Hierarchy / variable API
/////////////////////////////////////////
void Writer::setScope(
	Hierarchy::ScopeType scopetype,
	const string_view_pair scopename,
	const string_view_pair scopecomp
) {
	FST_CHECK(!m_hierarchy_finalized_);
	StreamVectorWriteHelper h(m_hierarchy_buffer_);
	h  //
		.writeU8Enum(Hierarchy::ScopeControlType::VCD_SCOPE)
		.writeU8Enum(scopetype)
		.writeString0(scopename)
		.writeString0(scopecomp);
	++m_header_.m_num_scopes;
}

void Writer::upscope() {
	FST_CHECK(!m_hierarchy_finalized_);
	// TODO: shall we inline it?
	StreamVectorWriteHelper h(m_hierarchy_buffer_);
	h.writeU8Enum(Hierarchy::ScopeControlType::VCD_UPSCOPE);
}

Handle Writer::createVar(
	Hierarchy::VarType vartype,
	Hierarchy::VarDirection vardir,
	uint32_t bitwidth,
	const string_view_pair name,
	Handle alias_handle
) {
	FST_CHECK(!m_hierarchy_finalized_);
	FST_CHECK_LE(bitwidth, VariableInfo::kMaxSupportedBitwidth);
	// write hierarchy entry: type, direction, name, length, alias
	StreamVectorWriteHelper h(m_hierarchy_buffer_);

	// determine real/string handling like original C implementation
	bool is_real{false};
	switch (vartype) {
	case Hierarchy::VarType::VCD_REAL:
	case Hierarchy::VarType::VCD_REAL_PARAMETER:
	case Hierarchy::VarType::VCD_REALTIME:
	case Hierarchy::VarType::SV_SHORTREAL:
		is_real = true;
		bitwidth = 8;  // recast to double size
		break;
	case Hierarchy::VarType::GEN_STRING:
		bitwidth = 0;
		break;
	default:
		break;
	}
	if (alias_handle > m_header_.m_num_handles) {
		// sanitize
		alias_handle = 0;
	}
	const bool is_alias{alias_handle != 0};
	// This counter is incremented whether alias || non-alias
	++m_header_.m_num_vars;
	if (!is_alias) {
		// This counter is incremented only for non-alias variables
		++m_header_.m_num_handles;
		alias_handle = static_cast<uint32_t>(m_header_.m_num_handles);
	}

	h  //
		.writeU8Enum(vartype)
		.writeU8Enum(vardir)
		.writeString0(name)
		.writeLEB128(bitwidth)
		.writeLEB128(is_alias ? alias_handle : 0);

	// If alias_handle == 0, we must allocate geom/valpos/curval entries and create a new handle
	if (!is_alias) {
		StreamVectorWriteHelper g(m_geometry_buffer_);
		// I don't know why the original C implementation encode bitwidth again
		const uint32_t geom_len{(bitwidth == 0 ? uint32_t(-1) : is_real ? uint32_t(0) : bitwidth)};
		g.writeLEB128(geom_len);
		m_value_change_data_.m_variable_infos.emplace_back(bitwidth, is_real);
	}

	return alias_handle;
}

// TODO
// LCOV_EXCL_START
// Handle Writer::createVar2(
// 	Hierarchy::VarType vartype,
// 	Hierarchy::VarDirection vardir,
// 	uint32_t bitwidth,
// 	const string_view_pair name,
// 	Handle alias_handle,
// 	const string_view_pair type,
// 	Hierarchy::SupplementalVarType svt,
// 	Hierarchy::SupplementalDataType sdt
// ) {
// 	FST_CHECK(!m_hierarchy_finalized_);
// 	(void)vartype;
// 	(void)vardir;
// 	(void)bitwidth;
// 	(void)name;
// 	(void)alias_handle;
// 	(void)type;
// 	(void)svt;
// 	(void)sdt;
// 	throw std::runtime_error("TODO");
// 	return 0;
// }
// LCOV_EXCL_STOP

/////////////////////////////////////////
// Waveform API
/////////////////////////////////////////
void Writer::emitTimeChange(uint64_t tim) {
	finalizeHierarchy_();

	if (m_value_change_data_usage_ > m_value_change_data_flush_threshold_ || m_flush_pending_) {
		flushValueChangeData_(m_value_change_data_, m_main_fst_file_);
	}

	// Update header
	m_header_.m_start_time = std::min(m_header_.m_start_time, tim);
	m_header_.m_end_time = tim;

	if (m_value_change_data_.m_timestamps.empty() ||
		m_value_change_data_.m_timestamps.back() != tim) {
		m_value_change_data_.m_timestamps.push_back(tim);
	}
}

// TODO
// void Writer::emitDumpActive(bool enable) {
// 	// TODO: this API is not fully understood, need to check
// 	FST_CHECK(!m_value_change_data_.m_timestamps.empty());
// 	m_blackout_data_.emitDumpActive(m_value_change_data_.m_timestamps.back(), enable);
// }

template <typename... T>
void Writer::emitValueChangeHelper_(Handle handle, T &&...val) {
	// Let data prefetch go first
	VariableInfo &var_info = AT(m_value_change_data_.m_variable_infos, handle - 1);
#if defined(__GNUC__) || defined(__clang__)
	__builtin_prefetch(var_info.data_ptr() + var_info.size() - 1, 1, 0);
#endif

	finalizeHierarchy_();

	// Original implementation: virtual, but vtable is too costly, we switch to if-else static
	// dispatch
	m_value_change_data_usage_ += var_info.emitValueChange(
		m_value_change_data_.m_timestamps.size() - 1, std::forward<T>(val)...
	);
}

void Writer::emitValueChange(Handle handle, const uint32_t *val, EncodingType encoding) {
	emitValueChangeHelper_(handle, val, encoding);
}

void Writer::emitValueChange(Handle handle, const uint64_t *val, EncodingType encoding) {
	emitValueChangeHelper_(handle, val, encoding);
}

void Writer::emitValueChange(Handle handle, uint64_t val) {
	emitValueChangeHelper_(handle, val);
}

void Writer::emitValueChange(Handle handle, const char *val) {
	finalizeHierarchy_();
	VariableInfo &var_info = AT(m_value_change_data_.m_variable_infos, handle - 1);

	// For double handles, const char* is interpreted as a double* (8B)
	// This double shall be written out as raw IEEE 754 double
	// So we just reinterpret_cast it to uint64_t and emit it
	if (var_info.is_real()) {
		emitValueChange(handle, *reinterpret_cast<const uint64_t *>(val));
		return;
	}

	// For normal integer handles, const char* is "01xz..." (1B per bit)
	const uint32_t bitwidth{var_info.bitwidth()};
	FST_DCHECK_NE(bitwidth, 0);

	val += bitwidth;
	const unsigned num_words{(bitwidth + 63) / 64};
	m_packed_value_buffer_.assign(num_words, 0);
	for (unsigned i = 0; i < num_words; ++i) {
		const char *start{val - std::min((i + 1) * 64, bitwidth)};
		const char *end{val - 64 * i};
		m_packed_value_buffer_[i] = 0;
		for (const char *p = start; p < end; ++p) {
			// No checking for invalid characters, follow original C implementation
			m_packed_value_buffer_[i] <<= 1;
			m_packed_value_buffer_[i] |= static_cast<uint64_t>(*p - '0');
		}
	}

	if (bitwidth <= 64) {
		emitValueChange(handle, m_packed_value_buffer_.front());
	} else {
		emitValueChange(handle, m_packed_value_buffer_.data(), EncodingType::BINARY);
	}
}

/////////////////////////////////////////
// File flushing functions
/////////////////////////////////////////
void Writer::writeHeader_(const Header &header, std::ostream &os) {
	StreamWriteHelper h(os);
	static char kDefaultWriterName[sizeof(header.m_writer)] = "fstcppWriter";
	const char *writer_name = header.m_writer[0] == '\0' ? kDefaultWriterName : header.m_writer;

	// Actual write
	h  //
		.seek(std::streamoff(0), std::ios_base::beg)
		.writeBlockHeader(BlockType::HEADER, HeaderInfo::total_size)
		.writeUInt(header.m_start_time)
		.writeUInt(header.m_end_time)
		.writeFloat(HeaderInfo::kEndianessMagicIdentifier)
		.writeUInt(header.m_writer_memory_use)
		.writeUInt(header.m_num_scopes)
		.writeUInt(header.m_num_vars)
		.writeUInt(header.m_num_handles)
		.writeUInt(header.m_num_value_change_data_blocks)
		.writeUInt(header.m_timescale)
		.write(writer_name, sizeof(header.m_writer))
		.write(header.m_date, sizeof(header.m_date))
		.fill('\0', HeaderInfo::Size::reserved)
		.writeUInt(static_cast<uint8_t>(header.m_filetype))
		.writeUInt(header.m_timezero);

	FST_DCHECK_EQ(os.tellp(), HeaderInfo::total_size + kSharedBlockHeaderSize);
}

namespace {  // compression helpers

// These API pass compressed_data to avoid frequent reallocations
void compressUsingLz4(
	const std::vector<uint8_t> &uncompressed_data, std::vector<uint8_t> &compressed_data
) {
	const int uncompressed_size = uncompressed_data.size();
	const int compressed_bound = LZ4_compressBound(uncompressed_size);
	compressed_data.resize(compressed_bound);
	const int compressed_size = LZ4_compress_default(
		reinterpret_cast<const char *>(uncompressed_data.data()),
		reinterpret_cast<char *>(compressed_data.data()),
		uncompressed_size,
		compressed_bound
	);
	compressed_data.resize(compressed_size);
}

void compressUsingZlib(
	const std::vector<uint8_t> &uncompressed_data, std::vector<uint8_t> &compressed_data, int level
) {
	// compress using zlib
	const uLong uncompressed_size = uncompressed_data.size();
	uLongf compressed_bound = compressBound(uncompressed_size);
	compressed_data.resize(compressed_bound);
	const auto z_status = compress2(
		reinterpret_cast<Bytef *>(compressed_data.data()),
		&compressed_bound,
		reinterpret_cast<const Bytef *>(uncompressed_data.data()),
		uncompressed_size,
		level
	);
	if (z_status != Z_OK) {
		throw std::runtime_error(
			"Failed to compress data with zlib, error code: " + std::to_string(z_status)
		);
	}
	compressed_data.resize(compressed_bound);
}

std::pair<const uint8_t *, size_t> selectSmaller(
	const std::vector<uint8_t> &compressed_data, const std::vector<uint8_t> &uncompressed_data
) {
	std::pair<const uint8_t *, size_t> ret;
	if (compressed_data.size() < uncompressed_data.size()) {
		ret.first = compressed_data.data();
		ret.second = compressed_data.size();
	} else {
		ret.first = uncompressed_data.data();
		ret.second = uncompressed_data.size();
	}
	return ret;
}

}  // namespace

// AppendHierarchy_ and AppendGeometry_ shares a very similar structure
// But they are slightly different in the original C implementation...
void Writer::appendGeometry_(std::ostream &os) {
	if (m_geometry_buffer_.empty()) {
		// skip the geometry block if there is no data
		return;
	}
	std::vector<uint8_t> geometry_buffer_compressed_{};
	compressUsingZlib(m_geometry_buffer_, geometry_buffer_compressed_, 9);
	// TODO: Replace with structured binding in C++17
	const std::pair<const uint8_t *, size_t> selected_pair =
		selectSmaller(geometry_buffer_compressed_, m_geometry_buffer_);
	const uint8_t *selected_data = selected_pair.first;
	const size_t selected_size = selected_pair.second;

	StreamWriteHelper h(os);
	h  //
		.seek(0, std::ios_base::end)
		// 16 is for the uncompressed_size and header_.num_handles
		.writeBlockHeader(BlockType::GEOMETRY, selected_size + 16)
		.writeUInt<uint64_t>(m_geometry_buffer_.size())
		// I don't know why the original C implementation write num_handles again here
		// but we have to follow it
		.writeUInt(m_header_.m_num_handles)
		.write(selected_data, selected_size);
}

void Writer::appendHierarchy_(std::ostream &os) {
	if (m_hierarchy_buffer_.empty()) {
		// skip the hierarchy block if there is no data
		return;
	}

	// compress hierarchy_buffer_ using LZ4.
	const int compressed_bound{LZ4_compressBound(m_hierarchy_buffer_.size())};
	std::vector<uint8_t> hierarchy_buffer_compressed_(compressed_bound);
	const int compressed_size{LZ4_compress_default(
		reinterpret_cast<const char *>(m_hierarchy_buffer_.data()),
		reinterpret_cast<char *>(hierarchy_buffer_compressed_.data()),
		m_hierarchy_buffer_.size(),
		compressed_bound
	)};

	StreamWriteHelper h(os);
	h  //
		.seek(0, std::ios_base::end)
		// +16 is for the uncompressed_size
		.writeBlockHeader(BlockType::HIERARCHY_LZ4_COMPRESSED, compressed_size + 8)
		.writeUInt<uint64_t>(m_hierarchy_buffer_.size())
		.write(hierarchy_buffer_compressed_.data(), compressed_size);
}

void Writer::appendBlackout_(std::ostream &os) {
	if (m_blackout_data_.m_count == 0) {
		// skip the blackout block if there is no data
		return;
	}
	const std::vector<uint8_t> &blackout_data = m_blackout_data_.m_buffer;
	const std::streampos begin_of_blackout_block = os.tellp();
	StreamWriteHelper h(os);
	h  //
	   // skip the block header
		.seek(kSharedBlockHeaderSize, std::ios_base::cur)
		// Note: we cannot know the size beforehand since this length is LEB128 encoded
		.writeLEB128(blackout_data.size())
		.write(blackout_data.data(), blackout_data.size());

	const std::streamoff size_of_blackout_block = os.tellp() - begin_of_blackout_block;
	h  //
	   // go back to the beginning of the block
		.seek(begin_of_blackout_block, std::ios_base::beg)
		// and write the block header
		.writeBlockHeader(
			BlockType::BLACKOUT,
			static_cast<uint64_t>(size_of_blackout_block - kSharedBlockHeaderSize)
		);
}

void detail::ValueChangeData::writeInitialBits(std::vector<uint8_t> &os) const {
	// Build vc_bits_data by concatenating each variable's initial bits as documented.
	// We will not compress for now; just generate the raw bytes and print summary to stdout.
	for (size_t i{0}; i < m_variable_infos.size(); ++i) {
		const VariableInfo &vref = m_variable_infos[i];
		vref.dumpInitialBits(os);
	}
}

std::vector<std::vector<uint8_t>> detail::ValueChangeData::computeWaveData() const {
	const size_t N{m_variable_infos.size()};
	std::vector<std::vector<uint8_t>> data(N);
	for (size_t i{0}; i < N; ++i) {
		m_variable_infos[i].dumpValueChanges(data[i]);
	}
	return data;
}

std::vector<int64_t> detail::ValueChangeData::uniquifyWaveData(
	std::vector<std::vector<uint8_t>> &data
) {
	// After this function, positions[i] is:
	//  - = 0: If data[i] is unique (first occurrence)
	//  - < 0: If data[i] is a duplicate, encoded as -(original_index + 1)
	std::vector<int64_t> positions(data.size(), 0);
	struct MyHash {
		size_t operator()(const std::vector<uint8_t> *vec) const {
			size_t seed = 0;
			for (auto v : *vec) {
				seed ^= v + 0x9e3779b9 + (seed << 6) + (seed >> 2);
			}
			return seed;
		}
	};
	struct MyEqual {
		bool operator()(const std::vector<uint8_t> *a, const std::vector<uint8_t> *b) const {
			return *a == *b;
		}
	};
	std::unordered_map<const std::vector<uint8_t> *, int64_t, MyHash, MyEqual> data_map;
	for (size_t i = 0; i < data.size(); ++i) {
		if (data[i].empty()) {
			continue;
		}
		// insert vec->i to data_map if not exists
		auto p = data_map.emplace(&data[i], static_cast<int64_t>(i));
		auto it = p.first;
		const bool inserted{p.second};

		if (!inserted) {
			// duplicated wave data found
			positions[i] = -(it->second + 1);
			// clear data to save memory
			data[i].clear();
		}
	}
	return positions;
}

uint64_t detail::ValueChangeData::encodePositionsAndwriteUniqueWaveData(
	std::ostream &os,
	const std::vector<std::vector<uint8_t>> &data,
	std::vector<int64_t> &positions,
	WriterPackType pack_type
) {
	// After this function, positions[i] is:
	//  - = 0: If variable i has no wave data
	//  - < 0: The negative value from flushValueChangeData_ValueChanges_UniquifyWaveData_,
	//  unchanged
	//  - > 0: The size (in bytes) of the wave data block for *previous* variable,
	//         the previous block size of the first block is 1 (required by FST spec).
	StreamWriteHelper h(os);
	int64_t previous_size = 1;
	uint64_t written_count = 0;
	std::vector<uint8_t> compressed_data;
	for (size_t i = 0; i < positions.size(); ++i) {
		if (positions[i] < 0) {
			// duplicate (negative index), do nothing
		} else if (data[i].empty()) {
			// no change (empty data), positions[i] remains 0
		} else {
			// try to compress
			const uint8_t *selected_data;
			size_t selected_size;
			if (pack_type == WriterPackType::NO_COMPRESSION || data[i].size() <= 32) {
				selected_data = data[i].data();
				selected_size = data[i].size();
			} else {
				compressUsingLz4(data[i], compressed_data);
				const std::pair<const uint8_t *, size_t> selected_pair =
					selectSmaller(compressed_data, data[i]);
				selected_data = selected_pair.first;
				selected_size = selected_pair.second;
			}
			const bool is_compressed = selected_data != data[i].data();

			// non-empty unique data, write it
			written_count++;
			std::streamoff bytes_written;
			h  //
				.beginOffset(bytes_written)
				// FST spec: 0 means no compression, >0 for the size of the original data
				.writeLEB128(is_compressed ? data[i].size() : 0)
				.write(selected_data, selected_size)
				.endOffset(&bytes_written);
			positions[i] = previous_size;
			previous_size = bytes_written;
		}
	}
	return written_count;
}

void detail::ValueChangeData::writeEncodedPositions(
	const std::vector<int64_t> &encoded_positions, std::ostream &os
) {
	// Encode positions with the specified run/varint rules into a varint buffer.
	StreamWriteHelper h(os);

	size_t i = 0;
	const size_t n = encoded_positions.size();

	// arbitrary positive value for prev_negative
	// so that first negative is always != prev_negative
	int64_t prev_negative = 1;

	// Please refer to the comments in
	// flushValueChangeData_ValueChanges_EncodePositionsAndwriteWaveData_() for the encoding rules
	// of positions.
	while (i < n) {
		if (encoded_positions[i] == 0) {
			// zero: handle zero run-length
			size_t run = 0;
			while (i < n && encoded_positions[i] == 0) {
				++run;
				++i;
			}
			// encode as signed (run << 1) | 0 and write as signed LEB128
			h.writeLEB128(run << 1);
		} else {
			// non-zero
			int64_t value_to_encode = 0;
			int64_t cur = encoded_positions[i];
			if (cur < 0) {
				if (cur == prev_negative) {
					value_to_encode = 0;
				} else {
					value_to_encode = cur;
					prev_negative = cur;
				}
			} else {
				value_to_encode = cur;
			}

			// encode as signed (value << 1) | 1 and write as signed LEB128
			h.writeLEB128Signed((value_to_encode << 1) | 1);

			++i;
		}
	}
}

void detail::ValueChangeData::writeTimestamps(std::vector<uint8_t> &os) const {
	// Build LEB128-encoded delta stream (first delta is timestamp[0] - 0)
	StreamVectorWriteHelper h(os);
	uint64_t prev{0};
	for (size_t i{0}; i < m_timestamps.size(); ++i) {
		const uint64_t cur{m_timestamps[i]};
		const uint64_t delta{cur - prev};
		h.writeLEB128(delta);
		prev = cur;
	}
}

void Writer::flushValueChangeDataConstPart_(
	const detail::ValueChangeData &vcd, std::ostream &os, WriterPackType pack_type
) {
	// 0. setup
	StreamWriteHelper h(os);

	// 1. write Block Header & Global Fields (start/end/mem_req placeholder)
	// FST_BL_VCDATA_DYN_ALIAS2 (8) maps to WaveDataVersion3 in fst_file.h
	// The positions we cannot fill in yet
	const auto p_tmp1 = [&]() {
		std::streamoff start_pos, memory_usage_pos;
		h                            //
			.beginOffset(start_pos)  // record start position
			.writeBlockHeader(BlockType::WAVE_DATA_VERSION3, 0 /* Length placeholder 0 */)
			.writeUInt(vcd.m_timestamps.front())
			.writeUInt(vcd.m_timestamps.back())
			.beginOffset(memory_usage_pos)  // record memory usage position
			.writeUInt<uint64_t>(0);        // placeholder for memory usage
		return std::make_pair(start_pos, memory_usage_pos);
	}();
	const std::streamoff start_pos{p_tmp1.first};
	const std::streamoff memory_usage_pos{p_tmp1.second};

	// 2. Bits Section
	{
		std::vector<uint8_t> bits_data;
		vcd.writeInitialBits(bits_data);
		std::vector<uint8_t> bits_data_compressed;
		const uint8_t *selected_data;
		size_t selected_size;
		if (pack_type == WriterPackType::NO_COMPRESSION || bits_data.size() < 32) {
			selected_data = bits_data.data();
			selected_size = bits_data.size();
		} else {
			compressUsingZlib(bits_data, bits_data_compressed, 4);
			const std::pair<const uint8_t *, size_t> selected_pair =
				selectSmaller(bits_data_compressed, bits_data);
			selected_data = selected_pair.first;
			selected_size = selected_pair.second;
		}

		h                                              //
			.writeLEB128(bits_data.size())             // uncompressed length
			.writeLEB128(selected_size)                // compressed length
			.writeLEB128(vcd.m_variable_infos.size())  // bits count
			.write(selected_data, selected_size);
	}

	// 3. Waves Section
	// Note: We need positions for the next section
	const auto p_tmp2 = [&, pack_type]() {
		std::vector<std::vector<uint8_t>> wave_data{vcd.computeWaveData()};
		const size_t memory_usage{std::accumulate(
			wave_data.begin(),
			wave_data.end(),
			size_t(0),
			[](size_t a, const std::vector<uint8_t> &b) { return a + b.size(); }
		)};
		std::vector<int64_t> positions{vcd.uniquifyWaveData(wave_data)};
		h
			// Note: this is not a typo, I expect we shall write count here.
			// but the spec indeed write vcd.variable_infos.size(),
			// which is repeated 1 times in header block, 2 times in valuechange block
			.writeLEB128(vcd.m_variable_infos.size())
			.writeUInt(uint8_t('4'));
		const uint64_t count{detail::ValueChangeData::encodePositionsAndwriteUniqueWaveData(
			os, wave_data, positions, pack_type
		)};
		(void)count;
		return std::make_pair(positions, memory_usage);
	}();
	const std::vector<int64_t> positions{p_tmp2.first};
	const size_t memory_usage{p_tmp2.second};

	// 4. Position Section
	{
		const std::streampos pos_begin{os.tellp()};
		vcd.writeEncodedPositions(positions, os);
		const uint64_t pos_size{static_cast<uint64_t>(os.tellp() - pos_begin)};
		h.writeUInt(pos_size);  // Length comes AFTER data for positions
	}

	// 5. Time Section
	{
		std::vector<uint8_t> time_data;
		vcd.writeTimestamps(time_data);
		std::vector<uint8_t> time_data_compressed;
		const uint8_t *selected_data;
		size_t selected_size;
		if (pack_type == WriterPackType::NO_COMPRESSION) {
			selected_data = time_data.data();
			selected_size = time_data.size();
		} else {
			compressUsingZlib(time_data, time_data_compressed, 9);
			const std::pair<const uint8_t *, size_t> selected_pair =
				selectSmaller(time_data_compressed, time_data);
			selected_data = selected_pair.first;
			selected_size = selected_pair.second;
		}
		h                                                   //
			.write(selected_data, selected_size)            // time data
			.writeUInt(time_data.size())                    // uncompressed len
			.writeUInt(selected_size)                       // compressed len
			.writeUInt(uint64_t(vcd.m_timestamps.size()));  // count
	}

	// 6. Patch Block Length and Memory Required
	std::streamoff end_pos{0};
	h  //
		.beginOffset(end_pos)
		// Patch Block Length (after 1 byte Type)
		.seek(start_pos + std::streamoff(1), std::ios_base::beg)
		.writeUInt<uint64_t>(static_cast<uint64_t>(end_pos - start_pos - 1))
		// Patch Memory Required
		.seek(memory_usage_pos, std::ios_base::beg)
		.writeUInt<uint64_t>(static_cast<uint64_t>(memory_usage))
		// Restore position to end
		.seek(end_pos, std::ios_base::beg);
}

namespace {  // Helper functions for createEnumTable

void appendEscToString(const string_view_pair in, std::string &out) {
	for (size_t i{0}; i < in.m_size; ++i) {
		const char c{in.m_data[i]};
		switch (c) {
			// clang-format off
		case '\a': { out += "\\a"; break; }
		case '\b': { out += "\\b"; break; }
		case '\f': { out += "\\f"; break; }
		case '\n': { out += "\\n"; break; }
		case '\r': { out += "\\r"; break; }
		case '\t': { out += "\\t"; break; }
		case '\v': { out += "\\v"; break; }
		case '\'': { out += "\\'"; break; }
		case '\"': { out += "\\\""; break; }
		case '\\': { out += "\\\\"; break; }
		case '?': { out += "\\?"; break; }
		// clang-format on
		default: {
			if (c > ' ' && c <= '~') {
				out += c;
			} else {
				unsigned char val = static_cast<unsigned char>(c);
				out += '\\';
				out += (val / 64) + '0';
				val &= 63;
				out += (val / 8) + '0';
				val &= 7;
				out += val + '0';
			}
			break;
		}
		}
	}
}

}  // namespace

void Writer::setAttrBegin(
	Hierarchy::AttrType attrtype,
	Hierarchy::AttrSubType subtype,
	const string_view_pair attrname,
	uint64_t arg
) {
	FST_CHECK(!m_hierarchy_finalized_);

	StreamVectorWriteHelper h(m_hierarchy_buffer_);

	if (attrtype > Hierarchy::AttrType::MAX) {
		attrtype = Hierarchy::AttrType::MISC;
		subtype = Hierarchy::AttrSubType::MISC_UNKNOWN;
	}

	switch (attrtype) {
		// clang-format off
	case Hierarchy::AttrType::ARRAY:
		if (
			subtype < Hierarchy::AttrSubType::ARRAY_NONE ||
			subtype > Hierarchy::AttrSubType::ARRAY_SPARSE
		) {
			subtype = Hierarchy::AttrSubType::ARRAY_NONE;
		}
		break;
	case Hierarchy::AttrType::ENUM:
		if (
			subtype < Hierarchy::AttrSubType::ENUM_SV_INTEGER ||
			subtype > Hierarchy::AttrSubType::ENUM_TIME
		) {
			subtype = Hierarchy::AttrSubType::ENUM_SV_INTEGER;
		}
		break;
	case Hierarchy::AttrType::PACK:
		if (
			subtype < Hierarchy::AttrSubType::PACK_NONE ||
			subtype > Hierarchy::AttrSubType::PACK_SPARSE
		) {
			subtype = Hierarchy::AttrSubType::PACK_NONE;
		}
		break;
	// clang-format on
	case Hierarchy::AttrType::MISC:
	default:
		break;
	}

	h  //
		.writeU8Enum(Hierarchy::ScopeControlType::GEN_ATTR_BEGIN)
		.writeU8Enum(attrtype)
		.writeU8Enum(subtype)
		.writeString0(attrname)
		.writeLEB128(arg);
}

EnumHandle Writer::createEnumTable(
	const string_view_pair name,
	uint32_t min_valbits,
	const std::vector<std::pair<string_view_pair, string_view_pair>> &literal_val_arr
) {
	EnumHandle handle{0};

	if (name.m_size == 0 || literal_val_arr.empty()) {
		return handle;
	}

	std::string attr_str;
	attr_str.reserve(256);
	attr_str.append(name.m_data, name.m_size);
	attr_str += ' ';
	attr_str += std::to_string(literal_val_arr.size());
	attr_str += ' ';

	for (const auto &p : literal_val_arr) {
		const string_view_pair literal{p.first};
		// literal
		appendEscToString(literal, attr_str);
		attr_str += ' ';
	}
	for (const auto &p : literal_val_arr) {
		const string_view_pair val{p.second};
		// val (with padding)
		if (min_valbits > 0 && val.m_size < min_valbits) {
			attr_str.insert(attr_str.end(), min_valbits - val.m_size, '0');
		}
		appendEscToString(val, attr_str);
		attr_str += ' ';
	}
	attr_str.pop_back();  // remove last space

	handle = ++m_enum_count_;
	setAttrBegin(
		Hierarchy::AttrType::MISC,
		Hierarchy::AttrSubType::MISC_ENUMTABLE,
		make_string_view_pair(attr_str.c_str(), attr_str.size()),
		handle
	);

	return handle;
}

}  // namespace fst
