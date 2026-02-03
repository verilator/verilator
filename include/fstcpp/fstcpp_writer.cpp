// SPDX-FileCopyrightText: 2025-2026 Yu-Sheng Lin <johnjohnlys@gmail.com>
// SPDX-FileCopyrightText: 2025-2026 Yoda Lee <lc85301@gmail.com>
// SPDX-License-Identifier: MIT
// direct include
#include "fstcpp/fstcpp_writer.h"
// C system headers
// C++ standard library headers
#include <cstdio>
#include <cstring>
#include <iostream>
#include <numeric>
#include <stdexcept>
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

using namespace std;

// AT(x) is used to access vector at index x, and it will throw exception if out of bound
// in debug mode, but in release mode, it will not throw exception
// Usually you should only need AT(x) only at very hot code path.
#ifndef NDEBUG
#	define AT(x) .at(x)
#else
#	define AT(x) [x]
#endif

namespace fst {

namespace detail {

void BlackoutData::emitDumpActive(uint64_t current_timestamp, bool enable) {
	StreamVectorWriteHelper h(buffer);
	h.writeUIntBE<uint8_t>(enable).writeLEB128(current_timestamp - previous_timestamp);
	++count;
}

ValueChangeData::ValueChangeData() {
	variable_infos.reserve(1024);
}

ValueChangeData::~ValueChangeData() = default;

void ValueChangeData::keepOnlyTheLatestValue() {
	for (auto &v : variable_infos) {
		v.KeepOnlyTheLatestValue();
	}
	FST_CHECK(not timestamps.empty());
	timestamps.front() = timestamps.back();
	timestamps.resize(1);
}

}  // namespace detail

void Writer::open(const string_view_pair name) {
	FST_CHECK(not main_fst_file_.is_open());
	main_fst_file_.open(string(name.first, name.second), ios::binary);
	// reserve space for header, we will write it at Close(), append geometry and hierarchy at the
	// end wave data will be flushed in between
	main_fst_file_.seekp(kSharedBlockHeaderSize + HeaderInfo::total_size, ios_base::beg);
}

void Writer::close() {
	if (not main_fst_file_.is_open()) return;
	// Finalize header fields
	if (header_.date[0] == '\0') {
		// date is not set yet, set to the current date
		setDate();
	}
	if (header_.start_time == kInvalidTime) {
		header_.start_time = 0;
	}
	flushValueChangeData_(value_change_data_, main_fst_file_);
	appendGeometry_(main_fst_file_);
	appendHierarchy_(main_fst_file_);
	appendBlackout_(main_fst_file_);
	// Note: write header seek to 0, so we need to do
	// this after all append operations
	writeHeader_(header_, main_fst_file_);
	main_fst_file_.close();
}

/////////////////////////////////////////
// Hierarchy / variable API
/////////////////////////////////////////
void Writer::setScope(
	Hierarchy::ScopeType scopetype,
	const string_view_pair scopename,
	const string_view_pair scopecomp
) {
	FST_CHECK(not hierarchy_finalized_);
	StreamVectorWriteHelper h(hierarchy_buffer_);
	h  //
		.writeU8Enum(Hierarchy::ScopeControlType::VCD_SCOPE)
		.writeU8Enum(scopetype)
		.writeString0(scopename)
		.writeString0(scopecomp);
	++header_.num_scopes;
}

void Writer::upscope() {
	FST_CHECK(not hierarchy_finalized_);
	// TODO: shall we inline it?
	StreamVectorWriteHelper h(hierarchy_buffer_);
	h.writeU8Enum(Hierarchy::ScopeControlType::VCD_UPSCOPE);
}

Handle Writer::createVar(
	Hierarchy::VarType vartype,
	Hierarchy::VarDirection vardir,
	uint32_t bitwidth,
	const string_view_pair name,
	Handle alias_handle
) {
	FST_CHECK(not hierarchy_finalized_);
	// write hierarchy entry: type, direction, name, length, alias
	StreamVectorWriteHelper h(hierarchy_buffer_);

	// determine real/string handling like original C implementation
	bool is_real = false;
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
	if (alias_handle > header_.num_handles) {
		// sanitize
		alias_handle = 0;
	}
	const bool is_alias = alias_handle != 0;
	// This counter is incremented whether alias or non-alias
	++header_.num_vars;
	if (not is_alias) {
		// This counter is incremented only for non-alias variables
		++header_.num_handles;
		alias_handle = header_.num_handles;
	}

	h  //
		.writeU8Enum(vartype)
		.writeU8Enum(vardir)
		.writeString0(name)
		.writeLEB128(bitwidth)
		.writeLEB128(is_alias ? alias_handle : 0);

	// If alias_handle == 0, we must allocate geom/valpos/curval entries and create a new handle
	if (not is_alias) {
		StreamVectorWriteHelper g(geometry_buffer_);
		// I don't know why the original C implementation encode bitwidth again
		const uint32_t geom_len = (bitwidth == 0 ? uint32_t(-1) : is_real ? uint32_t(0) : bitwidth);
		g.writeLEB128(geom_len);
		value_change_data_.variable_infos.emplace_back(bitwidth, is_real);
	}

	return alias_handle;
}

// LCOV_EXCL_START
Handle Writer::createVar2(
	Hierarchy::VarType vartype,
	Hierarchy::VarDirection vardir,
	uint32_t bitwidth,
	const string_view_pair name,
	Handle alias_handle,
	const string_view_pair type,
	Hierarchy::SupplementalVarType svt,
	Hierarchy::SupplementalDataType sdt
) {
	FST_CHECK(not hierarchy_finalized_);
	(void)vartype;
	(void)vardir;
	(void)bitwidth;
	(void)name;
	(void)alias_handle;
	(void)type;
	(void)svt;
	(void)sdt;
	throw runtime_error("TODO");
	return 0;
}
// LCOV_EXCL_STOP

/////////////////////////////////////////
// Waveform API
/////////////////////////////////////////
void Writer::emitTimeChange(uint64_t tim) {
	finalizeHierarchy_();

	if (value_change_data_usage_ > value_change_data_flush_threshold_ or flush_pending_) {
		flushValueChangeData_(value_change_data_, main_fst_file_);
	}

	// Update header
	header_.start_time = min(header_.start_time, tim);
	header_.end_time = tim;

	if (value_change_data_.timestamps.empty() or value_change_data_.timestamps.back() != tim) {
		value_change_data_.timestamps.push_back(tim);
	}
}

void Writer::emitDumpActive(bool enable) {
	// TODO: this API is not fully understood, need to check
	FST_CHECK(not value_change_data_.timestamps.empty());
	blackout_data_.emitDumpActive(value_change_data_.timestamps.back(), enable);
}

template <typename T, typename... U>
uint64_t emitValueHelperStaticDispatch_(
	VariableInfo *var_info, const uint64_t time_index, U &&...val
) {
	return static_cast<T *>(var_info)->emitValueChange(time_index, std::forward<U>(val)...);
}

template <typename... T>
void Writer::emitValueChangeHelper_(Handle handle, T &&...val) {
	// Let data prefetch go first
	auto &var_info = value_change_data_.variable_infos AT(handle - 1);
	__builtin_prefetch(var_info.data_ptr() + var_info.size() - 1, 1, 0);

	finalizeHierarchy_();

	// Original implementation: virtual, but vtable is too costly, we switch to if-else static
	// dispatch
	value_change_data_usage_ +=
		var_info.emitValueChange(value_change_data_.timestamps.size() - 1, std::forward<T>(val)...);
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
	auto &var_info = value_change_data_.variable_infos AT(handle - 1);
	const uint32_t bitwidth = var_info.bitwidth();
	FST_DCHECK_NE(bitwidth, 0);

	val += bitwidth;
	thread_local static vector<uint64_t> packed_value_buffer;
	const unsigned num_words = (bitwidth + 63) / 64;
	packed_value_buffer.assign(num_words, 0);
	for (unsigned i = 0; i < num_words; ++i) {
		const char *start = val - std::min((i + 1) * 64, bitwidth);
		const char *end = val - 64 * i;
		packed_value_buffer[i] = 0;
		for (const char *p = start; p < end; ++p) {
			// No checking for invalid characters, follow original C implementation
			packed_value_buffer[i] <<= 1;
			packed_value_buffer[i] |= (*p - '0');
		}
	}

	if (bitwidth <= 64) {
		emitValueChange(handle, packed_value_buffer.front());
	} else {
		emitValueChange(handle, packed_value_buffer.data(), EncodingType::BINARY);
	}
}

/////////////////////////////////////////
// File flushing functions
/////////////////////////////////////////
void Writer::writeHeader_(const Header &header, ostream &os) {
	StreamWriteHelper h(os);
	static char kDefaultWriterName[sizeof(header.writer)] = "fstcppWriter";
	const char *writer_name = header.writer[0] == '\0' ? kDefaultWriterName : header.writer;

	// Actual write
	h  //
		.seek(streamoff(0), ios_base::beg)
		.writeBlockHeader(BlockType::HEADER, HeaderInfo::total_size)
		.writeUInt(header.start_time)
		.writeUInt(header.end_time)
		.writeFloat(HeaderInfo::kEndianessMagicIdentifier)
		.writeUInt(header.writer_memory_use)
		.writeUInt(header.num_scopes)
		.writeUInt(header.num_vars)
		.writeUInt(header.num_handles)
		.writeUInt(header.num_value_change_data_blocks)
		.writeUInt(header.timescale)
		.write(writer_name, sizeof(header.writer))
		.write(header.date, sizeof(header.date))
		.fill('\0', HeaderInfo::Size::reserved)
		.writeUInt(static_cast<uint8_t>(header.filetype))
		.writeUInt(header.timezero);

	FST_DCHECK_EQ(os.tellp(), HeaderInfo::total_size + kSharedBlockHeaderSize);
};

namespace {  // compression helpers

// These API pass compressed_data to avoid frequent reallocations
void compressUsingLz4(const vector<uint8_t> &uncompressed_data, vector<uint8_t> &compressed_data) {
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
	const vector<uint8_t> &uncompressed_data, vector<uint8_t> &compressed_data, int level
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
		throw runtime_error(
			"Failed to compress data with zlib, error code: " + to_string(z_status)
		);
	}
	compressed_data.resize(compressed_bound);
}

pair<const uint8_t *, size_t> selectSmaller(
	const vector<uint8_t> &compressed_data, const vector<uint8_t> &uncompressed_data
) {
	pair<const uint8_t *, size_t> ret;
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
void Writer::appendGeometry_(ostream &os) {
	if (geometry_buffer_.empty()) {
		// skip the geometry block if there is no data
		return;
	}
	vector<uint8_t> geometry_buffer_compressed_;
	compressUsingZlib(geometry_buffer_, geometry_buffer_compressed_, 9);
	// TODO: Replace with structured binding in C++17
	const auto selected_pair = selectSmaller(geometry_buffer_compressed_, geometry_buffer_);
	const auto selected_data = selected_pair.first;
	const auto selected_size = selected_pair.second;

	StreamWriteHelper h(os);
	h  //
		.seek(0, ios_base::end)
		// 16 is for the uncompressed_size and header_.num_handles
		.writeBlockHeader(BlockType::GEOMETRY, selected_size + 16)
		.writeUInt<uint64_t>(geometry_buffer_.size())
		// I don't know why the original C implementation write num_handles again here
		// but we have to follow it
		.writeUInt(header_.num_handles)
		.write(selected_data, selected_size);
}

void Writer::appendHierarchy_(ostream &os) {
	if (hierarchy_buffer_.empty()) {
		// skip the hierarchy block if there is no data
		return;
	}

	// compress hierarchy_buffer_ using LZ4.
	const int compressed_bound = LZ4_compressBound(hierarchy_buffer_.size());
	vector<uint8_t> hierarchy_buffer_compressed_(compressed_bound);
	const int compressed_size = LZ4_compress_default(
		reinterpret_cast<const char *>(hierarchy_buffer_.data()),
		reinterpret_cast<char *>(hierarchy_buffer_compressed_.data()),
		hierarchy_buffer_.size(),
		compressed_bound
	);

	StreamWriteHelper h(os);
	h  //
		.seek(0, ios_base::end)
		// +16 is for the uncompressed_size
		.writeBlockHeader(BlockType::HIERARCHY_LZ4_COMPRESSED, compressed_size + 8)
		.writeUInt<uint64_t>(hierarchy_buffer_.size())
		.write(hierarchy_buffer_compressed_.data(), compressed_size);
}

void Writer::appendBlackout_(ostream &os) {
	if (blackout_data_.count == 0) {
		// skip the blackout block if there is no data
		return;
	}
	const vector<uint8_t> &blackout_data = blackout_data_.buffer;
	const auto begin_of_blackout_block = os.tellp();
	StreamWriteHelper h(os);
	h  //
	   // skip the block header
		.seek(kSharedBlockHeaderSize, ios_base::cur)
		// Note: we cannot know the size beforehand since this length is LEB128 encoded
		.writeLEB128(blackout_data.size())
		.write(blackout_data.data(), blackout_data.size());

	const auto size_of_blackout_block = os.tellp() - begin_of_blackout_block;
	h  //
	   // go back to the beginning of the block
		.seek(begin_of_blackout_block, ios_base::beg)
		// and write the block header
		.writeBlockHeader(BlockType::BLACKOUT, size_of_blackout_block - kSharedBlockHeaderSize);
}

void detail::ValueChangeData::writeInitialBits(vector<uint8_t> &os) const {
	// Build vc_bits_data by concatenating each variable's initial bits as documented.
	// We will not compress for now; just generate the raw bytes and print summary to stdout.
	for (size_t i = 0; i < variable_infos.size(); ++i) {
		auto &vref = variable_infos[i];
		vref.dumpInitialBits(os);
	}
}

vector<vector<uint8_t>> detail::ValueChangeData::computeWaveData() const {
	const size_t N = variable_infos.size();
	vector<vector<uint8_t>> data(N);
	for (size_t i = 0; i < N; ++i) {
		variable_infos[i].dumpValueChanges(data[i]);
	}
	return data;
}

vector<int64_t> detail::ValueChangeData::uniquifyWaveData(vector<vector<uint8_t>> &data) {
	// After this function, positions[i] is:
	//  - = 0: If data[i] is unique (first occurrence)
	//  - < 0: If data[i] is a duplicate, encoded as -(original_index + 1)
	vector<int64_t> positions(data.size(), 0);
	struct MyHash {
		size_t operator()(const vector<uint8_t> *vec) const {
			size_t seed = 0;
			for (auto v : *vec) {
				seed ^= v + 0x9e3779b9 + (seed << 6) + (seed >> 2);
			}
			return seed;
		}
	};
	struct MyEqual {
		bool operator()(const vector<uint8_t> *a, const vector<uint8_t> *b) const {
			return *a == *b;
		}
	};
	unordered_map<const vector<uint8_t> *, int64_t, MyHash, MyEqual> data_map;
	for (size_t i = 0; i < data.size(); ++i) {
		if (data[i].empty()) {
			continue;
		}
		// insert vec->i to data_map if not exists
		auto p = data_map.emplace(&data[i], static_cast<int64_t>(i));
		auto it = p.first;
		auto inserted = p.second;

		if (not inserted) {
			// duplicated wave data found
			positions[i] = -(it->second + 1);
			// clear data to save memory
			data[i].clear();
		}
	}
	return positions;
}

uint64_t detail::ValueChangeData::encodePositionsAndwriteUniqueWaveData(
	ostream &os,
	const vector<vector<uint8_t>> &data,
	vector<int64_t> &positions,
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
	vector<uint8_t> compressed_data;
	for (size_t i = 0; i < positions.size(); ++i) {
		if (positions[i] < 0) {
			// duplicate (negative index), do nothing
		} else if (data[i].empty()) {
			// no change (empty data), positions[i] remains 0
		} else {
			// try to compress
			const uint8_t *selected_data;
			size_t selected_size;
			if (pack_type == WriterPackType::NO_COMPRESSION or data[i].size() <= 32) {
				selected_data = data[i].data();
				selected_size = data[i].size();
			} else {
				compressUsingLz4(data[i], compressed_data);
				const auto selected_pair = selectSmaller(compressed_data, data[i]);
				selected_data = selected_pair.first;
				selected_size = selected_pair.second;
			}
			const bool is_compressed = selected_data != data[i].data();

			// non-empty unique data, write it
			written_count++;
			streamoff bytes_written;
			h  //
				.BeginOffset(bytes_written)
				// FST spec: 0 means no compression, >0 for the size of the original data
				.writeLEB128(is_compressed ? data[i].size() : 0)
				.write(selected_data, selected_size)
				.EndOffset(&bytes_written);
			positions[i] = previous_size;
			previous_size = bytes_written;
		}
	}
	return written_count;
}

void detail::ValueChangeData::writeEncodedPositions(
	const vector<int64_t> &encoded_positions, ostream &os
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

void detail::ValueChangeData::writeTimestamps(vector<uint8_t> &os) const {
	// Build LEB128-encoded delta stream (first delta is timestamp[0] - 0)
	StreamVectorWriteHelper h(os);
	uint64_t prev = 0;
	for (size_t i = 0; i < timestamps.size(); ++i) {
		const uint64_t cur = timestamps[i];
		const uint64_t delta = cur - prev;
		h.writeLEB128(delta);
		prev = cur;
	}
}

void Writer::flushValueChangeDataConstPart_(
	const detail::ValueChangeData &vcd, ostream &os, WriterPackType pack_type
) {
	// 0. setup
	StreamWriteHelper h(os);

	// 1. write Block Header & Global Fields (start/end/mem_req placeholder)
	// FST_BL_VCDATA_DYN_ALIAS2 (8) maps to WaveDataVersion3 in fst_file.h
	// The positions we cannot fill in yet
	const auto p_tmp1 = [&]() {
		streamoff start_pos, memory_usage_pos;
		h                            //
			.BeginOffset(start_pos)  // record start position
			.writeBlockHeader(BlockType::WAVE_DATA_VERSION3, 0 /* Length placeholder 0 */)
			.writeUInt(vcd.timestamps.front())
			.writeUInt(vcd.timestamps.back())
			.BeginOffset(memory_usage_pos)  // record memory usage position
			.writeUInt<uint64_t>(0);        // placeholder for memory usage
		return make_pair(start_pos, memory_usage_pos);
	}();
	const auto start_pos = p_tmp1.first;
	const auto memory_usage_pos = p_tmp1.second;

	// 2. Bits Section
	{
		vector<uint8_t> bits_data;
		vcd.writeInitialBits(bits_data);
		vector<uint8_t> bits_data_compressed;
		const uint8_t *selected_data;
		size_t selected_size;
		if (pack_type == WriterPackType::NO_COMPRESSION or bits_data.size() < 32) {
			selected_data = bits_data.data();
			selected_size = bits_data.size();
		} else {
			compressUsingZlib(bits_data, bits_data_compressed, 4);
			const auto selected_pair = selectSmaller(bits_data_compressed, bits_data);
			selected_data = selected_pair.first;
			selected_size = selected_pair.second;
		}

		h                                            //
			.writeLEB128(bits_data.size())           // uncompressed length
			.writeLEB128(selected_size)              // compressed length
			.writeLEB128(vcd.variable_infos.size())  // bits count
			.write(selected_data, selected_size);
	}

	// 3. Waves Section
	// Note: We need positions for the next section
	const auto p_tmp2 = [&, pack_type]() {
		auto wave_data = vcd.computeWaveData();
		const size_t memory_usage =
			accumulate(wave_data.begin(), wave_data.end(), size_t(0), [](size_t a, const auto &b) {
				return a + b.size();
			});
		auto positions = vcd.uniquifyWaveData(wave_data);
		h
			// Note: this is not a typo, I expect we shall write count here.
			// but the spec indeed write vcd.variable_infos.size(),
			// which is repeated 1 times in header block, 2 times in valuechange block
			.writeLEB128(vcd.variable_infos.size())
			.writeUInt(uint8_t('4'));
		const uint64_t count = detail::ValueChangeData::encodePositionsAndwriteUniqueWaveData(
			os, wave_data, positions, pack_type
		);
		(void)count;
		return make_pair(positions, memory_usage);
	}();
	const auto positions = p_tmp2.first;
	const auto memory_usage = p_tmp2.second;

	// 4. Position Section
	{
		const auto pos_begin = os.tellp();
		vcd.writeEncodedPositions(positions, os);
		const uint64_t pos_size = os.tellp() - pos_begin;
		h.writeUInt(pos_size);  // Length comes AFTER data for positions
	}

	// 5. Time Section
	{
		vector<uint8_t> time_data;
		vcd.writeTimestamps(time_data);
		vector<uint8_t> time_data_compressed;
		const uint8_t *selected_data;
		size_t selected_size;
		if (pack_type == WriterPackType::NO_COMPRESSION) {
			selected_data = time_data.data();
			selected_size = time_data.size();
		} else {
			compressUsingZlib(time_data, time_data_compressed, 9);
			const auto selected_pair = selectSmaller(time_data_compressed, time_data);
			selected_data = selected_pair.first;
			selected_size = selected_pair.second;
		}
		h                                                 //
			.write(selected_data, selected_size)          // time data
			.writeUInt(time_data.size())                  // uncompressed len
			.writeUInt(selected_size)                     // compressed len
			.writeUInt(uint64_t(vcd.timestamps.size()));  // count
	}

	// 6. Patch Block Length and Memory Required
	streamoff end_pos;
	h  //
		.BeginOffset(end_pos)
		// Patch Block Length (after 1 byte Type)
		.seek(start_pos + streamoff(1), ios_base::beg)
		.writeUInt<uint64_t>(end_pos - start_pos - 1)
		// Patch Memory Required
		.seek(memory_usage_pos, ios_base::beg)
		.writeUInt<uint64_t>(memory_usage)
		// Restore position to end
		.seek(end_pos, ios_base::beg);
}

namespace {  // Helper functions for createEnumTable

void appendEscToString(const string_view_pair in, string &out) {
	for (size_t i = 0; i < in.second; ++i) {
		const char c = in.first[i];
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
	FST_CHECK(not hierarchy_finalized_);

	StreamVectorWriteHelper h(hierarchy_buffer_);

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

namespace {

// overload for string += string_view_
// Remove this once C++17 is required
}  // namespace

EnumHandle Writer::createEnumTable(
	const string_view_pair name,
	uint32_t min_valbits,
	const vector<pair<string_view_pair, string_view_pair>> &literal_val_arr
) {
	EnumHandle handle = 0;

	if (name.second == 0 or literal_val_arr.empty()) {
		return handle;
	}

	string attr_str;
	attr_str.reserve(256);
	attr_str.append(name.first, name.second);
	attr_str += ' ';
	attr_str += to_string(literal_val_arr.size());
	attr_str += ' ';

	for (const auto &p : literal_val_arr) {
		const auto &literal = p.first;
		// literal
		appendEscToString(literal, attr_str);
		attr_str += ' ';
	}
	for (const auto &p : literal_val_arr) {
		const auto &val = p.second;
		// val (with padding)
		if (min_valbits > 0 and val.second < min_valbits) {
			attr_str.insert(attr_str.end(), min_valbits - val.second, '0');
		}
		appendEscToString(val, attr_str);
		attr_str += ' ';
	}
	attr_str.pop_back();  // remove last space

	handle = ++enum_count_;
	setAttrBegin(
		Hierarchy::AttrType::MISC,
		Hierarchy::AttrSubType::MISC_ENUMTABLE,
		make_string_view_pair(attr_str.c_str(), attr_str.size()),
		handle
	);

	return handle;
}

}  // namespace fst
