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
#include <algorithm>
#include <cstdint>
#include <ctime>
#include <fstream>
#include <vector>
#if __cplusplus >= 201703L
#	include <string_view>
#endif
// Other libraries' .h files.
// Your project's .h files.
#include "fstcpp/fstcpp_assertion.h"
#include "fstcpp/fstcpp_variable_info.h"

namespace fst {

class Writer;

namespace detail {

// We define BlackoutData here for better code inlining, no forward declaration
// Blackout is not implemented yet
struct BlackoutData {
	std::vector<uint8_t> m_buffer{};
	uint64_t m_previous_timestamp{0};
	uint64_t m_count{0};

	void emitDumpActive(uint64_t current_timestamp, bool enable);
};

// We define ValueChangeData here for better code inlining, no forward declaration
struct ValueChangeData {
	std::vector<VariableInfo> m_variable_infos{};
	std::vector<uint64_t> m_timestamps{};

	ValueChangeData();
	~ValueChangeData();

	void writeInitialBits(std::vector<uint8_t> &os) const;
	std::vector<std::vector<uint8_t>> computeWaveData() const;
	static std::vector<int64_t> uniquifyWaveData(std::vector<std::vector<uint8_t>> &data);
	static uint64_t encodePositionsAndwriteUniqueWaveData(
		std::ostream &os,
		const std::vector<std::vector<uint8_t>> &unique_data,
		std::vector<int64_t> &positions,
		WriterPackType pack_type
	);
	static void writeEncodedPositions(
		const std::vector<int64_t> &encoded_positions, std::ostream &os
	);
	void writeTimestamps(std::vector<uint8_t> &os) const;
	void keepOnlyTheLatestValue();
};

}  // namespace detail

class Writer {
	friend class WriterTest;

private:
	// File/memory buffers
	// 1. For hierarchy and geometry, we do not keep the data structure, instead we just
	//    serialize them into buffers, and compress+write them at the end of file.
	// 2. For header, we keep the data structure in memory since it is quite small
	// 3. For wave data, we keep a complicated data structure in memory,
	//    and flush them to file when necessary
	// 4. For blackout data, it is not implemented yet
	std::ofstream m_main_fst_file_{};
	std::vector<uint8_t> m_hierarchy_buffer_{};
	std::vector<uint8_t> m_geometry_buffer_{};
	// Temporary buffer for packing bit strings into words
	// Only used in emitValueChange(Handle, const char*)
	std::vector<uint64_t> m_packed_value_buffer_{};
	Header m_header_{};
	detail::BlackoutData m_blackout_data_{};  // Not implemented yet
	detail::ValueChangeData m_value_change_data_{};
	bool m_hierarchy_finalized_{false};
	WriterPackType m_pack_type_{WriterPackType::LZ4};
	uint64_t m_value_change_data_usage_{0};  // Note: this value is just an estimation
	uint64_t m_value_change_data_flush_threshold_{128 << 20};  // 128MB
	uint32_t m_enum_count_{0};
	bool m_flush_pending_{false};

public:
	Writer() {}
	Writer(const string_view_pair name) {
		if (name.m_size != 0) open(name);
	}
	~Writer() { close(); }

	Writer(const Writer &) = delete;
	Writer(Writer &&) = delete;
	Writer &operator=(const Writer &) = delete;
	Writer &operator=(Writer &&) = delete;

	// File control
	void open(const string_view_pair name);
	void close();

	//////////////////////////////
	// Header manipulation API
	//////////////////////////////
	const Header &getHeader() const { return m_header_; }
	void setTimecale(int8_t timescale) { m_header_.m_timescale = timescale; }
	void setWriter(const string_view_pair writer) {
		const size_t len = std::min(writer.m_size, sizeof(m_header_.m_writer));
		std::copy_n(writer.m_data, len, m_header_.m_writer);
		if (len != sizeof(m_header_.m_writer)) {
			m_header_.m_writer[len] = '\0';
		}
	}
	void setDate(const string_view_pair date_str) {
		const size_t len = date_str.m_size;
		FST_CHECK_EQ(len, sizeof(m_header_.m_date) - 1);
		std::copy_n(date_str.m_data, len, m_header_.m_date);
		m_header_.m_date[len] = '\0';
	}
	void setDate(const std::tm *d) { setDate(make_string_view_pair(std::asctime(d))); }
	void setDate() {
		// set date to now
		std::time_t t{std::time(nullptr)};
		setDate(std::localtime(&t));
	}
	void setTimezero(int64_t timezero) { m_header_.m_timezero = timezero; }

	//////////////////////////////
	// Change scope API
	//////////////////////////////
	void setScope(
		Hierarchy::ScopeType scopetype,
		const string_view_pair scopename,
		const string_view_pair scopecomp
	);
	void upscope();

	//////////////////////////////
	// Attribute / Misc API
	//////////////////////////////
	void setAttrBegin(
		Hierarchy::AttrType attrtype,
		Hierarchy::AttrSubType subtype,
		const string_view_pair attrname,
		uint64_t arg
	);
	void setAttrEnd() {
		m_hierarchy_buffer_.push_back(
			static_cast<uint8_t>(Hierarchy::ScopeControlType::GEN_ATTR_END)
		);
	}
	EnumHandle createEnumTable(
		const string_view_pair name,
		uint32_t min_valbits,
		const std::vector<std::pair<string_view_pair, string_view_pair>> &literal_val_arr
	);
	template <typename T1, typename T2>
	EnumHandle createEnumTable(
		const char *name,
		uint32_t min_valbits,
		const std::vector<std::pair<T1, T2>> &literal_val_arr
	) {
		std::vector<std::pair<string_view_pair, string_view_pair>> arr{};
		arr.reserve(literal_val_arr.size());
		for (const auto &p : literal_val_arr) {
			arr.emplace_back(make_string_view_pair(p.first), make_string_view_pair(p.second));
		}
		return createEnumTable(make_string_view_pair(name), min_valbits, arr);
	}
	void emitEnumTableRef(EnumHandle handle) {
		setAttrBegin(
			Hierarchy::AttrType::MISC,
			Hierarchy::AttrSubType::MISC_ENUMTABLE,
			make_string_view_pair(nullptr, 0),
			handle
		);
	}
	void setWriterPackType(WriterPackType pack_type) {
		FST_CHECK(pack_type != WriterPackType::ZLIB && pack_type != WriterPackType::FASTLZ);
		m_pack_type_ = pack_type;
	}

	//////////////////////////////
	// Create variable API
	//////////////////////////////
	Handle createVar(
		Hierarchy::VarType vartype,
		Hierarchy::VarDirection vardir,
		uint32_t bitwidth,
		const string_view_pair name,
		uint32_t alias_handle
	);
	// TODO
	// Handle createVar2(
	// 	Hierarchy::VarType vartype,
	// 	Hierarchy::VarDirection vardir,
	// 	uint32_t bitwidth,
	// 	const string_view_pair name,
	// 	uint32_t alias_handle,
	// 	const string_view_pair type,
	// 	Hierarchy::SupplementalVarType svt,
	// 	Hierarchy::SupplementalDataType sdt
	// );

	//////////////////////////////
	// Waveform API
	//////////////////////////////
	void emitTimeChange(uint64_t tim);
	// TODO
	// void emitDumpActive(bool enable);
	void emitValueChange(
		Handle handle, const uint32_t *val, EncodingType encoding = EncodingType::BINARY
	);
	void emitValueChange(
		Handle handle, const uint64_t *val, EncodingType encoding = EncodingType::BINARY
	);
	// Pass by value for small integers
	void emitValueChange(Handle handle, uint64_t val);
	// Add support for C-string value changes (e.g. fst string values)
	// Note: This function is mainly for GtkWave compatibility.
	// It is very dirty and inefficient, users should avoid using it.
	// - For double handles, const char* is interpreted as a double* (8B)
	// - For normal integer handles, const char* is "01xz..." (1B per bit)
	// We only ensure that this function works where Verilator use it.
	void emitValueChange(Handle handle, const char *val);

	// Flush value change data
	void flushValueChangeData() { m_flush_pending_ = true; }

private:
	// internal helpers
	static void writeHeader_(const Header &header, std::ostream &os);
	void appendGeometry_(std::ostream &os);
	void appendHierarchy_(std::ostream &os);
	void appendBlackout_(std::ostream &os);  // Not implemented yet
	// This function is used to flush value change data to file, and keep only the latest value in
	// memory Just want to separate the const part from the non-const part for code clarity
	static void flushValueChangeDataConstPart_(
		const detail::ValueChangeData &vcd, std::ostream &os, WriterPackType pack_type
	);
	void flushValueChangeData_(detail::ValueChangeData &vcd, std::ostream &os) {
		if (vcd.m_timestamps.empty()) {
			return;
		}
		flushValueChangeDataConstPart_(vcd, os, m_pack_type_);
		vcd.keepOnlyTheLatestValue();
		++m_header_.m_num_value_change_data_blocks;
		m_value_change_data_usage_ = 0;
		m_flush_pending_ = false;
	}
	void finalizeHierarchy_() {
		if (m_hierarchy_finalized_) return;
		m_hierarchy_finalized_ = true;
		// Original FST code comments: as a default, use 128MB and increment when
		// every 1M signals are defined.
		m_value_change_data_flush_threshold_ = (((m_header_.m_num_handles - 1) >> 20) + 1) << 27;
	}
	template <typename... T>
	void emitValueChangeHelper_(Handle handle, T &&...val);
};

}  // namespace fst
