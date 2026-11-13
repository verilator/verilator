// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2001-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
//
// Verilated tracing implementation code template common to all formats.
// This file is included by the format-specific implementations and
// should not be used otherwise.
//
//=============================================================================

// clang-format off

#ifndef VL_CPPCHECK
#if !defined(VL_SUB_T) || !defined(VL_BUF_T)
# error "This file should be included in trace format implementations"
#endif

#include "verilated_intrinsics.h"
#include "verilated_threads.h"
#include "verilated_trace.h"
#include <algorithm>
#include <cstring>
#include <list>

// clang-format on

// Values, and slices of packed values, are located assuming a little endian host
#if defined(__BYTE_ORDER__) && defined(__ORDER_LITTLE_ENDIAN__)
static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, "Tracing requires a little endian host");
#endif

//=============================================================================
// Static utility functions

static double timescaleToDouble(const char* unitp) VL_PURE {
    char* endp = nullptr;
    double value = std::strtod(unitp, &endp);
    // On error so we allow just "ns" to return 1e-9.
    if (value == 0.0 && endp == unitp) value = 1;
    unitp = endp;
    for (; *unitp && std::isspace(*unitp); ++unitp) {}
    switch (*unitp) {
    case 's': value *= 1e0; break;
    case 'm': value *= 1e-3; break;
    case 'u': value *= 1e-6; break;
    case 'n': value *= 1e-9; break;
    case 'p': value *= 1e-12; break;
    case 'f': value *= 1e-15; break;
    case 'a': value *= 1e-18; break;
    }
    return value;
}

//=========================================================================
// Hierarchy building

template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::addSignal(const char* namep, const VlRtmdVarType& varType,
                                                   const VlRtmdDataType& dtype,
                                                   const VlRtmdActSet& actSet, const void* datap,
                                                   uint32_t lsb) VL_MT_UNSAFE {
    const uint32_t bits = dtype.width();

    // Aliases of the same value share the same code
    const auto pair = m_codes.emplace(std::make_tuple(datap, lsb, bits), m_nextCode);
    const uint32_t code = pair.first->second;

    // If the value is not already in the map, it is a new signal, allocate it
    if (pair.second) {
        // Need one code per word
        m_nextCode += VL_WORDS_I(bits);
        // Need to know max bits for buffer sizing
        m_maxBits = std::max(m_maxBits, bits);
        // Record the value to dump, with the others of the same activity set, stored the same
        // way. A slice also with the others of packed values stored the same way.
        const StorageKind storage = dtype.storageKind();
        const auto groupOf = [&](StorageKind valueStorage) -> Group& {
            return m_groupMap[actSet][{storage, valueStorage}];
        };
        // If a slice exactly fills its storage, which is aligned, then extraction is pointer math
        const auto sliceIsWhole = [bits, lsb]() {
            // A wide slice of whole words, starting on a word
            if (bits > VL_QUADSIZE) return (bits % VL_EDATASIZE == 0) && (lsb % VL_EDATASIZE == 0);
            // A narrow slice exactly filling its storage, starting on a byte. Loaded unaligned.
            const bool fills = bits == VL_BYTESIZE || bits == VL_SHORTSIZE || bits == VL_IDATASIZE
                               || bits == VL_QUADSIZE;
            return fills && lsb % VL_BYTESIZE == 0;
        };
        if (lsb == NOLSB) {
            groupOf(storage).m_wholes.push_back({datap, code, bits});
        } else if (sliceIsWhole()) {
            // Dumped as the whole value at the byte holding its lowest bit (little endian)
            const uint8_t* const bytep = static_cast<const uint8_t*>(datap) + lsb / VL_BYTESIZE;
            groupOf(storage).m_wholes.push_back({bytep, code, bits});
        } else {
            const StorageKind valueStorage = VlRtmdDataType::storageKind(m_packedBits);
            groupOf(valueStorage).m_slices.push_back({datap, code, bits, lsb, m_packedBits});
        }
    }

    self()->declareSignal(code, namep, varType, dtype);
}

template <>
bool VerilatedTrace<VL_SUB_T, VL_BUF_T>::dumpvarsSelected(const char* namep) const {
    if (m_dumpvars.empty()) return true;  // Everything is selected
    const std::string path = pathName();
    const std::string name = path.empty() ? namep : path + '.' + namep;
    // To keep it simple, this is O(dumpvars * signals), but we expect few dumpvars
    for (const auto& item : m_dumpvars) {
        const int dumpvarsLevel = item.first;
        const std::string& hier = item.second;
        // Must match a whole prefix of hierarchy levels, e.g. "t" does not match "top"
        if (name.compare(0, hier.size(), hier) != 0) continue;
        if (name.size() > hier.size() && name[hier.size()] != '.') continue;
        // Must not be too deep below it
        const int levels = std::count(name.begin() + hier.size(), name.end(), '.');
        if (levels > dumpvarsLevel) continue;
        return true;
    }
    return false;
}

template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::traceInit() VL_MT_UNSAFE {
    // Without VerilatedContext::trace, trace the context of the opening thread
    if (!m_contextp) m_contextp = Verilated::threadContextp();

    // Context needs to be set to calculate unused signals
    if (!m_contextp->calcUnusedSigs()) {
        VL_FATAL_MT("", 0, "",
                    "Turning on wave traces requires VerilatedContext::traceEverOn(true) call "
                    "before time 0.");
    }

    // Note: It is possible to re-open a trace file (VCD in particular),
    // so we must reset the next code here, but it must have the same number
    // of codes on re-open
    const uint32_t expectedCodes = m_nextCode;
    m_nextCode = 1;
    m_maxBits = 0;

    m_groupVec.clear();
    m_modelps.clear();

    // Declare all enum types, in all models, before the signals that reference them
    bool anyTraced = false;
    bool anyParallel = false;
    for (const std::pair<const std::string, VerilatedModel*>& pair : m_contextp->models()) {
        const VlRtmd* const rtmdp = pair.second->rtmd();
        if (!rtmdp) continue;
        anyTraced |= rtmdp->m_opt.m_trace;
        anyParallel |= rtmdp->m_opt.m_traceParallel;
        m_modelps.push_back(pair.second);
        for (uint32_t i = 0;; ++i) {
            const VlRtmdDataTypeRow& typeRow = rtmdp->dataTypeRow(i);
            if (typeRow.isEnd()) break;
            if (typeRow.enump()) self()->declareEnum(rtmdp->dataType(i));
        }
    }
    // At least one model must be Verilated for tracing (though technically could still trace
    // whatever is available via the RTMD at this point, if present). If at least one model
    // requests parallel tracing, then use it, if the format can.
    if (!anyTraced) {
        VL_FATAL_MT("", 0, "",
                    "Testbench C call to 'VerilatedContext::trace()' requires model(s) "
                    "Verilated with a '--trace-*' option");
    }

    // Declare the hierarchy of all models, see the VlRtmdHierListener methods in verilated_trace.h
    walkContext(*m_contextp);
    m_codes.clear();

    // If reopen, check that the number of codes is the same as the previous dump
    if (expectedCodes && m_nextCode != expectedCodes) {
        VL_FATAL_MT(__FILE__, __LINE__, "",
                    "Reopening trace file with different number of signals");
    }

    // Keep the groups in the order of their activity sets, then how they are dumped
    for (auto& actSetPair : m_groupMap) {
        for (auto& storagePair : actSetPair.second) {
            Group& group = storagePair.second;
            group.m_storage = storagePair.first.first;
            group.m_valueStorage = storagePair.first.second;
            m_groupVec.emplace_back(actSetPair.first, std::move(group));
        }
    }
    m_groupMap.clear();

    // Dump the values of a group in address order, for better locality
    for (auto& group : m_groupVec) {
        std::vector<Whole>& wholes = group.second.m_wholes;
        std::sort(wholes.begin(), wholes.end(), [](const Whole& a, const Whole& b) {  //
            return a.m_datap < b.m_datap;
        });
        std::vector<Slice>& slices = group.second.m_slices;
        std::sort(slices.begin(), slices.end(), [](const Slice& a, const Slice& b) {
            if (a.m_datap != b.m_datap) return a.m_datap < b.m_datap;
            return a.m_lsb < b.m_lsb;
        });
    }

    // Dump in parallel using each thread of the context, one shard each
    const uint32_t nShards
        = anyParallel && parallelCapable()
              ? static_cast<uint32_t>(
                    static_cast<VlThreadPool*>(m_contextp->threadPoolp())->numThreads())
                    + 1
              : 1;

    // Split the groups into contiguous shards of about the same number of codes, splitting
    // groups at shard boundaries. Committing the shards in order gives the same output as
    // dumping serially. Codes start from 1.
    const uint32_t maxCodes = std::max((m_nextCode - 1 + nShards - 1) / nShards, 1U);
    // Codes of the value 'i' of a group, the whole values first, then the slices
    const auto valueCodes = [](const Group& group, size_t i) -> uint32_t {
        const size_t nWholes = group.m_wholes.size();
        return VL_WORDS_I(i < nWholes ? group.m_wholes[i].m_bits
                                      : group.m_slices[i - nWholes].m_bits);
    };
    std::vector<std::pair<VlRtmdActSet, Group>> groupVec;
    m_shards.clear();
    m_shards.emplace_back();
    uint32_t shardCodes = 0;  // Codes in the last shard
    for (std::pair<VlRtmdActSet, Group>& pair : m_groupVec) {
        Group& group = pair.second;
        while (true) {
            // The number of values of the group that fit in the last shard, which holds at
            // least one value, or all of them if no more shards can be added
            const size_t nValues = group.m_wholes.size() + group.m_slices.size();
            size_t n = 0;
            if (m_shards.size() == nShards) {
                n = nValues;
            } else {
                for (; n < nValues; ++n) {
                    const uint32_t codes = valueCodes(group, n);
                    if (shardCodes && shardCodes + codes > maxCodes) break;
                    shardCodes += codes;
                }
            }
            // All fit, continue with the next group
            if (n == nValues) {
                groupVec.emplace_back(pair.first, std::move(group));
                break;
            }
            // Move the values that fit to a group of their own, in the last shard
            if (n) {
                const size_t nWholes = std::min(n, group.m_wholes.size());
                const auto wholesEnd = group.m_wholes.begin() + nWholes;
                const auto slicesEnd = group.m_slices.begin() + (n - nWholes);
                Group first{group.m_storage, group.m_valueStorage, {}, {}};
                first.m_wholes.assign(group.m_wholes.begin(), wholesEnd);
                first.m_slices.assign(group.m_slices.begin(), slicesEnd);
                groupVec.emplace_back(pair.first, std::move(first));
                group.m_wholes.erase(group.m_wholes.begin(), wholesEnd);
                group.m_slices.erase(group.m_slices.begin(), slicesEnd);
            }
            // Start the next shard
            m_shards.back().m_end = groupVec.size();
            m_shards.emplace_back();
            m_shards.back().m_begin = groupVec.size();
            shardCodes = 0;
        }
    }
    m_shards.back().m_end = groupVec.size();
    m_groupVec = std::move(groupVec);

    // Room in each shard for extracting a wide slice, no wider than the widest signal
    for (Shard& shard : m_shards) shard.m_wideSlice.resize(VL_WORDS_I(m_maxBits));

    // Now that we know the number of codes, allocate space for the buffer holding
    // previous signal values.
    if (!m_sigs_oldvalp) m_sigs_oldvalp = new uint32_t[m_nextCode];

    // Set callback so flush/abort will flush this file
    Verilated::addFlushCb(onFlush, this);
    Verilated::addExitCb(onExit, this);
}

//=========================================================================
// Internals available to format-specific implementations

template <>
std::string VerilatedTrace<VL_SUB_T, VL_BUF_T>::timeResStr() const {
    return vl_timescaled_double(m_timeRes);
}

//=========================================================================
// External interface to client code

template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::set_time_unit(const char*) VL_MT_SAFE {}
template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::set_time_unit(const std::string&) VL_MT_SAFE {}
template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::set_time_resolution(const char* unitp) VL_MT_SAFE {
    m_timeRes = timescaleToDouble(unitp);
}
template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::set_time_resolution(const std::string& unit) VL_MT_SAFE {
    set_time_resolution(unit.c_str());
}
template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::dumpvars(int level, const std::string& hier) VL_MT_SAFE {
    if (level == 0) {
        m_dumpvars.clear();  // empty = everything on
    } else {
        m_dumpvars.emplace_back(level, hier);
    }
}

//=========================================================================
// Primitives converting binary values to strings...

// All of these take a destination pointer where the string will be emitted,
// and a value to convert. There are a couple of variants for efficiency.

inline void cvtCDataToStr(char* dstp, CData value) {
#ifdef VL_HAVE_SSE2
    // Similar to cvtSDataToStr but only the bottom 8 byte lanes are used
    const __m128i a = _mm_cvtsi32_si128(value);
    const __m128i b = _mm_unpacklo_epi8(a, a);
    const __m128i c = _mm_shufflelo_epi16(b, 0);
    const __m128i m = _mm_set1_epi64x(0x0102040810204080);
    const __m128i d = _mm_cmpeq_epi8(_mm_and_si128(c, m), m);
    const __m128i result = _mm_sub_epi8(_mm_set1_epi8('0'), d);
    _mm_storel_epi64(reinterpret_cast<__m128i*>(dstp), result);
#else
    dstp[0] = '0' | static_cast<char>((value >> 7) & 1);
    dstp[1] = '0' | static_cast<char>((value >> 6) & 1);
    dstp[2] = '0' | static_cast<char>((value >> 5) & 1);
    dstp[3] = '0' | static_cast<char>((value >> 4) & 1);
    dstp[4] = '0' | static_cast<char>((value >> 3) & 1);
    dstp[5] = '0' | static_cast<char>((value >> 2) & 1);
    dstp[6] = '0' | static_cast<char>((value >> 1) & 1);
    dstp[7] = '0' | static_cast<char>(value & 1);
#endif
}

inline void cvtSDataToStr(char* dstp, SData value) {
#ifdef VL_HAVE_SSE2
    // We want each bit in the 16-bit input value to end up in a byte lane
    // within the 128-bit XMM register. Note that x86 is little-endian and we
    // want the MSB of the input at the low address, so we will bit-reverse
    // at the same time.

    // Put value in bottom of 128-bit register a[15:0] = value
    const __m128i a = _mm_cvtsi32_si128(value);
    // Interleave bytes with themselves
    // b[15: 0] = {2{a[ 7:0]}} == {2{value[ 7:0]}}
    // b[31:16] = {2{a[15:8]}} == {2{value[15:8]}}
    const __m128i b = _mm_unpacklo_epi8(a, a);
    // Shuffle bottom 64 bits, note swapping high bytes with low bytes
    // c[31: 0] = {2{b[31:16]}} == {4{value[15:8}}
    // c[63:32] = {2{b[15: 0]}} == {4{value[ 7:0}}
    const __m128i c = _mm_shufflelo_epi16(b, 0x05);
    // Shuffle whole register
    // d[ 63: 0] = {2{c[31: 0]}} == {8{value[15:8}}
    // d[126:54] = {2{c[63:32]}} == {8{value[ 7:0}}
    const __m128i d = _mm_shuffle_epi32(c, 0x50);
    // Test each bit within the bytes, this sets each byte lane to 0
    // if the bit for that lane is 0 and to 0xff if the bit is 1.
    const __m128i m = _mm_set1_epi64x(0x0102040810204080);
    const __m128i e = _mm_cmpeq_epi8(_mm_and_si128(d, m), m);
    // Convert to ASCII by subtracting the masks from ASCII '0':
    // '0' - 0 is '0', '0' - -1 is '1'
    const __m128i result = _mm_sub_epi8(_mm_set1_epi8('0'), e);
    // Store the 16 characters to the un-aligned buffer
    _mm_storeu_si128(reinterpret_cast<__m128i*>(dstp), result);
#else
    cvtCDataToStr(dstp, value >> 8);
    cvtCDataToStr(dstp + 8, value);
#endif
}

inline void cvtIDataToStr(char* dstp, IData value) {
#ifdef VL_HAVE_AVX2
    // Similar to cvtSDataToStr but the bottom 16-bits are processed in the
    // top half of the YMM registers
    const __m256i a = _mm256_insert_epi32(_mm256_undefined_si256(), value, 0);
    const __m256i b = _mm256_permute4x64_epi64(a, 0);
    const __m256i s = _mm256_set_epi8(0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2,
                                      2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3);
    const __m256i c = _mm256_shuffle_epi8(b, s);
    const __m256i m = _mm256_set1_epi64x(0x0102040810204080);
    const __m256i d = _mm256_cmpeq_epi8(_mm256_and_si256(c, m), m);
    const __m256i result = _mm256_sub_epi8(_mm256_set1_epi8('0'), d);
    _mm256_storeu_si256(reinterpret_cast<__m256i*>(dstp), result);
#else
    cvtSDataToStr(dstp, value >> 16);
    cvtSDataToStr(dstp + 16, value);
#endif
}

inline void cvtQDataToStr(char* dstp, QData value) {
    cvtIDataToStr(dstp, value >> 32);
    cvtIDataToStr(dstp + 32, value);
}

#define cvtEDataToStr cvtIDataToStr

//=========================================================================
// VerilatedTraceBuffer

template <>
VerilatedTraceBuffer<VL_BUF_T>::VerilatedTraceBuffer(Trace& owner)
    : VL_BUF_T{owner}
    , m_sigs_oldvalp{owner.m_sigs_oldvalp} {}

// These functions must write the new value back into the old value store,
// and subsequently call the format-specific emit* implementations. Note
// that this file must be included in the format-specific implementation, so
// the emit* functions can be inlined for performance.

template <>
void VerilatedTraceBuffer<VL_BUF_T>::fullBit(uint32_t code, CData newval) {
    m_sigs_oldvalp[code] = newval;  // Still copy even if not tracing so chg doesn't call full
    emitBit(code, newval);
}

template <>
void VerilatedTraceBuffer<VL_BUF_T>::fullEvent(uint32_t code, const VlEventBase* newvalp) {
    // No need to update the previous value
    if (newvalp->isTriggered()) emitEvent(code);
}

template <>
void VerilatedTraceBuffer<VL_BUF_T>::fullCData(uint32_t code, CData newval, int bits) {
    m_sigs_oldvalp[code] = newval;  // Still copy even if not tracing so chg doesn't call full
    emitCData(code, newval, bits);
}

template <>
void VerilatedTraceBuffer<VL_BUF_T>::fullSData(uint32_t code, SData newval, int bits) {
    m_sigs_oldvalp[code] = newval;  // Still copy even if not tracing so chg doesn't call full
    emitSData(code, newval, bits);
}

template <>
void VerilatedTraceBuffer<VL_BUF_T>::fullIData(uint32_t code, IData newval, int bits) {
    m_sigs_oldvalp[code] = newval;  // Still copy even if not tracing so chg doesn't call full
    emitIData(code, newval, bits);
}

template <>
void VerilatedTraceBuffer<VL_BUF_T>::fullQData(uint32_t code, QData newval, int bits) {
    std::memcpy(m_sigs_oldvalp + code, &newval, sizeof(newval));
    emitQData(code, newval, bits);
}

template <>
void VerilatedTraceBuffer<VL_BUF_T>::fullWData(uint32_t code, WDataInP newval, int bits) {
    uint32_t* const oldp = m_sigs_oldvalp + code;
    for (int i = 0; i < VL_WORDS_I(bits); ++i) oldp[i] = newval[i];
    emitWData(code, newval, bits);
}

template <>
void VerilatedTraceBuffer<VL_BUF_T>::fullDouble(uint32_t code, double newval) {
    std::memcpy(m_sigs_oldvalp + code, &newval, sizeof(newval));
    // cppcheck-suppress invalidPointerCast
    emitDouble(code, newval);
}

//=========================================================================
// Dumping

template <>
template <bool T_Full, VlRtmdDataType::StorageKind T_Storage>
VL_ATTR_ALWINLINE void VerilatedTrace<VL_SUB_T, VL_BUF_T>::dumpValue(Buffer* bufp, uint32_t code,
                                                                     const void* datap,
                                                                     int bits) VL_MT_UNSAFE {
    switch (T_Storage) {
    case StorageKind::CDATA: {
        const CData val = *static_cast<const CData*>(datap);
        // Single bits are dumped as scalars
        if (bits == 1) {
            if VL_CONSTEXPR_CXX17 (T_Full) {
                bufp->fullBit(code, val);
            } else {
                bufp->chgBit(code, val);
            }
        } else {
            if VL_CONSTEXPR_CXX17 (T_Full) {
                bufp->fullCData(code, val, bits);
            } else {
                bufp->chgCData(code, val, bits);
            }
        }
        break;
    }
    case StorageKind::SDATA: {
        SData val;
        std::memcpy(&val, datap, sizeof(val));  // Might be unaligned, see addSignal
        if VL_CONSTEXPR_CXX17 (T_Full) {
            bufp->fullSData(code, val, bits);
        } else {
            bufp->chgSData(code, val, bits);
        }
        break;
    }
    case StorageKind::IDATA: {
        IData val;
        std::memcpy(&val, datap, sizeof(val));  // Might be unaligned, see addSignal
        if VL_CONSTEXPR_CXX17 (T_Full) {
            bufp->fullIData(code, val, bits);
        } else {
            bufp->chgIData(code, val, bits);
        }
        break;
    }
    case StorageKind::QDATA: {
        QData val;
        std::memcpy(&val, datap, sizeof(val));  // Might be unaligned, see addSignal
        if VL_CONSTEXPR_CXX17 (T_Full) {
            bufp->fullQData(code, val, bits);
        } else {
            bufp->chgQData(code, val, bits);
        }
        break;
    }
    case StorageKind::WDATA: {
        const WDataInP valp = WDataInP::external(static_cast<const EData*>(datap));
        if VL_CONSTEXPR_CXX17 (T_Full) {
            bufp->fullWData(code, valp, bits);
        } else {
            bufp->chgWData(code, valp, bits);
        }
        break;
    }
    case StorageKind::DOUBLE: {
        const double val = *static_cast<const double*>(datap);
        if VL_CONSTEXPR_CXX17 (T_Full) {
            bufp->fullDouble(code, val);
        } else {
            bufp->chgDouble(code, val);
        }
        break;
    }
    case StorageKind::EVENT: {
        const VlEventBase* const valp = static_cast<const VlEventBase*>(datap);
        if VL_CONSTEXPR_CXX17 (T_Full) {
            bufp->fullEvent(code, valp);
        } else {
            bufp->chgEvent(code, valp);
        }
        break;
    }
    }
}

template <>
template <bool T_Full, VlRtmdDataType::StorageKind T_Storage, VlRtmdDataType::StorageKind T_Value>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::dumpSlices(Buffer* bufp, const Group& group,
                                                    EData* wideSlicep) VL_MT_UNSAFE {
    // Only the packed value is read: whole by its own type if it fits in a quadword, otherwise
    // the words holding the slice. A narrow slice is extracted into a quadword, which is read
    // back as a value of its width, so the low bytes, as the host is little endian.
    for (const Slice& slice : group.m_slices) {
        const int bits = static_cast<int>(slice.m_bits);
        if VL_CONSTEXPR_CXX17 (T_Storage == StorageKind::WDATA) {
            // A wide slice is of a wide value
            const WDataInP valuep = WDataInP::external(static_cast<const EData*>(slice.m_datap));
            VL_SEL_WWII(bits, static_cast<int>(slice.m_valueBits), WDataOutP::external(wideSlicep),
                        valuep, slice.m_lsb, slice.m_bits);
            // Clear the bits above the slice
            if (VL_BITBIT_E(bits)) wideSlicep[VL_WORDS_I(bits) - 1] &= VL_MASK_E(bits);
            dumpValue<T_Full, T_Storage>(bufp, slice.m_code, wideSlicep, bits);
        } else {
            QData value;
            if VL_CONSTEXPR_CXX17 (T_Value == StorageKind::CDATA) {
                value = *static_cast<const CData*>(slice.m_datap) >> slice.m_lsb;
            } else if VL_CONSTEXPR_CXX17 (T_Value == StorageKind::SDATA) {
                value = *static_cast<const SData*>(slice.m_datap) >> slice.m_lsb;
            } else if VL_CONSTEXPR_CXX17 (T_Value == StorageKind::IDATA) {
                value = *static_cast<const IData*>(slice.m_datap) >> slice.m_lsb;
            } else if VL_CONSTEXPR_CXX17 (T_Value == StorageKind::QDATA) {
                value = *static_cast<const QData*>(slice.m_datap) >> slice.m_lsb;
            } else {
                const WDataInP valuep
                    = WDataInP::external(static_cast<const EData*>(slice.m_datap));
                value = VL_SEL_QWII(static_cast<int>(slice.m_valueBits), valuep, slice.m_lsb,
                                    slice.m_bits);
            }
            value &= VL_MASK_Q(bits);
            dumpValue<T_Full, T_Storage>(bufp, slice.m_code, &value, bits);
        }
    }
}

template <>
template <bool T_Full, VlRtmdDataType::StorageKind T_Storage>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::dumpGroupSlices(Buffer* bufp, const Group& group,
                                                         EData* wideSlicep) VL_MT_UNSAFE {
    // Dispatch on how the packed values are stored once for the whole group
    switch (group.m_valueStorage) {
    case StorageKind::CDATA:
        dumpSlices<T_Full, T_Storage, wider(T_Storage, StorageKind::CDATA)>(bufp, group,
                                                                            wideSlicep);
        break;
    case StorageKind::SDATA:
        dumpSlices<T_Full, T_Storage, wider(T_Storage, StorageKind::SDATA)>(bufp, group,
                                                                            wideSlicep);
        break;
    case StorageKind::IDATA:
        dumpSlices<T_Full, T_Storage, wider(T_Storage, StorageKind::IDATA)>(bufp, group,
                                                                            wideSlicep);
        break;
    case StorageKind::QDATA:
        dumpSlices<T_Full, T_Storage, wider(T_Storage, StorageKind::QDATA)>(bufp, group,
                                                                            wideSlicep);
        break;
    case StorageKind::WDATA:
        dumpSlices<T_Full, T_Storage, StorageKind::WDATA>(bufp, group, wideSlicep);
        break;
    case StorageKind::DOUBLE:
    case StorageKind::EVENT: break;  // LCOV_EXCL_LINE
    }
}

template <>
template <bool T_Full, VlRtmdDataType::StorageKind T_Storage>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::dumpGroupWholes(Buffer* bufp,
                                                         const Group& group) VL_MT_UNSAFE {
    for (const Whole& whole : group.m_wholes) {
        dumpValue<T_Full, T_Storage>(bufp, whole.m_code, whole.m_datap,
                                     static_cast<int>(whole.m_bits));
    }
}

template <>
template <bool T_Full>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::dumpGroupDispatch(Buffer* bufp, const Group& group,
                                                           EData* wideSlicep) VL_MT_UNSAFE {
    // Dispatch on how the values are stored once for the whole group. Events and reals have no
    // slices.
    switch (group.m_storage) {
    case StorageKind::CDATA:
        dumpGroupWholes<T_Full, StorageKind::CDATA>(bufp, group);
        dumpGroupSlices<T_Full, StorageKind::CDATA>(bufp, group, wideSlicep);
        break;
    case StorageKind::SDATA:
        dumpGroupWholes<T_Full, StorageKind::SDATA>(bufp, group);
        dumpGroupSlices<T_Full, StorageKind::SDATA>(bufp, group, wideSlicep);
        break;
    case StorageKind::IDATA:
        dumpGroupWholes<T_Full, StorageKind::IDATA>(bufp, group);
        dumpGroupSlices<T_Full, StorageKind::IDATA>(bufp, group, wideSlicep);
        break;
    case StorageKind::QDATA:
        dumpGroupWholes<T_Full, StorageKind::QDATA>(bufp, group);
        dumpGroupSlices<T_Full, StorageKind::QDATA>(bufp, group, wideSlicep);
        break;
    case StorageKind::WDATA:
        dumpGroupWholes<T_Full, StorageKind::WDATA>(bufp, group);
        dumpGroupSlices<T_Full, StorageKind::WDATA>(bufp, group, wideSlicep);
        break;
    case StorageKind::DOUBLE: dumpGroupWholes<T_Full, StorageKind::DOUBLE>(bufp, group); break;
    case StorageKind::EVENT: dumpGroupWholes<T_Full, StorageKind::EVENT>(bufp, group); break;
    }
}

template <>
template <bool T_Full>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::dumpShard(Buffer* bufp, Shard& shard) VL_MT_UNSAFE {
    EData* const wideSlicep = shard.m_wideSlice.data();
    if VL_CONSTEXPR_CXX17 (T_Full) {
        // Dump all values
        for (size_t i = shard.m_begin; i < shard.m_end; ++i) {
            dumpGroupDispatch<true>(bufp, m_groupVec[i].second, wideSlicep);
        }
        return;
    }
    // Dump the changed values, skipping those that have not changed since the last dump.
    // The groups of an activity set are adjacent, so check each set only once.
    const VlRtmdActSet* lastActSetp = nullptr;
    bool active = false;
    for (size_t i = shard.m_begin; i < shard.m_end; ++i) {
        const VlRtmdActSet& actSet = m_groupVec[i].first;
        if (!lastActSetp || !(actSet == *lastActSetp)) {
            lastActSetp = &actSet;
            active = actSet.active();
        }
        if (!active) continue;
        dumpGroupDispatch<false>(bufp, m_groupVec[i].second, wideSlicep);
    }
}

template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::parallelWorkerTask(void* datap) {
    ParallelWorkerData* const wdp = reinterpret_cast<ParallelWorkerData*>(datap);
    // Dump the shard
    if (wdp->m_full) {
        wdp->m_trace.dumpShard<true>(wdp->m_bufp, wdp->m_shard);
    } else {
        wdp->m_trace.dumpShard<false>(wdp->m_bufp, wdp->m_shard);
    }
    // Mark buffer as ready
    const VerilatedLockGuard lock{wdp->m_mutex};
    wdp->m_ready.store(true);
    if (wdp->m_waiting) wdp->m_cv.notify_one();
}

template <>
VL_ATTR_NOINLINE void VerilatedTrace<VL_SUB_T, VL_BUF_T>::ParallelWorkerData::wait() {
    // Spin for a while, waiting for the buffer to become ready
    for (int i = 0; i < VL_LOCK_SPINS; ++i) {
        if (VL_LIKELY(m_ready.load(std::memory_order_relaxed))) return;
        VL_CPU_RELAX();
    }
    // We have been spinning for a while, so yield the thread
    VerilatedLockGuard lock{m_mutex};
    m_waiting = true;
    m_cv.wait(m_mutex, [this] { return m_ready.load(std::memory_order_relaxed); });
    m_waiting = false;
}

template <>
void VerilatedTrace<VL_SUB_T, VL_BUF_T>::dump(uint64_t timeui) VL_MT_SAFE_EXCLUDES(m_mutex) {
    // Not really VL_MT_SAFE but more VL_MT_UNSAFE_ONE.
    // This does get the mutex, but if multiple threads are trying to dump
    // chances are the data being dumped will have other problems
    const VerilatedLockGuard lock{m_mutex};
    if (VL_UNCOVERABLE(m_didSomeDump && timeui <= m_timeLastDump)) {  // LCOV_EXCL_START
        VL_PRINTF_MT("%%Warning: previous dump at t=%" PRIu64 ", requesting t=%" PRIu64
                     ", dump call ignored\n",
                     m_timeLastDump, timeui);
        return;
    }  // LCOV_EXCL_STOP
    m_timeLastDump = timeui;
    m_didSomeDump = true;

    Verilated::quiesce();

    // Call hook for format-specific behaviour
    if (VL_UNLIKELY(m_fullDump)) {
        if (!preFullDump()) return;
    } else {
        if (!preChangeDump()) return;
    }

    // Update time point
    emitTimeChange(timeui);

    // Dump the described models
    const bool full = m_fullDump;
    m_fullDump = false;
    if (!parallel()) {
        Buffer* const bufp = getTraceBuffer();
        if (VL_UNLIKELY(full)) {
            dumpShard<true>(bufp, m_shards.front());
        } else {
            dumpShard<false>(bufp, m_shards.front());
        }
        commitTraceBuffer(bufp);
    } else {
        // Dump each shard on its own thread, the first on this one
        VlThreadPool* const threadPoolp = static_cast<VlThreadPool*>(m_contextp->threadPoolp());
        // List of work items for threads (std::list, as ParallelWorkerData is not movable)
        std::list<ParallelWorkerData> workerData;
        for (size_t i = 0; i < m_shards.size(); ++i) {
            // Always get the trace buffer on the main thread
            workerData.emplace_back(*this, m_shards[i], getTraceBuffer(), full);
            if (i) {
                threadPoolp->workerp(static_cast<int>(i - 1))
                    ->addTask(parallelWorkerTask, &workerData.back());
            }
        }
        parallelWorkerTask(&workerData.front());
        // Commit all trace buffers in order
        for (ParallelWorkerData& item : workerData) {
            // Wait until ready
            item.wait();
            // Commit the buffer
            commitTraceBuffer(item.m_bufp);
        }
    }

    // The models clear their activity flags at their next evaluation
    for (VerilatedModel* const modelp : m_modelps) modelp->m_didDump = true;
}

#endif  // VL_CPPCHECK
