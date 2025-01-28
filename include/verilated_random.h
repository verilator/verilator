// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Code available from: https://verilator.org
//
// Copyright 2024 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU Lesser
// General Public License Version 3 or the Perl Artistic License Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
///
/// \file
/// \brief Verilated randomization header
///
/// This file is included automatically by Verilator in some of the C++ files
/// it generates if randomization features are used.
///
/// This file is not part of the Verilated public-facing API.
/// It is only for internal use.
///
/// See the internals documentation docs/internals.rst for details.
///
//*************************************************************************
#ifndef VERILATOR_VERILATED_RANDOM_H_
#define VERILATOR_VERILATED_RANDOM_H_

#include "verilated.h"

#include <iomanip>
#include <iostream>
#include <ostream>
#include <sstream>

//=============================================================================
// VlRandomExpr and subclasses represent expressions for the constraint solver.
class ArrayInfo final {
public:
    const std::string
        m_name;  // Name of the array variable, including index notation (e.g., arr[2][1])
    void* const m_datap;  // Reference to the array variable data
    const int m_index;  // Flattened (1D) index of the array element
    const std::vector<IData> m_indices;  // Multi-dimensional indices of the array element
    const std::vector<size_t> m_idxWidths;  // Multi-dimensional indices' bit widths

    ArrayInfo(const std::string& name, void* datap, int index, const std::vector<IData>& indices,
              const std::vector<size_t>& idxWidths)
        : m_name(name)
        , m_datap(datap)
        , m_index(index)
        , m_indices(indices)
        , m_idxWidths(idxWidths) {}
};
using ArrayInfoMap = std::map<std::string, std::shared_ptr<const ArrayInfo>>;

class VlRandomVar VL_NOT_FINAL {
    const char* m_name;  // Variable name
    void* const m_datap;  // Reference to variable data
    const int m_width;  // Variable width in bits
    const int m_dimension;  //Variable dimension, default is 0
    const std::uint32_t m_randModeIdx;  // rand_mode index

public:
    VlRandomVar(const char* name, int width, void* datap, int dimension, std::uint32_t randModeIdx)
        : m_name{name}
        , m_datap{datap}
        , m_width{width}
        , m_dimension{dimension}
        , m_randModeIdx{randModeIdx} {
        m_name = new char[std::strlen(name) + 1];
        std::strcpy(const_cast<char*>(m_name), name);
    }
    virtual ~VlRandomVar() { delete[] m_name; }
    const char* name() const { return m_name; }
    int width() const { return m_width; }
    int dimension() const { return m_dimension; }
    virtual void* datap(int idx) const { return m_datap; }
    std::uint32_t randModeIdx() const { return m_randModeIdx; }
    bool randModeIdxNone() const { return randModeIdx() == std::numeric_limits<unsigned>::max(); }
    bool set(const std::string& idx, const std::string& val) const;
    virtual void emitGetValue(std::ostream& s) const;
    virtual void emitExtract(std::ostream& s, int i) const;
    virtual void emitType(std::ostream& s) const;
    virtual int totalWidth() const;
    mutable std::shared_ptr<const ArrayInfoMap> m_arrVarsRefp;
    void setArrayInfo(const std::shared_ptr<const ArrayInfoMap>& arrVarsRefp) const {
        m_arrVarsRefp = arrVarsRefp;
    }
    mutable std::map<std::string, int> count_cache;
    int countMatchingElements(const ArrayInfoMap& arr_vars, const std::string& base_name) const {
        if (VL_LIKELY(count_cache.find(base_name) != count_cache.end()))
            return count_cache[base_name];
        int count = 0;
        for (int index = 0; arr_vars.find(base_name + std::to_string(index)) != arr_vars.end();
             ++index) {
            ++count;
        }
        count_cache[base_name] = count;
        return count;
    }
};
template <typename T>
class VlRandomArrayVarTemplate final : public VlRandomVar {
public:
    VlRandomArrayVarTemplate(const char* name, int width, void* datap, int dimension,
                             std::uint32_t randModeIdx)
        : VlRandomVar{name, width, datap, dimension, randModeIdx} {}
    void* datap(int idx) const override {
        const std::string indexed_name = name() + std::to_string(idx);
        const auto it = m_arrVarsRefp->find(indexed_name);
        if (it != m_arrVarsRefp->end()) {
            return it->second->m_datap;
        } else {
            VL_FATAL_MT(__FILE__, __LINE__, "randomize", "indexed_name not found in m_arr_vars");
            return nullptr;
        }
    }
    void emitHexs(std::ostream& s, const std::vector<IData>& indices, const size_t bit_width,
                  size_t idx) const {
        for (int j = bit_width - 4; j >= 0; j -= 4) {
            s << "0123456789abcdef"[(indices[idx] >> j) & 0xf];
        }
    }
    void emitSelect(std::ostream& s, const std::vector<IData>& indices,
                    const std::vector<size_t>& idxWidths) const {
        const size_t num_indices = idxWidths.size();
        size_t wide_size = 0;

        for (size_t idx = 0; idx < num_indices; ++idx) s << "(select ";
        s << name();

        for (size_t idx = 0; idx < num_indices; ++idx) {
            const size_t bit_width = idxWidths[idx];
            s << " #x";

            const size_t emit_count = (bit_width > 32) ? (idxWidths[idx] / 32) : 1;

            for (size_t i = 0; i < emit_count; ++i) {
                emitHexs(s, indices, (bit_width > 32) ? 32 : bit_width, wide_size + i);
            }

            wide_size += (idxWidths[idx] > 32) ? (idxWidths[idx] / 32) : 1;
            s << ")";
        }
    }
    void emitGetValue(std::ostream& s) const override {
        const int elementCounts = countMatchingElements(*m_arrVarsRefp, name());
        for (int i = 0; i < elementCounts; i++) {
            const std::string indexed_name = name() + std::to_string(i);
            const auto it = m_arrVarsRefp->find(indexed_name);
            if (it != m_arrVarsRefp->end()) {
                const std::vector<IData>& indices = it->second->m_indices;
                const std::vector<size_t>& idxWidths = it->second->m_idxWidths;
                emitSelect(s, indices, idxWidths);
            } else {
                VL_FATAL_MT(__FILE__, __LINE__, "randomize",
                            "indexed_name not found in m_arr_vars");
            }
        }
    }
    void emitType(std::ostream& s) const override {
        const std::string indexed_name = name() + std::to_string(0);
        const auto it = m_arrVarsRefp->find(indexed_name);
        if (it != m_arrVarsRefp->end()) {
            const std::vector<size_t>& idxWidths = it->second->m_idxWidths;
            if (dimension() > 0) {
                for (int i = 0; i < dimension(); ++i) {
                    s << "(Array (_ BitVec " << idxWidths[i] << ") ";
                }
                s << "(_ BitVec " << width() << ")";
                for (int i = 0; i < dimension(); ++i) { s << ")"; }
            }
        } else {
            VL_FATAL_MT(__FILE__, __LINE__, "randomize", "indexed_name not found in m_arr_vars");
        }
    }
    int totalWidth() const override {
        const int elementCounts = countMatchingElements(*m_arrVarsRefp, name());
        return width() * elementCounts;
    }
    void emitExtract(std::ostream& s, int i) const override {
        const int j = i / width();
        i = i % width();
        s << " ((_ extract " << i << ' ' << i << ')';
        const std::string indexed_name = name() + std::to_string(j);
        const auto it = m_arrVarsRefp->find(indexed_name);
        if (it != m_arrVarsRefp->end()) {
            const std::vector<IData>& indices = it->second->m_indices;
            const std::vector<size_t>& idxWidths = it->second->m_idxWidths;
            emitSelect(s, indices, idxWidths);
        } else {
            VL_FATAL_MT(__FILE__, __LINE__, "randomize", "indexed_name not found in m_arr_vars");
        }
        s << ')';
    }
};
//=============================================================================
// VlRandomizer is the object holding constraints and variable references.
class VlRandomizer final {
    // MEMBERS
    std::vector<std::string> m_constraints;  // Solver-dependent constraints
    std::map<std::string, std::shared_ptr<const VlRandomVar>> m_vars;  // Solver-dependent
                                                                       // variables
    ArrayInfoMap m_arr_vars;  // Tracks each element in array structures for iteration
    std::map<size_t, std::string> seen_values;  // Record String Index to avoid conflicts
    const VlQueue<CData>* m_randmode;  // rand_mode state;

    // PRIVATE METHODS
    void randomConstraint(std::ostream& os, VlRNG& rngr, int bits);
    bool parseSolution(std::iostream& file);

public:
    // CONSTRUCTORS
    VlRandomizer() = default;
    ~VlRandomizer() = default;

    // METHODS
    // Finds the next solution satisfying the constraints
    bool next(VlRNG& rngr);

    template <typename T_Key>
    typename std::enable_if<std::is_integral<T_Key>::value && (sizeof(T_Key) <= 4)>::type
    process_key(const T_Key& key, std::string& indexed_name, std::vector<size_t>& integral_index,
                const std::string& base_name, size_t& idx_width) {
        integral_index.push_back(static_cast<size_t>(key));
        indexed_name
            = base_name + "[" + std::to_string(integral_index[integral_index.size() - 1]) + "]";
        idx_width = sizeof(T_Key) * 8;
    }
    template <typename T_Key>
    typename std::enable_if<std::is_integral<T_Key>::value && (sizeof(T_Key) > 4)>::type
    process_key(const T_Key& key, std::string& indexed_name, std::vector<size_t>& integral_index,
                const std::string& base_name, size_t& idx_width) {
        constexpr size_t segment_bits = 32;
        constexpr T_Key mask = (static_cast<T_Key>(1) << segment_bits) - 1;
        integral_index.push_back(static_cast<size_t>(key >> segment_bits));
        integral_index.push_back(static_cast<size_t>(key & mask));

        std::ostringstream hex_stream;
        hex_stream << std::hex << key;
        std::string index_string = hex_stream.str();
        index_string.erase(0, index_string.find_first_not_of('0'));
        index_string = index_string.empty() ? "0" : index_string;

        indexed_name = base_name + "[" + index_string + "]";

        idx_width = sizeof(T_Key) * 8;
    }
    template <typename T_Key>
    typename std::enable_if<VlIsVlWide<T_Key>::value>::type
    process_key(const T_Key& key, std::string& indexed_name, std::vector<size_t>& integral_index,
                const std::string& base_name, size_t& idx_width) {
        std::ostringstream hex_stream;
        for (size_t i = key.size(); i > 0; --i) {
            const size_t segment_value = key.at(i - 1);
            hex_stream << std::hex << segment_value;
            integral_index.push_back(segment_value);
        }
        std::string index_string = hex_stream.str();
        index_string.erase(0, index_string.find_first_not_of('0'));
        index_string = index_string.empty() ? "0" : index_string;

        indexed_name = base_name + "[" + index_string + "]";
        idx_width = key.size() * 32;
    }
    template <typename T_Key>
    typename std::enable_if<std::is_same<T_Key, std::string>::value>::type
    process_key(const T_Key& key, std::string& indexed_name, std::vector<size_t>& integral_index,
                const std::string& base_name, size_t& idx_width) {
        // Convert the input string to its ASCII hexadecimal representation
        std::ostringstream oss;
        for (unsigned char c : key) {
            oss << std::hex << std::setw(2) << std::setfill('0') << static_cast<int>(c);
        }
        std::string hex_str = oss.str();
        // Ensure the hex string is exactly 128 bits (32 hex characters)
        hex_str = hex_str.size() > 32 ? hex_str.substr(0, 32)
                                      : std::string(32 - hex_str.size(), '0') + hex_str;

        // Split the hex string into 4 segments (32-bit per segment)
        integral_index.clear();
        for (size_t i = 0; i < hex_str.size(); i += 8) {
            integral_index.push_back(std::stoul(hex_str.substr(i, 8), nullptr, 16));
        }

        indexed_name = base_name + "["
                       + (hex_str.find_first_not_of('0') == std::string::npos
                              ? "0"
                              : hex_str.substr(hex_str.find_first_not_of('0')))
                       + "]";

        idx_width = 128;
    }
    template <typename T_Key>
    typename std::enable_if<!std::is_integral<T_Key>::value
                            && !std::is_same<T_Key, std::string>::value
                            && !VlIsVlWide<T_Key>::value>::type
    process_key(const T_Key& key, std::string& indexed_name, std::vector<size_t>& integral_index,
                const std::string& base_name, size_t& idx_width) {
        VL_FATAL_MT(__FILE__, __LINE__, "randomize",
                    "Unsupported: Only integral and string index of associative array is "
                    "supported currently.");
    }

    template <typename T>
    typename std::enable_if<!VlIsCustomStruct<T>::value, void>::type
    write_var(T& var, int width, const char* name, int dimension,
              std::uint32_t randmodeIdx = std::numeric_limits<std::uint32_t>::max()) {
        if (m_vars.find(name) != m_vars.end()) return;
        // TODO: make_unique once VlRandomizer is per-instance not per-ref
        m_vars[name]
            = std::make_shared<const VlRandomVar>(name, width, &var, dimension, randmodeIdx);
    }
    template <typename T>
    void write_var(VlQueue<T>& var, int width, const char* name, int dimension,
                   std::uint32_t randmodeIdx = std::numeric_limits<std::uint32_t>::max()) {
        if (m_vars.find(name) != m_vars.end()) return;
        m_vars[name] = std::make_shared<const VlRandomArrayVarTemplate<VlQueue<T>>>(
            name, width, &var, dimension, randmodeIdx);
        if (dimension > 0) {
            idx = 0;
            record_arr_table(var, name, dimension, {}, {});
        }
    }
    template <typename T, std::size_t N_Depth>
    void write_var(VlUnpacked<T, N_Depth>& var, int width, const char* name, int dimension,
                   std::uint32_t randmodeIdx = std::numeric_limits<std::uint32_t>::max()) {
        if (m_vars.find(name) != m_vars.end()) return;
        m_vars[name] = std::make_shared<const VlRandomArrayVarTemplate<VlUnpacked<T, N_Depth>>>(
            name, width, &var, dimension, randmodeIdx);
        if (dimension > 0) {
            idx = 0;
            record_arr_table(var, name, dimension, {}, {});
        }
    }
    template <typename T_Key, typename T_Value>
    void write_var(VlAssocArray<T_Key, T_Value>& var, int width, const char* name, int dimension,
                   std::uint32_t randmodeIdx = std::numeric_limits<std::uint32_t>::max()) {
        if (m_vars.find(name) != m_vars.end()) return;
        m_vars[name]
            = std::make_shared<const VlRandomArrayVarTemplate<VlAssocArray<T_Key, T_Value>>>(
                name, width, &var, dimension, randmodeIdx);
        if (dimension > 0) {
            idx = 0;
            record_arr_table(var, name, dimension, {}, {});
        }
    }
    template <typename T, std::size_t... I>
    void modifyMembers(T& obj, std::index_sequence<I...>, std::string baseName) {
        // Use the indices to access each member via std::get
        (void)std::initializer_list<int>{
            (write_var(std::get<I>(obj.getMembers(obj)),
                        sizeof(std::get<I>(obj.getMembers(obj))) * 8,
                        (baseName + "." + obj.memberNames()[I]).c_str(), 0), 0)...};
    }

    template <typename T>
    typename std::enable_if<VlIsCustomStruct<T>::value, void>::type
    write_var(T& var, int width, const char* name, int dimension,
              std::uint32_t randmodeIdx = std::numeric_limits<std::uint32_t>::max()) {
        modifyMembers(var, var.memberIndices(), name);
    }

    int idx;
    std::string generateKey(const std::string& name, int idx) {
        if (!name.empty() && name[0] == '\\') {
            const size_t space_pos = name.find(' ');
            return (space_pos != std::string::npos ? name.substr(0, space_pos) : name)
                   + std::to_string(idx);
        }
        const size_t bracket_pos = name.find('[');
        return (bracket_pos != std::string::npos ? name.substr(0, bracket_pos) : name)
               + std::to_string(idx);
    }

    template <typename T>
    typename std::enable_if<!std::is_class<T>::value, void>::type
    record_arr_table(T& var, const std::string name, int dimension, std::vector<IData> indices,
                     std::vector<size_t> idxWidths) {
        const std::string key = generateKey(name, idx);
        m_arr_vars[key] = std::make_shared<ArrayInfo>(name, &var, idx, indices, idxWidths);
        ++idx;
    }
    template <typename T>
    void record_arr_table(VlQueue<T>& var, const std::string name, int dimension,
                          std::vector<IData> indices, std::vector<size_t> idxWidths) {
        if ((dimension > 0) && (var.size() != 0)) {
            idxWidths.push_back(32);
            for (size_t i = 0; i < var.size(); ++i) {
                const std::string indexed_name = name + "[" + std::to_string(i) + "]";
                indices.push_back(i);
                record_arr_table(var.atWrite(i), indexed_name, dimension - 1, indices, idxWidths);
                indices.pop_back();
            }
        }
    }
    template <typename T, std::size_t N_Depth>
    void record_arr_table(VlUnpacked<T, N_Depth>& var, const std::string name, int dimension,
                          std::vector<IData> indices, std::vector<size_t> idxWidths) {
        if ((dimension > 0) && (N_Depth != 0)) {
            idxWidths.push_back(32);
            for (size_t i = 0; i < N_Depth; ++i) {
                const std::string indexed_name = name + "[" + std::to_string(i) + "]";
                indices.push_back(i);
                record_arr_table(var.operator[](i), indexed_name, dimension - 1, indices,
                                 idxWidths);
                indices.pop_back();
            }
        }
    }
    template <typename T_Key, typename T_Value>
    void record_arr_table(VlAssocArray<T_Key, T_Value>& var, const std::string name, int dimension,
                          std::vector<IData> indices, std::vector<size_t> idxWidths) {
        if ((dimension > 0) && (var.size() != 0)) {
            for (auto it = var.begin(); it != var.end(); ++it) {
                const T_Key& key = it->first;
                const T_Value& value = it->second;

                std::string indexed_name;
                std::vector<size_t> integral_index;
                size_t idx_width = 0;

                process_key(key, indexed_name, integral_index, name, idx_width);

                // Update indices and widths
                idxWidths.push_back(idx_width);
                indices.insert(indices.end(), integral_index.begin(), integral_index.end());

                record_arr_table(var.at(key), indexed_name, dimension - 1, indices, idxWidths);

                // Cleanup indices and widths
                idxWidths.pop_back();
                indices.resize(indices.size() - integral_index.size());
            }
        }
    }

    void hard(std::string&& constraint);
    void clear();
    void set_randmode(const VlQueue<CData>& randmode) { m_randmode = &randmode; }
#ifdef VL_DEBUG
    void dump() const;
#endif
};

#endif  // Guard
