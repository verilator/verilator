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

#include <iostream>
#include <ostream>
//=============================================================================
// VlRandomExpr and subclasses represent expressions for the constraint solver.
class ArrayInfo {
public:
    const std::string m_name;
    void* const m_datap;
    const int m_index;
    std::vector<size_t> m_indices;

    ArrayInfo(const std::string name, void* datap, int index, const std::vector<size_t>& indices)
        : m_name(name)
        , m_datap(datap)
        , m_index(index)
        , m_indices(indices) {}
};

class VlRandomVar VL_NOT_FINAL {
    const char* const m_name;  // Variable name
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
        , m_randModeIdx{randModeIdx} {}
    virtual ~VlRandomVar() = default;
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
    mutable const std::map<std::string, std::shared_ptr<const ArrayInfo>>* m_arr_vars_ref = nullptr;
    virtual void setArrayInfo(const std::map<std::string, std::shared_ptr<const ArrayInfo>>& arr_vars) const { m_arr_vars_ref = &arr_vars; }
    mutable std::map<std::string, int> count_cache;
    int countMatchingElements(const std::map<std::string, std::shared_ptr<const ArrayInfo>>& arr_vars, const std::string& base_name) const {
        if (count_cache.find(base_name) != count_cache.end()) return count_cache[base_name];
        int count = 0;
        for (int index = 0; arr_vars.find(base_name + std::to_string(index)) != arr_vars.end();
             ++index) {
            count++;
        }
        count_cache[base_name] = count;
        return count;
    }
};

template <typename T>
class VlRandomQueueVar final : public VlRandomVar {
public:
    VlRandomQueueVar(const char* name, int width, void* datap, int dimension,
                     std::uint32_t randModeIdx)
        : VlRandomVar{name, width, datap, dimension, randModeIdx} {}
    void* datap(int idx) const override {
        std::string indexed_name = name() + std::to_string(idx);
        if (auto it = m_arr_vars_ref->find(indexed_name); it != m_arr_vars_ref->end()) {
            return it->second->m_datap;
        }
        return &static_cast<T*>(VlRandomVar::datap(idx))->atWrite(idx);
    }
    void emitSelect(std::ostream& s, const std::vector<size_t>& indices) const {
        for (size_t idx = 0; idx < indices.size(); ++idx) s << "(select ";
        s << name();
        for (size_t idx = 0; idx < indices.size(); ++idx) {
            s << " #x";
            for (int j = 28; j >= 0; j -= 4) {
                s << "0123456789abcdef"[(indices[idx] >> j) & 0xf];
            }
            s << ")";
        }
    }
    void emitGetValue(std::ostream& s) const override {
        int elementCounts = countMatchingElements(*m_arr_vars_ref, name());
        for (int i = 0; i < elementCounts; i++) {
            std::string indexed_name = name() + std::to_string(i);
            if (auto it = m_arr_vars_ref->find(indexed_name); it != m_arr_vars_ref->end()) {
                std::vector<size_t> indices = it->second->m_indices;
                emitSelect(s, indices);
            }
        }
    }
    void emitType(std::ostream& s) const override {
        if (dimension() > 0) {
            for (int i = 0; i < dimension(); ++i) s << "(Array (_ BitVec 32) ";
            s << "(_ BitVec " << width() << ")";
            for (int i = 0; i < dimension(); ++i) s << ")";
        }
    }
    int totalWidth() const override {
        const int elementCounts = countMatchingElements(*m_arr_vars_ref, name());
        return width() * elementCounts;
    }
    void emitExtract(std::ostream& s, int i) const override {
        const int j = i / width();
        i = i % width();
        s << " ((_ extract " << i << ' ' << i << ')';
        std::string indexed_name = name() + std::to_string(j);
        if (auto it = m_arr_vars_ref->find(indexed_name); it != m_arr_vars_ref->end()) {
            std::vector<size_t> indices = it->second->m_indices;
            emitSelect(s, indices);
        }
        s << ')';
    }
};

template <typename T>
class VlRandomArrayVar final : public VlRandomVar {
public:
    VlRandomArrayVar(const char* name, int width, void* datap, int dimension,
                     std::uint32_t randModeIdx)
        : VlRandomVar{name, width, datap, dimension, randModeIdx} {}
    void* datap(int idx) const override {
        std::string indexed_name = name() + std::to_string(idx);
        if (auto it = m_arr_vars_ref->find(indexed_name); it != m_arr_vars_ref->end()) {
            return it->second->m_datap;
        }
        return &static_cast<T*>(VlRandomVar::datap(idx))->operator[](idx);
    }
    void emitSelect(std::ostream& s, const std::vector<size_t>& indices) const {
        for (size_t idx = 0; idx < indices.size(); ++idx) s << "(select ";
        s << name();
        for (size_t idx = 0; idx < indices.size(); ++idx) {
            s << " #x";
            for (int j = 28; j >= 0; j -= 4) {
                s << "0123456789abcdef"[(indices[idx] >> j) & 0xf];
            }
            s << ")";
        }
    }
    void emitGetValue(std::ostream& s) const override {
        int elementCounts = countMatchingElements(*m_arr_vars_ref, name());
        for (int i = 0; i < elementCounts; i++) {
            std::string indexed_name = name() + std::to_string(i);
            if (auto it = m_arr_vars_ref->find(indexed_name); it != m_arr_vars_ref->end()) {
                std::vector<size_t> indices = it->second->m_indices;
                emitSelect(s, indices);
            }
        }
    }
    void emitType(std::ostream& s) const override {
        if (dimension() > 0) {
            for (int i = 0; i < dimension(); ++i) s << "(Array (_ BitVec 32) ";
            s << "(_ BitVec " << width() << ")";
            for (int i = 0; i < dimension(); ++i) s << ")";
        }
    }
    int totalWidth() const override {
        const int elementCounts = countMatchingElements(*m_arr_vars_ref, name());
        return width() * elementCounts;
    }
    void emitExtract(std::ostream& s, int i) const override {
        const int j = i / width();
        i = i % width();
        s << " ((_ extract " << i << ' ' << i << ')';
        std::string indexed_name = name() + std::to_string(j);
        if (auto it = m_arr_vars_ref->find(indexed_name); it != m_arr_vars_ref->end()) {
            std::vector<size_t> indices = it->second->m_indices;
            emitSelect(s, indices);
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
    std::map<std::string, std::shared_ptr<const ArrayInfo>> m_arr_vars;
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
    template <typename T>
    void write_var(T& var, int width, const char* name, int dimension,
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
        m_vars[name] = std::make_shared<const VlRandomQueueVar<VlQueue<T>>>(
            name, width, &var, dimension, randmodeIdx);
        if (dimension > 0) {
            idx = 0;
            record_arr_table(var, name, dimension, {});
        }
    }
    template <typename T, std::size_t N>
    void write_var(VlUnpacked<T, N>& var, int width, const char* name, int dimension,
                   std::uint32_t randmodeIdx = std::numeric_limits<std::uint32_t>::max()) {
        if (m_vars.find(name) != m_vars.end()) return;
        m_vars[name] = std::make_shared<const VlRandomArrayVar<VlUnpacked<T, N>>>(
            name, width, &var, dimension, randmodeIdx);
        if (dimension > 0) {
            idx = 0;
            record_arr_table(var, name, dimension, {});
        }
    }
    int idx = 0;
    std::string generateKey(const std::string& name, int idx) {
        size_t bracket_pos = name.find('[');
        std::string base_name
            = (bracket_pos != std::string::npos) ? name.substr(0, bracket_pos) : name;
        return base_name + std::to_string(idx);
    }
    template <typename T>
    void record_arr_table(T& var, const std::string name, int dimension,
                          std::vector<size_t> indices) {
        std::string key = generateKey(name, idx);
        m_arr_vars[key] = std::make_shared<ArrayInfo>(name, &var, idx, indices);
        idx += 1;
    }
    template <typename T>
    void record_arr_table(VlQueue<T>& var, const std::string name, int dimension,
                          std::vector<size_t> indices) {
        if ((dimension > 0) && (var.size() != 0)) {
            for (size_t i = 0; i < var.size(); ++i) {
                std::string indexed_name = name + "[" + std::to_string(i) + "]";
                indices.push_back(i);
                record_arr_table(var.atWrite(i), indexed_name, dimension - 1, indices);
                indices.pop_back();
            }
        } else {
            std::string key = generateKey(name, idx);
            m_arr_vars[key] = std::make_shared<ArrayInfo>(name, &var, idx, indices);
            idx += 1;
        }
    }
    template <typename T, std::size_t N>
    void record_arr_table(VlUnpacked<T, N>& var, const std::string name, int dimension,
                          std::vector<size_t> indices) {
        if ((dimension > 0) && (N != 0)) {
            for (size_t i = 0; i < N; ++i) {
                std::string indexed_name = name + "[" + std::to_string(i) + "]";
                indices.push_back(i);
                record_arr_table(var.operator[](i), indexed_name, dimension - 1, indices);
                indices.pop_back();
            }
        } else {
            std::string key = generateKey(name, idx);
            m_arr_vars[key] = std::make_shared<ArrayInfo>(name, &var, idx, indices);
            idx += 1;
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
