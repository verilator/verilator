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

#include <ostream>

//=============================================================================
// VlRandomExpr and subclasses represent expressions for the constraint solver.

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
    virtual int getLength(int dimension) const { return -1; }
};

template <typename T>
class VlRandomQueueVar final : public VlRandomVar {
public:
    VlRandomQueueVar(const char* name, int width, void* datap, int dimension,
                     std::uint32_t randModeIdx)
        : VlRandomVar{name, width, datap, dimension, randModeIdx} {}
    void* datap(int idx) const override {
        return &static_cast<T*>(VlRandomVar::datap(idx))->atWrite(idx);
    }
    void emitSelect(std::ostream& s, int i) const {
        s << " (select " << name() << " #x";
        for (int j = 28; j >= 0; j -= 4) s << "0123456789abcdef"[(i >> j) & 0xf];
        s << ')';
    }
    void emitGetValue(std::ostream& s) const override {
        const int length = static_cast<T*>(VlRandomVar::datap(0))->size();
        for (int i = 0; i < length; i++) emitSelect(s, i);
    }
    void emitType(std::ostream& s) const override {
        s << "(Array (_ BitVec 32) (_ BitVec " << width() << "))";
    }
    int totalWidth() const override {
        const int length = static_cast<T*>(VlRandomVar::datap(0))->size();
        return width() * length;
    }
    void emitExtract(std::ostream& s, int i) const override {
        const int j = i / width();
        i = i % width();
        s << " ((_ extract " << i << ' ' << i << ')';
        emitSelect(s, j);
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
        if (idx < 0) return &static_cast<T*>(VlRandomVar::datap(0))->operator[](0);
        std::vector<size_t> indices(dimension());
        for (int dim = dimension() - 1; dim >= 0; --dim) {
            const int length = getLength(dim);
            indices[dim] = idx % length;
            idx /= length;
        }
        return &static_cast<T*>(VlRandomVar::datap(0))->find_element(indices);
    }

    void emitSelect(std::ostream& s, const std::vector<int>& indices) const {
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

    int getLength(int dimension) const override {
        const auto var = static_cast<const T*>(datap(-1));
        const int lenth = var->find_length(dimension);
        return lenth;
    }

    void emitGetValue(std::ostream& s) const override {
        const int total_dimensions = dimension();
        std::vector<int> lengths;
        for (int dim = 0; dim < total_dimensions; dim++) {
            const int len = getLength(dim);
            lengths.push_back(len);
        }
        std::vector<int> indices(total_dimensions, 0);
        while (true) {
            emitSelect(s, indices);
            int currentDimension = total_dimensions - 1;
            while (currentDimension >= 0
                   && ++indices[currentDimension] >= lengths[currentDimension]) {
                indices[currentDimension] = 0;
                --currentDimension;
            }
            if (currentDimension < 0) break;
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
        int totalLength = 1;
        for (int dim = 0; dim < dimension(); ++dim) {
            const int length = getLength(dim);
            if (length == -1) return 0;
            totalLength *= length;
        }
        return width() * totalLength;
    }

    void emitExtract(std::ostream& s, int i) const override {
        const int j = i / width();
        i = i % width();
        std::vector<int> indices(dimension());
        int idx = j;
        for (int dim = dimension() - 1; dim >= 0; --dim) {
            int length = getLength(dim);
            indices[dim] = idx % length;
            idx /= length;
        }
        s << " ((_ extract " << i << ' ' << i << ')';
        emitSelect(s, indices);
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
    }
    template <typename T, std::size_t N>
    void write_var(VlUnpacked<T, N>& var, int width, const char* name, int dimension,
                   std::uint32_t randmodeIdx = std::numeric_limits<std::uint32_t>::max()) {
        if (m_vars.find(name) != m_vars.end()) return;
        m_vars[name] = std::make_shared<const VlRandomArrayVar<VlUnpacked<T, N>>>(
            name, width, &var, dimension, randmodeIdx);
    }
    void hard(std::string&& constraint);
    void clear();
    void set_randmode(const VlQueue<CData>& randmode) { m_randmode = &randmode; }
#ifdef VL_DEBUG
    void dump() const;
#endif
};

#endif  // Guard
