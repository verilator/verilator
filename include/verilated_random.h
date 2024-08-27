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
    const std::uint32_t m_randModeIdx;  // rand_mode index

public:
    VlRandomVar(const char* name, int width, void* datap, std::uint32_t randModeIdx)
        : m_name{name}
        , m_datap{datap}
        , m_width{width}
        , m_randModeIdx{randModeIdx} {}
    virtual ~VlRandomVar() = default;
    const char* name() const { return m_name; }
    int width() const { return m_width; }
    virtual void* datap(int idx) const { return m_datap; }
    std::uint32_t randModeIdx() const { return m_randModeIdx; }
    bool randModeIdxNone() const { return randModeIdx() == std::numeric_limits<unsigned>::max(); }
    bool set(const std::string& idx, const std::string& val) const;
    virtual void emitGetValue(std::ostream& s) const;
    virtual void emitExtract(std::ostream& s, int i) const;
    virtual void emitType(std::ostream& s) const;
    virtual int totalWidth() const;
};

template <typename T>
class VlRandomQueueVar final : public VlRandomVar {
public:
    VlRandomQueueVar(const char* name, int width, void* datap, std::uint32_t randModeIdx)
        : VlRandomVar{name, width, datap, randModeIdx} {}
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
    void write_var(T& var, int width, const char* name,
                   std::uint32_t randmodeIdx = std::numeric_limits<std::uint32_t>::max()) {
        if (m_vars.find(name) != m_vars.end()) return;
        // TODO: make_unique once VlRandomizer is per-instance not per-ref
        m_vars[name] = std::make_shared<const VlRandomVar>(name, width, &var, randmodeIdx);
    }
    template <typename T>
    void write_var(VlQueue<T>& var, int width, const char* name,
                   std::uint32_t randmodeIdx = std::numeric_limits<std::uint32_t>::max()) {
        if (m_vars.find(name) != m_vars.end()) return;
        m_vars[name]
            = std::make_shared<const VlRandomQueueVar<VlQueue<T>>>(name, width, &var, randmodeIdx);
    }
    void hard(std::string&& constraint);
    void clear();
    void set_randmode(const VlQueue<CData>& randmode) { m_randmode = &randmode; }
#ifdef VL_DEBUG
    void dump() const;
#endif
};

#endif  // Guard
