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

//=============================================================================
// VlRandomExpr and subclasses represent expressions for the constraint solver.

class VlRandomExpr VL_NOT_FINAL {
public:
    virtual void emit(std::ostream& s) const = 0;
    virtual ~VlRandomExpr() = default;
};
class VlRandomVar final : public VlRandomExpr {
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
    const char* name() const { return m_name; }
    int width() const { return m_width; }
    void* datap() const { return m_datap; }
    std::uint32_t randModeIdx() const { return m_randModeIdx; }
    bool randModeIdxNone() const { return randModeIdx() == std::numeric_limits<unsigned>::max(); }
    bool set(std::string&&) const;
    void emit(std::ostream& s) const override;
};

class VlRandomExtract final : public VlRandomExpr {
    const std::shared_ptr<const VlRandomExpr> m_expr;  // Sub-expression
    const unsigned m_idx;  // Extracted index

public:
    VlRandomExtract(std::shared_ptr<const VlRandomExpr> expr, unsigned idx)
        : m_expr{expr}
        , m_idx{idx} {}
    void emit(std::ostream& s) const override;
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
        auto it = m_vars.find(name);
        if (it != m_vars.end()) return;
        m_vars[name] = std::make_shared<const VlRandomVar>(name, width, &var, randmodeIdx);
    }
    void hard(std::string&& constraint);
    void clear();
    void set_randmode(const VlQueue<CData>& randmode) { m_randmode = &randmode; }
#ifdef VL_DEBUG
    void dump() const;
#endif
};

#endif  // Guard
