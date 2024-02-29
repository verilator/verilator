// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Code available from: https://verilator.org
//
// Copyright 2024 by Antmicro Ltd.  This program is free software; you can
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
};
class VlRandomVar VL_NOT_FINAL : public VlRandomExpr {
    const char* const m_name;
    void* const m_ref;
    const int m_width;

public:
    VlRandomVar(const char* name, int width, void* ref)
        : m_name{name}
        , m_ref{ref}
        , m_width{width} {}
    const char* name() const { return m_name; }
    int width() const { return m_width; }
    void* ref() const { return m_ref; }
    virtual void set(unsigned long long) const = 0;
    void emit(std::ostream& s) const;
};
template <typename T>
class VlRandomVarR final : public VlRandomVar {
public:
    VlRandomVarR(const char* name, int width, T* ref)
        : VlRandomVar{name, width, ref} {}
    virtual void set(unsigned long long val) const { *(T*)ref() = val; }
};

class VlRandomConst final : public VlRandomExpr {
    const unsigned long long m_val;
    const int m_width;

public:
    VlRandomConst(unsigned long long val, int width)
        : m_val{val}
        , m_width{width} {}
    void emit(std::ostream& s) const;
};

class VlRandomExtract final : public VlRandomExpr {
    const std::shared_ptr<const VlRandomExpr> m_expr;
    const unsigned m_idx;

public:
    VlRandomExtract(std::shared_ptr<const VlRandomExpr> expr, unsigned idx)
        : m_expr{expr}
        , m_idx{idx} {}
    void emit(std::ostream& s) const;
};

class VlRandomBinOp final : public VlRandomExpr {
    const char* m_op;
    const std::shared_ptr<const VlRandomExpr> m_lhs, m_rhs;

public:
    VlRandomBinOp(const char* op, std::shared_ptr<const VlRandomExpr> lhs,
                  std::shared_ptr<const VlRandomExpr> rhs)
        : m_op{op}
        , m_lhs{lhs}
        , m_rhs{rhs} {}
    void emit(std::ostream& s) const;
};

//=============================================================================
// VlRandomizer is the object holding constraints and variable references.

class VlRandomizer final {
    // MEMBERS
    std::vector<std::string> m_constraints;
    std::map<std::string, std::shared_ptr<const VlRandomVar>> m_vars;
    char* m_line = nullptr;
    size_t m_capacity;

    // PRIVATE METHODS
    std::shared_ptr<const VlRandomExpr> random_constraint(VlRNG& rngr, int bits);
    int parse_solution(FILE* file);

public:
    // METHODS
    // Finds the next solution satisfying the constraints
    bool next(VlRNG& rngr);
    template <typename T>
    void write_var(T& var, int width, const char* name) {
        auto it = m_vars.find(name);
        if (it != m_vars.end()) return;
        auto varp = std::make_shared<const VlRandomVarR<T>>(name, width, &var);
        m_vars[name] = varp;
    }
    void hard(std::string&& constraint);
#ifdef VL_DEBUG
    void dump() const;
#endif
    ~VlRandomizer();
};

#endif  // Guard
