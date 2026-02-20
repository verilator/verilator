// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: AstNode sub-types for functional coverage
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 by Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// This file contains AST nodes for SystemVerilog functional coverage
// (IEEE 1800-2023 Section 19)
//
//*************************************************************************

#ifndef VERILATOR_V3ASTNODEFUNCCOV_H_
#define VERILATOR_V3ASTNODEFUNCCOV_H_

#ifndef VERILATOR_V3AST_H_
#error "Use V3Ast.h as the include"
#include "V3Ast.h"
#define VL_NOT_FINAL
#endif

//######################################################################
// Enumerations

enum class VCoverBinsType : uint8_t {
    USER,
    ARRAY,
    AUTO,
    BINS_IGNORE,  // Renamed to avoid Windows macro conflict
    BINS_ILLEGAL,  // Renamed to avoid Windows macro conflict
    DEFAULT,
    BINS_WILDCARD,  // Renamed to avoid Windows macro conflict
    TRANSITION
};

enum class VCoverOptionType : uint8_t {
    WEIGHT,
    GOAL,
    AT_LEAST,
    AUTO_BIN_MAX,
    PER_INSTANCE,
    COMMENT
};

enum class VTransRepType : uint8_t {
    NONE,  // No repetition
    CONSEC,  // Consecutive repetition [*]
    GOTO,  // Goto repetition [->]
    NONCONS  // Nonconsecutive repetition [=]
};

//######################################################################
// Base classes

class AstNodeFuncCovItem VL_NOT_FINAL : public AstNode {
protected:
    string m_name;

public:
    AstNodeFuncCovItem(VNType t, FileLine* fl, const string& name)
        : AstNode{t, fl}
        , m_name{name} {}
    ASTGEN_MEMBERS_AstNodeFuncCovItem;
    string name() const override VL_MT_STABLE { return m_name; }
    void name(const string& flag) override { m_name = flag; }
    bool maybePointedTo() const override { return true; }
};

//######################################################################
// Concrete nodes - ORDER MATTERS FOR ASTGEN!
// Must be in order: CoverBin, CoverCrossBins, CoverOption, CoverSelectExpr,
//                   CoverTransItem, CoverTransSet, Covergroup, CoverpointRef, CoverCross,
//                   Coverpoint

// Forward declarations for types used in constructors
class AstCoverTransSet;
class AstCoverSelectExpr;

class AstCoverBin final : public AstNode {
    // @astgen op1 := rangesp : List[AstNode]
    // @astgen op2 := iffp : Optional[AstNodeExpr]
    // @astgen op3 := arraySizep : Optional[AstNodeExpr]
    // @astgen op4 := transp : List[AstCoverTransSet]
    string m_name;
    VCoverBinsType m_type;
    bool m_isArray = false;

public:
    AstCoverBin(FileLine* fl, const string& name, AstNode* rangesp, bool isIgnore, bool isIllegal,
                bool isWildcard = false)
        : ASTGEN_SUPER_CoverBin(fl)
        , m_name{name}
        , m_type{isWildcard ? VCoverBinsType::BINS_WILDCARD
                            : (isIllegal ? VCoverBinsType::BINS_ILLEGAL
                                         : (isIgnore ? VCoverBinsType::BINS_IGNORE
                                                     : VCoverBinsType::USER))} {
        if (rangesp) addRangesp(rangesp);
    }
    // Constructor for automatic bins
    AstCoverBin(FileLine* fl, const string& name, AstNodeExpr* arraySizep)
        : ASTGEN_SUPER_CoverBin(fl)
        , m_name{name}
        , m_type{VCoverBinsType::AUTO}
        , m_isArray{true} {
        this->arraySizep(arraySizep);
    }
    // Constructor for default bins (catch-all)
    AstCoverBin(FileLine* fl, const string& name, VCoverBinsType type)
        : ASTGEN_SUPER_CoverBin(fl)
        , m_name{name}
        , m_type{type} {
        // DEFAULT bins have no ranges - they catch everything not in other bins
    }
    // Constructor for transition bins
    AstCoverBin(FileLine* fl, const string& name, AstCoverTransSet* transp, bool isIgnore,
                bool isIllegal, bool isArrayBin = false)
        : ASTGEN_SUPER_CoverBin(fl)
        , m_name{name}
        , m_type{isIllegal ? VCoverBinsType::BINS_ILLEGAL
                           : (isIgnore ? VCoverBinsType::BINS_IGNORE : VCoverBinsType::TRANSITION)}
        , m_isArray{isArrayBin} {
        if (transp) addTransp(transp);
    }
    ASTGEN_MEMBERS_AstCoverBin;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    string name() const override VL_MT_STABLE { return m_name; }
    VCoverBinsType binsType() const { return m_type; }
    bool isArray() const { return m_isArray; }
    void isArray(bool flag) { m_isArray = flag; }
};

class AstCoverCrossBins final : public AstNode {
    // @astgen op1 := selectp : Optional[AstCoverSelectExpr]
    string m_name;

public:
    AstCoverCrossBins(FileLine* fl, const string& name, AstCoverSelectExpr* selectp)
        : ASTGEN_SUPER_CoverCrossBins(fl)
        , m_name{name} {
        this->selectp(selectp);
    }
    ASTGEN_MEMBERS_AstCoverCrossBins;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    string name() const override VL_MT_STABLE { return m_name; }
};

class AstCoverOption final : public AstNode {
    // @astgen op1 := valuep : AstNodeExpr
    VCoverOptionType m_type;

public:
    AstCoverOption(FileLine* fl, VCoverOptionType type, AstNodeExpr* valuep)
        : ASTGEN_SUPER_CoverOption(fl)
        , m_type{type} {
        this->valuep(valuep);
    }
    ASTGEN_MEMBERS_AstCoverOption;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    VCoverOptionType optionType() const { return m_type; }
};

class AstCoverSelectExpr final : public AstNode {
    // @astgen op1 := exprp : AstNodeExpr
public:
    AstCoverSelectExpr(FileLine* fl, AstNodeExpr* exprp)
        : ASTGEN_SUPER_CoverSelectExpr(fl) {
        this->exprp(exprp);
    }
    ASTGEN_MEMBERS_AstCoverSelectExpr;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
};

// Represents a single transition item: value or value[*N] or value[->N] or value[=N]
class AstCoverTransItem final : public AstNode {
    // @astgen op1 := valuesp : List[AstNode]  // Range list (values or ranges)
    // @astgen op2 := repMinp : Optional[AstNodeExpr]  // Repetition min count (for [*], [->], [=])
    // @astgen op3 := repMaxp : Optional[AstNodeExpr]  // Repetition max count (for ranges)
    VTransRepType m_repType;

public:
    AstCoverTransItem(FileLine* fl, AstNode* valuesp, VTransRepType repType = VTransRepType::NONE)
        : ASTGEN_SUPER_CoverTransItem(fl)
        , m_repType{repType} {
        if (valuesp) addValuesp(valuesp);
    }
    ASTGEN_MEMBERS_AstCoverTransItem;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    VTransRepType repType() const { return m_repType; }
};

// Represents a transition set: value1 => value2 => value3
class AstCoverTransSet final : public AstNode {
    // @astgen op1 := itemsp : List[AstCoverTransItem]
public:
    AstCoverTransSet(FileLine* fl, AstCoverTransItem* itemsp)
        : ASTGEN_SUPER_CoverTransSet(fl) {
        if (itemsp) addItemsp(itemsp);
    }
    ASTGEN_MEMBERS_AstCoverTransSet;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
};

class AstCovergroup final : public AstNode {
    // @astgen op1 := argsp : List[AstVar]
    // @astgen op2 := membersp : List[AstNode]
    // @astgen op3 := eventp : Optional[AstSenTree]
    string m_name;
    bool m_isClass = false;

public:
    AstCovergroup(FileLine* fl, const string& name, AstNode* membersp, AstSenTree* eventp)
        : ASTGEN_SUPER_Covergroup(fl)
        , m_name{name} {
        if (membersp) addMembersp(membersp);
        this->eventp(eventp);
    }
    ASTGEN_MEMBERS_AstCovergroup;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    string name() const override VL_MT_STABLE { return m_name; }
    void name(const string& name) override { m_name = name; }
    bool isClass() const { return m_isClass; }
    void isClass(bool flag) { m_isClass = flag; }
    bool maybePointedTo() const override { return true; }
};

class AstCoverpointRef final : public AstNode {
    // @astgen ptr := m_coverpointp : Optional[AstCoverpoint]
    string m_name;

public:
    AstCoverpointRef(FileLine* fl, const string& name)
        : ASTGEN_SUPER_CoverpointRef(fl)
        , m_name{name} {}
    ASTGEN_MEMBERS_AstCoverpointRef;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    string name() const override VL_MT_STABLE { return m_name; }
    AstCoverpoint* coverpointp() const { return m_coverpointp; }
    void coverpointp(AstCoverpoint* nodep) { m_coverpointp = nodep; }
};

class AstCoverCross final : public AstNodeFuncCovItem {
    // @astgen op1 := itemsp : List[AstCoverpointRef]
    // @astgen op2 := binsp : List[AstCoverCrossBins]
    // @astgen op3 := optionsp : List[AstCoverOption]
public:
    AstCoverCross(FileLine* fl, const string& name, AstCoverpointRef* itemsp)
        : ASTGEN_SUPER_CoverCross(fl, name) {
        if (itemsp) addItemsp(itemsp);
    }
    ASTGEN_MEMBERS_AstCoverCross;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
};

class AstCoverpoint final : public AstNodeFuncCovItem {
    // @astgen op1 := exprp : AstNodeExpr
    // @astgen op2 := binsp : List[AstCoverBin]
    // @astgen op3 := iffp : Optional[AstNodeExpr]
    // @astgen op4 := optionsp : List[AstCoverOption]
public:
    AstCoverpoint(FileLine* fl, const string& name, AstNodeExpr* exprp)
        : ASTGEN_SUPER_Coverpoint(fl, name) {
        this->exprp(exprp);
    }
    ASTGEN_MEMBERS_AstCoverpoint;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
};

//######################################################################

#endif  // Guard
