// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: AstNode sub-types representing functional coverage
// constructs
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2025 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU Lesser
// General Public License Version 3 or the Perl Artistic License Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// This files contains all 'AstNode' sub-types that represent expressions,
// i.e.: those constructs that represent, or evaluate to [a possible void]
// value. The root of the hierarchy is 'AstNodeExpr'.
//
// Think of expressions in a very general sense as constructs that "name
// things". The "thing" can be considered the value, but can be highly
// structured. For example, an AstConst can name the value '1', which is
// hopefully familiar. On the opposite end of the spectrum of "things" named by
// expressions, consider AstClassOrPackageRef, that can name a collection of
// pairs (specifically the collection of ('member name', 'member thing')
// pairs). Nevertheless, that collection itself can be considered a value. The
// valid composition of expressions then defines the calculus of values in the
// language.
//
//*************************************************************************

#ifndef VERILATOR_V3ASTNODECOVER_H_
#define VERILATOR_V3ASTNODECOVER_H_

#include "V3FileLine.h"

#include <cstdint>
#ifndef VERILATOR_V3AST_H_
#error "Use V3Ast.h as the include"
#include "V3Ast.h"  // This helps code analysis tools pick up symbols in V3Ast.h
#define VL_NOT_FINAL  // This #define fixes broken code folding in the CLion IDE
#endif

// Covergroup is represented by AstClass

#define VL_ENUM_ELEMENT(x) x,
#define VL_ENUM_STRING(x) #x,

#define VL_ENUM(name, elements) VL_ENUM_SIZED(name, uint8_t, elements)
#define VL_ENUM_SIZED(name, underlying, elements) \
    class name final { \
    public: \
        enum en : underlying { elements(VL_ENUM_ELEMENT) }; \
        const en m_e; \
        const char* ascii() const { \
            static const char* const names[] = {elements(VL_ENUM_STRING)}; \
            return names[m_e]; \
        } \
        constexpr name(en _e) \
            : m_e{_e} {} \
        constexpr operator en() const { return m_e; } \
    }; \
    constexpr bool operator==(const name& lhs, const name& rhs) { return lhs.m_e == rhs.m_e; } \
    constexpr bool operator==(const name& lhs, name::en rhs) { return lhs.m_e == rhs; } \
    constexpr bool operator==(name::en lhs, const name& rhs) { return lhs == rhs.m_e; }

class AstNodeBinsSelect VL_NOT_FINAL : public AstNodeExpr {
public:
    AstNodeBinsSelect(VNType kind, FileLine* fl)
        : AstNodeExpr{kind, fl} {}

    ASTGEN_MEMBERS_AstNodeBinsSelect;
};

#define COVERAGE_BIN_KIND(X) X(BINS) X(ILLEGAL_BINS) X(IGNORE_BINS)
VL_ENUM(VCoverBinKind, COVERAGE_BIN_KIND)
#undef COVERAGE_BIN_KIND

class AstCoverBin final : public AstNode {
    // Represents a coverage bin definition
    //
    // @astgen op1 := valuesp : List[AstNode]
    // @astgen op2 := binNump : Optional[AstNodeExpr]
    // @astgen op3 := withp : Optional[AstNodeExpr]
    // @astgen op4 := iffp : Optional[AstNodeExpr]
    string m_name;  // Name of bin
    VCoverBinKind m_kind;  // Kind of bin
    bool m_array : 1;
    bool m_wildcard : 1;
    bool m_default : 1;
    bool m_default_sequence : 1;

public:
    AstCoverBin(FileLine* fl, const string& name, VCoverBinKind kind)
        : AstNode{VNType::CoverBin, fl}
        , m_name{name}
        , m_kind{kind}
        , m_array{false}
        , m_wildcard{false}
        , m_default{false}
        , m_default_sequence{false} {}
    ASTGEN_MEMBERS_AstCoverBin;
    string name() const override { return m_name; }
    VCoverBinKind kind() const { return m_kind; }
    bool isArray() const { return m_array; }
    void isArray(bool flag) { m_array = flag; }
    bool isWildcard() const { return m_wildcard; }
    void isWildcard(bool flag) { m_wildcard = flag; }
    bool isDefault() const { return m_default; }
    void isDefault(bool flag) { m_default = flag; }
    bool isDefaultSequence() const { return m_default_sequence; }
    void isDefaultSequence(bool flag) { m_default_sequence = flag; }
};

class AstCoverCross final : public AstNode {
    // Represents a covergroup cross definition
    //
    // @astgen op1 := itemsp : List[AstCoverpoint]
    // @astgen op2 := iffp : Optional[AstNodeExpr]
    // @astgen op3 := binsp : List[AstCoverBin]
    // @astgen op4 := optionsp : List[AstCoverOption]

public:
    AstCoverCross(FileLine* fl)
        : AstNode{VNType::CoverCross, fl} {}
    ASTGEN_MEMBERS_AstCoverCross;
};

class AstCoverOption final : public AstNode {
    // Represents a covergroup option
    //
    // @astgen op1 := valuep : AstNodeExpr  // Value expression
    string m_name;  // Name of option
    bool m_type_option;

public:
    AstCoverOption(FileLine* fl, const std::string& name, AstNodeExpr* valuep, bool type_option)
        : AstNode{VNType::CoverOption, fl}
        , m_name{name}
        , m_type_option{type_option} {
          this->valuep(valuep);
        }
    ASTGEN_MEMBERS_AstCoverOption;
    const string& optionName() const { return m_name; }
    void optionName(const string& name) { m_name = name; }
    bool isTypeOption() const { return m_type_option; }
    void isTypeOption(bool flag) { m_type_option = flag; }
    AstNode* scopep() const { return backp(); }
};

class AstCoverpoint final : public AstNode {
    // Represents a coverpoint definition
    //
    // @astgen op1 := exprp : AstNodeExpr                  // Target expression
    // @astgen op2 := childDTypep : Optional[AstNodeDType]
    // @astgen op3 := iffp : Optional[AstNodeExpr]
    // @astgen op4 := binsp : List[AstCoverBin]      // Coverage bins
    // @astgen op5 := optionsp : List[AstCoverOption]  // Coverpoint options
    bool m_implicit : 1;

public:
    explicit AstCoverpoint(FileLine* fl)
        : AstNode{VNType::Coverpoint, fl}
        , m_implicit{false} {}
    ASTGEN_MEMBERS_AstCoverpoint;
    bool isImplicit() const { return m_implicit; }
    void isImplicit(bool flag) { m_implicit = flag; }
};

#define TRANS_RANGE_LIST_ELEMENTS(X) \
    X(NONE) \
    X(CONSECUTIVE) \
    X(NONCONSECUTIVE) \
    X(GOTO)
VL_ENUM(VTransRangeListKind, TRANS_RANGE_LIST_ELEMENTS)
#undef TRANS_RANGE_LIST_ELEMENTS

class AstTransRangeList final : public AstNode {
    // Represents a list of transition ranges
    //
    // @astgen op1 := itemsp : List[AstNode]  // Transition range expressions
    // @astgen op2 := fromp : AstNodeExpr  // Transition range expressions
    // @astgen op3 := top : Optional[AstNodeExpr]  // Transition range expressions
    VTransRangeListKind m_kind;

public:
    AstTransRangeList(FileLine* fl, VTransRangeListKind kind)
        : AstNode{VNType::TransRangeList, fl}
        , m_kind{kind} {}
    ASTGEN_MEMBERS_AstTransRangeList;
    VTransRangeListKind kind() const { return m_kind; }
};

class AstTransSet final : public AstNode {
    // Represents a transition set
    //
    // @astgen op1 := rangesp : List[AstTransRangeList]

public:
    AstTransSet(FileLine* fl)
        : AstNode{VNType::TransSet, fl} {}
    ASTGEN_MEMBERS_AstTransSet;
};

class AstBinsSelectWith final : public AstNodeBinsSelect {
    // Represents a bins selection with a filter expression
    //
    // @astgen op1 := exprp : AstNodeBinsSelect  // Base bins selection
    // @astgen op2 := withp : AstNodeExpr  // Filter expression
    // @astgen op3 := matchesp : Optional[AstNodeExpr]  // Matches expression

public:
    AstBinsSelectWith(FileLine* fl)
        : AstNodeBinsSelect{VNType::BinsSelectWith, fl} {}
    ASTGEN_MEMBERS_AstBinsSelectWith;
};

class AstConditionBinsSelect final : public AstNodeBinsSelect {
    // Represents select_condition
    //
    // @astgen op1 := binsp : AstNode              // Target bin
    // @astgen op2 := intersectsp : List[AstNode]  // Intersects

public:
    AstConditionBinsSelect(FileLine* fl, AstNode *binsp)
        : AstNodeBinsSelect{VNType::ConditionBinsSelect, fl} {
          this->binsp(binsp);
        }
    ASTGEN_MEMBERS_AstConditionBinsSelect;
};

class AstCrossIDBinsSelect final : public AstNodeBinsSelect {
    // Represents a cross ID bins selection

    std::string cross_name;

public:
    AstCrossIDBinsSelect(FileLine* fl, const std::string& name)
        : AstNodeBinsSelect{VNType::CrossIDBinsSelect, fl}
        , cross_name{name} {}
    ASTGEN_MEMBERS_AstCrossIDBinsSelect;
    const std::string& target() const { return cross_name; }
};

class AstCrossSetExprBinsSelect final : public AstNodeBinsSelect {
    // Represents a set expression for selecting bins
    //
    // @astgen op1 := exprp : AstNodeExpr  // Set expression
    // @astgen op2 := matchesp : Optional[AstNodeExpr]  // Matches expression

public:
    AstCrossSetExprBinsSelect(FileLine* fl, AstNodeExpr* exprp, AstNodeExpr* matchesp)
        : AstNodeBinsSelect{VNType::CrossSetExprBinsSelect, fl} {
        this->exprp(exprp);
        this->matchesp(matchesp);
    }
    ASTGEN_MEMBERS_AstCrossSetExprBinsSelect;
};

class AstInvalidBinsSelect final : public AstNodeBinsSelect {
    // Represents an invalid bins selection
    //
    // @astgen op1 := selectp : AstNodeBinsSelect  // Invalid bins selection
public:
    AstInvalidBinsSelect(FileLine* fl, AstNodeBinsSelect* selectp)
        : AstNodeBinsSelect{VNType::InvalidBinsSelect, fl} {
        this->selectp(selectp);
    };
    ASTGEN_MEMBERS_AstInvalidBinsSelect;
};

#undef VL_ENUM_ELEMENT
#undef VL_ENUM_STRING
#undef VL_ENUM
#undef VL_ENUM_SIZED

#endif  // Guard
