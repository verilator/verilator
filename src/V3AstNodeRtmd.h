// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: AstNode sub-types representing the RTMD
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// This file contains the 'AstNode' sub-types representing the
// Run Time Model Descriptors (RTMD), which describe the generated model as
// data for use at run time (e.g. by tracing).
//
// There are 3 main kinds of descriptors:
// - AstNodeRtmdDataType, its sub-types + AstRtmdEnumItem and AstRtmdMember
//   represent data types. These relate to the AstNodeDType hierarchy, but
//   can only represent a subset of internal data types, and more importantly
//   they map source level SystemVerilog types as defined in the standard,
//   so they can be presented to the user accurately. RTMD data types are
//   completely interned via AstTypeTable::rtmdDataTypesp(), so there is only
//   ever one descriptor representing a unique type.
// - AstRtmdSignalType represents the type of a signal, which is a data
//   type + extra info (e.g. Var/Wire/Param + Input/Output/Inout/Nonport).
// - AstNodeRtmdItem and its sub-types represent the static scope hierarchy
//   of the design. It is stored as tree rooted on AstRtmdHier, which loosely
//   corresponds to a hierarchy scope in the design, but can represent a non
//   source level scope (e.g. the ROOTIO level holding the variables of the
//   root module).
//
// The Rtmd is constructed early, by V3Rtmd::buildAll(). It is transformed
// and considered by passes as they proceed. Prior to V3Scope, each relevant
// AstNodeModule holds its own AstRtmdHier descriptor. V3Scope inlines
// descriptors of instances, and the completely flattened descriptor is
// then held under AstTopScope. Finally V3EmitCRtmd emits the descriptors
// as C++ static data, which is then passed to the runtime.
//
//*************************************************************************

#ifndef VERILATOR_V3ASTNODERTMD_H_
#define VERILATOR_V3ASTNODERTMD_H_

#ifndef VERILATOR_V3AST_H_
#error "Use V3Ast.h as the include"
#include "V3Ast.h"  // This helps code analysis tools pick up symbols in V3Ast.h
#define VL_NOT_FINAL  // This #define fixes broken code folding in the CLion IDE
#endif

// === Abstract base node types (AstNode*) =====================================

class AstNodeRtmdDataType VL_NOT_FINAL : public AstNode {
    // Describes a source level data type as represented in the RTMD
protected:
    AstNodeRtmdDataType(VNType t, FileLine* fl)
        : AstNode{t, fl} {}

public:
    ASTGEN_MEMBERS_AstNodeRtmdDataType;
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
};
class AstNodeRtmdItem VL_NOT_FINAL : public AstNode {
    // An item describing the hierarchy of the design
protected:
    AstNodeRtmdItem(VNType t, FileLine* fl)
        : AstNode{t, fl} {}

public:
    ASTGEN_MEMBERS_AstNodeRtmdItem;
};

// === Concrete node types =====================================================

// === AstNode ===
class AstRtmdEnumItem final : public AstNode {
    // One item of an AstRtmdDTEnum
    const std::string m_name;  // Name of the item
    const std::string m_value;  // Value of the item

public:
    AstRtmdEnumItem(FileLine* fl, const std::string& name, const std::string& value)
        : ASTGEN_SUPER_RtmdEnumItem(fl)
        , m_name{name}
        , m_value{value} {}
    ASTGEN_MEMBERS_AstRtmdEnumItem;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override {
        const AstRtmdEnumItem* const asamep = VN_DBG_AS(samep, RtmdEnumItem);
        return name() == asamep->name() && value() == asamep->value();
    }
    std::string name() const override VL_MT_STABLE { return m_name; }
    std::string value() const { return m_value; }
};
class AstRtmdMember final : public AstNode {
    // A member of an RTMD struct or union data type
    // @astgen ptr := m_rtmddtp : AstNodeRtmdDataType  // Rtmd of the member's data type
    const std::string m_name;  // Name of the member
    const uint32_t m_lsb;  // Bit offset of a packed struct or union member, 0 if unpacked

public:
    AstRtmdMember(FileLine* fl, const std::string& name, AstNodeRtmdDataType* rtmddtp,
                  uint32_t lsb)
        : ASTGEN_SUPER_RtmdMember(fl)
        , m_name{name}
        , m_lsb{lsb}
        , m_rtmddtp{rtmddtp} {}
    ASTGEN_MEMBERS_AstRtmdMember;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override {
        const AstRtmdMember* const asamep = VN_DBG_AS(samep, RtmdMember);
        return name() == asamep->name() && lsb() == asamep->lsb()
               && rtmddtp() == asamep->rtmddtp();
    }
    std::string name() const override VL_MT_STABLE { return m_name; }
    uint32_t lsb() const { return m_lsb; }
    AstNodeRtmdDataType* rtmddtp() const { return m_rtmddtp; }
};
class AstRtmdSignalType final : public AstNode {
    // How a signal is declared: its data type, kind and direction. Not an AstNodeRtmdDataType,
    // as it does not compose.
    // @astgen ptr := m_rtmddtp : AstNodeRtmdDataType  // Type of the value
    const VRtmdSignalKind m_kind;  // Kind of variable or net
    const VDirection m_direction;  // Declared direction, or NONE if it is not a port
public:
    AstRtmdSignalType(FileLine* fl, AstNodeRtmdDataType* rtmddtp, VRtmdSignalKind kind,
                      VDirection direction)
        : ASTGEN_SUPER_RtmdSignalType(fl)
        , m_kind{kind}
        , m_direction{direction}
        , m_rtmddtp{rtmddtp} {}
    ASTGEN_MEMBERS_AstRtmdSignalType;
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override {
        const AstRtmdSignalType* const asamep = VN_DBG_AS(samep, RtmdSignalType);
        return rtmddtp() == asamep->rtmddtp()  //
               && kind() == asamep->kind()  //
               && direction() == asamep->direction();
    }
    AstNodeRtmdDataType* rtmddtp() const { return m_rtmddtp; }
    VRtmdSignalKind kind() const { return m_kind; }
    VDirection direction() const { return m_direction; }
};

// === AstNodeRtmdDataType ===
class AstRtmdDTAtom final : public AstNodeRtmdDataType {
    // A builtin type ('logic', 'bit', 'int', etc.)
    const VBasicDTypeKwd m_keyword;  // Which builtin
    const bool m_signed;  // Is signed/unsigned
public:
    AstRtmdDTAtom(FileLine* fl, VBasicDTypeKwd keyword, bool isSigned)
        : ASTGEN_SUPER_RtmdDTAtom(fl)
        , m_keyword{keyword}
        , m_signed{isSigned} {}
    ASTGEN_MEMBERS_AstRtmdDTAtom;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override {
        const AstRtmdDTAtom* const asamep = VN_DBG_AS(samep, RtmdDTAtom);
        return keyword() == asamep->keyword() && isSigned() == asamep->isSigned();
    }
    VBasicDTypeKwd keyword() const { return m_keyword; }
    uint32_t bits() const { return m_keyword.width(); }
    bool isSigned() const { return m_signed; }
};
class AstRtmdDTEnum final : public AstNodeRtmdDataType {
    // An enumeration type
    // @astgen op1 := itemsp : List[AstRtmdEnumItem]  // The enumerated constants
    // @astgen ptr := m_rtmddtp : AstNodeRtmdDataType  // Underlying type of the representation
    const std::string m_name;  // Name of the enum
public:
    AstRtmdDTEnum(FileLine* fl, const std::string& name, AstNodeRtmdDataType* rtmddtp)
        : ASTGEN_SUPER_RtmdDTEnum(fl)
        , m_name{name}
        , m_rtmddtp{rtmddtp} {}
    ASTGEN_MEMBERS_AstRtmdDTEnum;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override {
        const AstRtmdDTEnum* const asamep = VN_DBG_AS(samep, RtmdDTEnum);
        return name() == asamep->name() && rtmddtp() == asamep->rtmddtp();
    }
    std::string name() const override VL_MT_STABLE { return m_name; }
    AstNodeRtmdDataType* rtmddtp() const { return m_rtmddtp; }
};
class AstRtmdDTPackedArray final : public AstNodeRtmdDataType {
    // A packed array type, including ranged AstBasicDTypes
    // @astgen ptr := m_elemRtmddtp : AstNodeRtmdDataType  // Element type
    const int32_t m_left;  // Declared left index
    const int32_t m_right;  // Declared right index
    const bool m_signed;  // The value as a whole is signed
public:
    AstRtmdDTPackedArray(FileLine* fl, AstNodeRtmdDataType* elemRtmddtp, int32_t left,
                         int32_t right, bool isSigned)
        : ASTGEN_SUPER_RtmdDTPackedArray(fl)
        , m_left{left}
        , m_right{right}
        , m_signed{isSigned}
        , m_elemRtmddtp{elemRtmddtp} {}
    ASTGEN_MEMBERS_AstRtmdDTPackedArray;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override {
        const AstRtmdDTPackedArray* const asamep = VN_DBG_AS(samep, RtmdDTPackedArray);
        return elemRtmddtp() == asamep->elemRtmddtp()  //
               && left() == asamep->left()  //
               && right() == asamep->right()  //
               && isSigned() == asamep->isSigned();
    }
    AstNodeRtmdDataType* elemRtmddtp() const { return m_elemRtmddtp; }
    int32_t left() const { return m_left; }
    int32_t right() const { return m_right; }
    bool isSigned() const { return m_signed; }
};
class AstRtmdDTPackedStruct final : public AstNodeRtmdDataType {
    // A packed structure type
    // @astgen op1 := membersp : List[AstRtmdMember]  // The members
    const bool m_signed;  // The value as a whole is signed
public:
    AstRtmdDTPackedStruct(FileLine* fl, bool isSigned, AstRtmdMember* membersp)
        : ASTGEN_SUPER_RtmdDTPackedStruct(fl)
        , m_signed{isSigned} {
        this->addMembersp(membersp);
    }
    ASTGEN_MEMBERS_AstRtmdDTPackedStruct;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override {
        const AstRtmdDTPackedStruct* const asamep = VN_DBG_AS(samep, RtmdDTPackedStruct);
        return isSigned() == asamep->isSigned();
    }
    bool isSigned() const { return m_signed; }
};
class AstRtmdDTPackedUnion final : public AstNodeRtmdDataType {
    // A packed union type
    // @astgen op1 := membersp : List[AstRtmdMember]  // The members
    const bool m_signed;  // The value as a whole is signed
public:
    AstRtmdDTPackedUnion(FileLine* fl, bool isSigned, AstRtmdMember* membersp)
        : ASTGEN_SUPER_RtmdDTPackedUnion(fl)
        , m_signed{isSigned} {
        this->addMembersp(membersp);
    }
    ASTGEN_MEMBERS_AstRtmdDTPackedUnion;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override {
        const AstRtmdDTPackedUnion* const asamep = VN_DBG_AS(samep, RtmdDTPackedUnion);
        return isSigned() == asamep->isSigned();
    }
    bool isSigned() const { return m_signed; }
};
class AstRtmdDTUnpackedArray final : public AstNodeRtmdDataType {
    // An unpacked array type
    // @astgen ptr := m_elemRtmddtp : AstNodeRtmdDataType  // Element type
    const int32_t m_left;  // Declared left index
    const int32_t m_right;  // Declared right index

public:
    AstRtmdDTUnpackedArray(FileLine* fl, AstUnpackArrayDType* dtypep,
                           AstNodeRtmdDataType* elemRtmddtp, int32_t left, int32_t right)
        : ASTGEN_SUPER_RtmdDTUnpackedArray(fl)
        , m_left{left}
        , m_right{right}
        , m_elemRtmddtp{elemRtmddtp} {
        this->dtypep(dtypep);
    }
    ASTGEN_MEMBERS_AstRtmdDTUnpackedArray;
    bool hasDType() const override VL_MT_SAFE { return true; }
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override {
        const AstRtmdDTUnpackedArray* const asamep = VN_DBG_AS(samep, RtmdDTUnpackedArray);
        return elemRtmddtp() == asamep->elemRtmddtp()  //
               && left() == asamep->left()  //
               && right() == asamep->right();
    }
    AstNodeRtmdDataType* elemRtmddtp() const { return m_elemRtmddtp; }
    int32_t left() const { return m_left; }
    int32_t right() const { return m_right; }
};
class AstRtmdDTUnpackedStruct final : public AstNodeRtmdDataType {
    // An unpacked structure type
    // @astgen op1 := membersp : List[AstRtmdMember]  // The members
public:
    AstRtmdDTUnpackedStruct(FileLine* fl, AstStructDType* dtypep, AstRtmdMember* membersp)
        : ASTGEN_SUPER_RtmdDTUnpackedStruct(fl) {
        this->addMembersp(membersp);
        this->dtypep(dtypep);
    }
    ASTGEN_MEMBERS_AstRtmdDTUnpackedStruct;
    bool hasDType() const override VL_MT_SAFE { return true; }
};

// === AstNodeRtmdItem ===
class AstRtmdHier final : public AstNodeRtmdItem {
    // A hierarchy level: e.g. an instance, generate/begin block, fork, function or task
    // @astgen op1 := itemsp : List[AstNodeRtmdItem]  // Contents of this level
    const VRtmdHierKind m_kind;  // Kind of hierarchy level
    const std::string m_name;  // Name of the hierarchy entity

public:
    AstRtmdHier(FileLine* fl, const std::string& name, VRtmdHierKind kind)
        : ASTGEN_SUPER_RtmdHier(fl)
        , m_kind{kind}
        , m_name{name} {}
    ASTGEN_MEMBERS_AstRtmdHier;
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override;
    std::string name() const override VL_MT_STABLE { return m_name; }
    VRtmdHierKind kind() const { return m_kind; }
};
class AstRtmdIfaceRef final : public AstNodeRtmdItem {
    // An interface reference variable, shown as the referenced interface's hierarchy level
    // @astgen op1 := refp : Optional[AstVarRef]  // The interface reference, until linkDotScope
    // @astgen ptr := m_ifaceRtmdp : Optional[AstRtmdHier] // Inlined RTMD of the target interface
    const std::string m_name;  // Name of the reference
public:
    AstRtmdIfaceRef(FileLine* fl, const std::string& name, AstVarRef* refp)
        : ASTGEN_SUPER_RtmdIfaceRef(fl)
        , m_name{name} {
        this->refp(refp);
    }
    ASTGEN_MEMBERS_AstRtmdIfaceRef;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override;
    std::string name() const override VL_MT_STABLE { return m_name; }
    AstRtmdHier* ifaceRtmdp() const { return m_ifaceRtmdp; }
    void ifaceRtmdp(AstRtmdHier* nodep) { m_ifaceRtmdp = nodep; }
};
class AstRtmdInstance final : public AstNodeRtmdItem {
    // A sub-instance.
    // @astgen ptr := m_cellp : Optional[AstCell]  // The cell, until V3Scope
    const std::string m_name;  // Name of the instance
public:
    AstRtmdInstance(FileLine* fl, const std::string& name, AstCell* cellp)
        : ASTGEN_SUPER_RtmdInstance(fl)
        , m_name{name}
        , m_cellp{cellp} {}
    ASTGEN_MEMBERS_AstRtmdInstance;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override;
    std::string name() const override VL_MT_STABLE { return m_name; }
    AstCell* cellp() const { return m_cellp; }
    void cellp(AstCell* cellp) { m_cellp = cellp; }
};
class AstRtmdPartition final : public AstNodeRtmdItem {
    // An instance of a separately verilated model
    const std::string m_name;  // Name of the instance in the hierarchy
public:
    AstRtmdPartition(FileLine* fl, const std::string& name)
        : ASTGEN_SUPER_RtmdPartition(fl)
        , m_name{name} {}
    ASTGEN_MEMBERS_AstRtmdPartition;
    bool sameNode(const AstNode* samep) const override;
    std::string name() const override VL_MT_STABLE { return m_name; }
};
class AstRtmdSignal final : public AstNodeRtmdItem {
    // A signal
    // @astgen op1 := refp : Optional[AstVarRef]  // Reference to the variable holding the value,
    //                                              // if the value is accessible at run time
    // @astgen ptr := m_typeDescp : AstRtmdSignalType  // Signal type
    // Scope holding the variable, which might differ from the described scope. Set by V3Descope.
    // @astgen ptr := m_refScopep : Optional[AstScope]
    const std::string m_name;  // Name of the signal in the hierarchy
    uint32_t m_actSetIdx = ~0U;  // Index of its set in AstNetlist::actSets(), from V3Trace
    bool m_traced = false;  // Traced, as its variable, unless turned off by V3Rtmd::scopedAll
public:
    AstRtmdSignal(FileLine* fl, const std::string& name, AstRtmdSignalType* typeDescp,
                  AstVarRef* refp)
        : ASTGEN_SUPER_RtmdSignal(fl)
        , m_name{name}
        , m_typeDescp{typeDescp} {
        this->refp(refp);
    }
    ASTGEN_MEMBERS_AstRtmdSignal;
    const char* broken() const override {
        BROKEN_RTN(m_traced && !refp());  // The value of a traced signal must be accessible
        return nullptr;
    }
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override;
    std::string name() const override VL_MT_STABLE { return m_name; }
    // The variable and its scope, only if the value is accessible
    AstVar* varp() const { return refp()->varp(); }
    AstVarScope* vscp() const { return refp()->varScopep(); }
    AstRtmdSignalType* typeDescp() const { return m_typeDescp; }
    bool hasActSet() const { return m_actSetIdx != ~0U; }
    uint32_t actSetIdx() const { return m_actSetIdx; }
    void actSetIdx(uint32_t idx) { m_actSetIdx = idx; }
    bool traced() const { return m_traced; }
    void traced(bool flag) { m_traced = flag; }
    bool needsRuntimeAccess() const { return m_traced; }
    AstScope* refScopep() const { return m_refScopep; }
    void refScopep(AstScope* scopep) { m_refScopep = scopep; }
};

#endif  // Guard
