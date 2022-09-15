// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: AstNode sub-types representing data types
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// This files contains all 'AstNode' sub-types that relate to the
// representation of data types.
//
//*************************************************************************

#ifndef VERILATOR_V3ASTNODEDTYPE_H_
#define VERILATOR_V3ASTNODEDTYPE_H_

#ifndef VERILATOR_V3AST_H_
#error "Use V3Ast.h as the include"
#include "V3Ast.h"  // This helps code analysis tools pick up symbols in V3Ast.h
#define VL_NOT_FINAL  // This #define fixes broken code folding in the CLion IDE
#endif

// === Abstract base node types (AstNode*) =====================================

class AstNodeDType VL_NOT_FINAL : public AstNode {
    // Ideally width() would migrate to BasicDType as that's where it makes sense,
    // but it's currently so prevalent in the code we leave it here.
    // Note the below members are included in AstTypeTable::Key lookups
private:
    int m_width = 0;  // (also in AstTypeTable::Key) Bit width of operation
    int m_widthMin
        = 0;  // (also in AstTypeTable::Key) If unsized, bitwidth of minimum implementation
    VSigning m_numeric;  // (also in AstTypeTable::Key) Node is signed
    // Other members
    bool m_generic = false;  // Simple globally referenced type, don't garbage collect
    // Unique number assigned to each dtype during creation for IEEE matching
    static int s_uniqueNum;

protected:
    // CONSTRUCTORS
    AstNodeDType(VNType t, FileLine* fl)
        : AstNode{t, fl} {}

public:
    ASTNODE_BASE_FUNCS(NodeDType)
    // ACCESSORS
    virtual void dump(std::ostream& str) const override;
    virtual void dumpSmall(std::ostream& str) const;
    virtual bool hasDType() const override { return true; }
    /// Require VlUnpacked, instead of [] for POD elements.
    /// A non-POD object is always compound, but some POD elements
    /// are compound when methods calls operate on object, or when
    /// under another compound-requiring object e.g. class
    virtual bool isCompound() const = 0;
    // (Slow) recurse down to find basic data type
    virtual AstBasicDType* basicp() const = 0;
    // recurses over typedefs/const/enum to next non-typeref type
    virtual AstNodeDType* skipRefp() const = 0;
    // recurses over typedefs to next non-typeref-or-const type
    virtual AstNodeDType* skipRefToConstp() const = 0;
    // recurses over typedefs/const to next non-typeref-or-enum/struct type
    virtual AstNodeDType* skipRefToEnump() const = 0;
    // (Slow) recurses - Structure alignment 1,2,4 or 8 bytes (arrays affect this)
    virtual int widthAlignBytes() const = 0;
    // (Slow) recurses - Width in bytes rounding up 1,2,4,8,12,...
    virtual int widthTotalBytes() const = 0;
    virtual bool maybePointedTo() const override { return true; }
    // Iff has a non-null refDTypep(), as generic node function
    virtual AstNodeDType* virtRefDTypep() const { return nullptr; }
    // Iff has refDTypep(), set as generic node function
    virtual void virtRefDTypep(AstNodeDType* nodep) {}
    // Iff has a non-null second dtypep, as generic node function
    virtual AstNodeDType* virtRefDType2p() const { return nullptr; }
    // Iff has second dtype, set as generic node function
    virtual void virtRefDType2p(AstNodeDType* nodep) {}
    // Assignable equivalence.  Call skipRefp() on this and samep before calling
    virtual bool similarDType(AstNodeDType* samep) const = 0;
    // Iff has a non-null subDTypep(), as generic node function
    virtual AstNodeDType* subDTypep() const { return nullptr; }
    virtual bool isFourstate() const;
    // Ideally an IEEE $typename
    virtual string prettyDTypeName() const { return prettyTypeName(); }
    string prettyDTypeNameQ() const { return "'" + prettyDTypeName() + "'"; }
    //
    // Changing the width may confuse the data type resolution, so must clear
    // TypeTable cache after use.
    void widthForce(int width, int widthMin) {
        m_width = width;
        m_widthMin = widthMin;
    }
    // For backward compatibility inherit width and signing from the subDType/base type
    void widthFromSub(AstNodeDType* nodep) {
        m_width = nodep->m_width;
        m_widthMin = nodep->m_widthMin;
        m_numeric = nodep->m_numeric;
    }
    //
    int width() const { return m_width; }
    void numeric(VSigning flag) { m_numeric = flag; }
    bool isSigned() const { return m_numeric.isSigned(); }
    bool isNosign() const { return m_numeric.isNosign(); }
    VSigning numeric() const { return m_numeric; }
    int widthWords() const { return VL_WORDS_I(width()); }
    int widthMin() const {  // If sized, the size, if unsized the min digits to represent it
        return m_widthMin ? m_widthMin : m_width;
    }
    int widthPow2() const;
    void widthMinFromWidth() { m_widthMin = m_width; }
    bool widthSized() const { return !m_widthMin || m_widthMin == m_width; }
    bool generic() const { return m_generic; }
    void generic(bool flag) { m_generic = flag; }
    std::pair<uint32_t, uint32_t> dimensions(bool includeBasic);
    uint32_t arrayUnpackedElements();  // 1, or total multiplication of all dimensions
    static int uniqueNumInc() { return ++s_uniqueNum; }
    const char* charIQWN() const {
        return (isString() ? "N" : isWide() ? "W" : isQuad() ? "Q" : "I");
    }
    string cType(const string& name, bool forFunc, bool isRef) const;
    bool isLiteralType() const;  // Does this represent a C++ LiteralType? (can be constexpr)

private:
    class CTypeRecursed;
    CTypeRecursed cTypeRecurse(bool compound) const;
};
class AstNodeArrayDType VL_NOT_FINAL : public AstNodeDType {
    // Array data type, ie "some_dtype var_name [2:0]"
    // Children: DTYPE (moved to refDTypep() in V3Width)
    // Children: RANGE (array bounds)
private:
    AstNodeDType* m_refDTypep = nullptr;  // Elements of this type (after widthing)
    AstNode* rangenp() const { return op2p(); }  // op2 = Array(s) of variable
protected:
    AstNodeArrayDType(VNType t, FileLine* fl)
        : AstNodeDType{t, fl} {}

public:
    ASTNODE_BASE_FUNCS(NodeArrayDType)
    virtual void dump(std::ostream& str) const override;
    virtual void dumpSmall(std::ostream& str) const override;
    virtual const char* broken() const override {
        BROKEN_RTN(!((m_refDTypep && !childDTypep() && m_refDTypep->brokeExists())
                     || (!m_refDTypep && childDTypep())));
        return nullptr;
    }
    virtual void cloneRelink() override {
        if (m_refDTypep && m_refDTypep->clonep()) m_refDTypep = m_refDTypep->clonep();
    }
    virtual bool same(const AstNode* samep) const override {
        const AstNodeArrayDType* const asamep = static_cast<const AstNodeArrayDType*>(samep);
        return (hi() == asamep->hi() && subDTypep() == asamep->subDTypep()
                && rangenp()->sameTree(asamep->rangenp()));
    }  // HashedDT doesn't recurse, so need to check children
    virtual bool similarDType(AstNodeDType* samep) const override {
        const AstNodeArrayDType* const asamep = static_cast<const AstNodeArrayDType*>(samep);
        return (asamep && type() == samep->type() && hi() == asamep->hi()
                && rangenp()->sameTree(asamep->rangenp())
                && subDTypep()->skipRefp()->similarDType(asamep->subDTypep()->skipRefp()));
    }
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    AstNodeDType* childDTypep() const { return VN_AS(op1p(), NodeDType); }
    void childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    virtual AstNodeDType* subDTypep() const override {
        return m_refDTypep ? m_refDTypep : childDTypep();
    }
    void refDTypep(AstNodeDType* nodep) { m_refDTypep = nodep; }
    virtual AstNodeDType* virtRefDTypep() const override { return m_refDTypep; }
    virtual void virtRefDTypep(AstNodeDType* nodep) override { refDTypep(nodep); }
    AstRange* rangep() const { return VN_AS(op2p(), Range); }  // op2 = Array(s) of variable
    void rangep(AstRange* nodep);
    // METHODS
    virtual AstBasicDType* basicp() const override {
        return subDTypep()->basicp();
    }  // (Slow) recurse down to find basic data type
    virtual AstNodeDType* skipRefp() const override { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    virtual int widthAlignBytes() const override { return subDTypep()->widthAlignBytes(); }
    virtual int widthTotalBytes() const override {
        return elementsConst() * subDTypep()->widthTotalBytes();
    }
    int left() const;
    int right() const;
    int hi() const;
    int lo() const;
    int elementsConst() const;
    VNumRange declRange() const;
};
class AstNodeUOrStructDType VL_NOT_FINAL : public AstNodeDType {
    // A struct or union; common handling
private:
    // TYPES
    using MemberNameMap = std::map<const std::string, AstMemberDType*>;
    // MEMBERS
    string m_name;  // Name from upper typedef, if any
    bool m_packed;
    bool m_isFourstate = false;  // V3Width computes
    MemberNameMap m_members;
    const int m_uniqueNum;

protected:
    AstNodeUOrStructDType(VNType t, FileLine* fl, VSigning numericUnpack)
        : AstNodeDType{t, fl}
        , m_uniqueNum{uniqueNumInc()} {
        // VSigning::NOSIGN overloaded to indicate not packed
        m_packed = (numericUnpack != VSigning::NOSIGN);
        numeric(VSigning::fromBool(numericUnpack.isSigned()));
    }

public:
    ASTNODE_BASE_FUNCS(NodeUOrStructDType)
    int uniqueNum() const { return m_uniqueNum; }
    virtual const char* broken() const override;
    virtual void dump(std::ostream& str) const override;
    virtual bool isCompound() const override { return false; }  // Because don't support unpacked
    // For basicp() we reuse the size to indicate a "fake" basic type of same size
    virtual AstBasicDType* basicp() const override {
        return (isFourstate()
                    ? VN_AS(findLogicRangeDType(VNumRange{width() - 1, 0}, width(), numeric()),
                            BasicDType)
                    : VN_AS(findBitRangeDType(VNumRange{width() - 1, 0}, width(), numeric()),
                            BasicDType));
    }
    virtual AstNodeDType* skipRefp() const override { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    // (Slow) recurses - Structure alignment 1,2,4 or 8 bytes (arrays affect this)
    virtual int widthAlignBytes() const override;
    // (Slow) recurses - Width in bytes rounding up 1,2,4,8,12,...
    virtual int widthTotalBytes() const override;
    // op1 = members
    virtual bool similarDType(AstNodeDType* samep) const override {
        return this == samep;  // We don't compare members, require exact equivalence
    }
    virtual string name() const override { return m_name; }
    virtual void name(const string& flag) override { m_name = flag; }
    AstMemberDType* membersp() const {
        return VN_AS(op1p(), MemberDType);
    }  // op1 = AstMember list
    void addMembersp(AstNode* nodep) { addNOp1p(nodep); }
    bool packed() const { return m_packed; }
    // packed() but as don't support unpacked, presently all structs
    static bool packedUnsup() { return true; }
    void isFourstate(bool flag) { m_isFourstate = flag; }
    virtual bool isFourstate() const override { return m_isFourstate; }
    void clearCache() { m_members.clear(); }
    void repairMemberCache();
    AstMemberDType* findMember(const string& name) const {
        const auto it = m_members.find(name);
        return (it == m_members.end()) ? nullptr : it->second;
    }
    static int lo() { return 0; }
    int hi() const { return dtypep()->width() - 1; }  // Packed classes look like arrays
    VNumRange declRange() const { return VNumRange{hi(), lo()}; }
};

// === Concrete node types =====================================================

// === AstNode ===
class AstEnumItem final : public AstNode {
private:
    string m_name;

public:
    // Parents: ENUM
    AstEnumItem(FileLine* fl, const string& name, AstNode* rangep, AstNode* initp)
        : ASTGEN_SUPER_EnumItem(fl)
        , m_name{name} {
        addNOp1p(rangep);
        addNOp2p(initp);
    }
    ASTNODE_NODE_FUNCS(EnumItem)
    virtual string name() const override { return m_name; }
    virtual bool maybePointedTo() const override { return true; }
    virtual bool hasDType() const override { return true; }
    virtual void name(const string& flag) override { m_name = flag; }
    AstRange* rangep() const { return VN_AS(op1p(), Range); }  // op1 = Range for name appending
    void rangep(AstRange* nodep) { addOp1p((AstNode*)nodep); }
    AstNode* valuep() const { return op2p(); }  // op2 = Value
    void valuep(AstNode* nodep) { addOp2p(nodep); }
};

// === AstNodeDType ===
class AstAssocArrayDType final : public AstNodeDType {
    // Associative array data type, ie "[some_dtype]"
    // Children: DTYPE (moved to refDTypep() in V3Width)
    // Children: DTYPE (the key, which remains here as a pointer)
private:
    AstNodeDType* m_refDTypep;  // Elements of this type (after widthing)
    AstNodeDType* m_keyDTypep;  // Keys of this type (after widthing)
public:
    AstAssocArrayDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp, AstNodeDType* keyDtp)
        : ASTGEN_SUPER_AssocArrayDType(fl) {
        childDTypep(dtp);  // Only for parser
        keyChildDTypep(keyDtp);  // Only for parser
        refDTypep(nullptr);
        keyDTypep(nullptr);
        dtypep(nullptr);  // V3Width will resolve
    }
    AstAssocArrayDType(FileLine* fl, AstNodeDType* dtp, AstNodeDType* keyDtp)
        : ASTGEN_SUPER_AssocArrayDType(fl) {
        refDTypep(dtp);
        keyDTypep(keyDtp);
        dtypep(dtp);
    }
    ASTNODE_NODE_FUNCS(AssocArrayDType)
    virtual const char* broken() const override {
        BROKEN_RTN(!((m_refDTypep && !childDTypep() && m_refDTypep->brokeExists())
                     || (!m_refDTypep && childDTypep())));
        BROKEN_RTN(!((m_keyDTypep && !childDTypep() && m_keyDTypep->brokeExists())
                     || (!m_keyDTypep && childDTypep())));
        return nullptr;
    }
    virtual void cloneRelink() override {
        if (m_refDTypep && m_refDTypep->clonep()) m_refDTypep = m_refDTypep->clonep();
        if (m_keyDTypep && m_keyDTypep->clonep()) m_keyDTypep = m_keyDTypep->clonep();
    }
    virtual bool same(const AstNode* samep) const override {
        const AstAssocArrayDType* const asamep = static_cast<const AstAssocArrayDType*>(samep);
        if (!asamep->subDTypep()) return false;
        if (!asamep->keyDTypep()) return false;
        return (subDTypep() == asamep->subDTypep() && keyDTypep() == asamep->keyDTypep());
    }
    virtual bool similarDType(AstNodeDType* samep) const override {
        const AstAssocArrayDType* const asamep = static_cast<const AstAssocArrayDType*>(samep);
        return type() == samep->type() && asamep->subDTypep()
               && subDTypep()->skipRefp()->similarDType(asamep->subDTypep()->skipRefp());
    }
    virtual string prettyDTypeName() const override;
    virtual void dumpSmall(std::ostream& str) const override;
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    virtual AstNodeDType* getChild2DTypep() const override { return keyChildDTypep(); }
    // op1 = Range of variable
    AstNodeDType* childDTypep() const { return VN_AS(op1p(), NodeDType); }
    void childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    virtual AstNodeDType* subDTypep() const override {
        return m_refDTypep ? m_refDTypep : childDTypep();
    }
    void refDTypep(AstNodeDType* nodep) { m_refDTypep = nodep; }
    virtual AstNodeDType* virtRefDTypep() const override { return m_refDTypep; }
    virtual void virtRefDTypep(AstNodeDType* nodep) override { refDTypep(nodep); }
    virtual AstNodeDType* virtRefDType2p() const override { return m_keyDTypep; }
    virtual void virtRefDType2p(AstNodeDType* nodep) override { keyDTypep(nodep); }
    //
    AstNodeDType* keyDTypep() const { return m_keyDTypep ? m_keyDTypep : keyChildDTypep(); }
    void keyDTypep(AstNodeDType* nodep) { m_keyDTypep = nodep; }
    // op1 = Range of variable
    AstNodeDType* keyChildDTypep() const { return VN_AS(op2p(), NodeDType); }
    void keyChildDTypep(AstNodeDType* nodep) { setOp2p(nodep); }
    // METHODS
    virtual AstBasicDType* basicp() const override { return nullptr; }
    virtual AstNodeDType* skipRefp() const override { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    virtual int widthAlignBytes() const override { return subDTypep()->widthAlignBytes(); }
    virtual int widthTotalBytes() const override { return subDTypep()->widthTotalBytes(); }
    virtual bool isCompound() const override { return true; }
};
class AstBasicDType final : public AstNodeDType {
    // Builtin atomic/vectored data type
    // Children: RANGE (converted to constant in V3Width)
private:
    struct Members {
        VBasicDTypeKwd m_keyword;  // (also in VBasicTypeKey) What keyword created basic type
        VNumRange m_nrange;  // (also in VBasicTypeKey) Numeric msb/lsb (if non-opaque keyword)
        bool operator==(const Members& rhs) const {
            return rhs.m_keyword == m_keyword && rhs.m_nrange == m_nrange;
        }
    } m;
    // See also in AstNodeDType: m_width, m_widthMin, m_numeric(issigned)
public:
    AstBasicDType(FileLine* fl, VBasicDTypeKwd kwd, const VSigning& signst = VSigning::NOSIGN)
        : ASTGEN_SUPER_BasicDType(fl) {
        init(kwd, signst, 0, -1, nullptr);
    }
    AstBasicDType(FileLine* fl, VFlagLogicPacked, int wantwidth)
        : ASTGEN_SUPER_BasicDType(fl) {
        init(VBasicDTypeKwd::LOGIC, VSigning::NOSIGN, wantwidth, -1, nullptr);
    }
    AstBasicDType(FileLine* fl, VFlagBitPacked, int wantwidth)
        : ASTGEN_SUPER_BasicDType(fl) {
        init(VBasicDTypeKwd::BIT, VSigning::NOSIGN, wantwidth, -1, nullptr);
    }
    AstBasicDType(FileLine* fl, VBasicDTypeKwd kwd, VSigning numer, int wantwidth, int widthmin)
        : ASTGEN_SUPER_BasicDType(fl) {
        init(kwd, numer, wantwidth, widthmin, nullptr);
    }
    AstBasicDType(FileLine* fl, VBasicDTypeKwd kwd, VSigning numer, VNumRange range, int widthmin)
        : ASTGEN_SUPER_BasicDType(fl) {
        init(kwd, numer, range.elements(), widthmin, nullptr);
        m.m_nrange = range;  // as init() presumes lsb==0, but range.lsb() might not be
    }
    // See also addRange in verilog.y
private:
    void init(VBasicDTypeKwd kwd, VSigning numer, int wantwidth, int wantwidthmin,
              AstRange* rangep);

public:
    ASTNODE_NODE_FUNCS(BasicDType)
    virtual void dump(std::ostream& str) const override;
    // width/widthMin/numeric compared elsewhere
    virtual bool same(const AstNode* samep) const override {
        const AstBasicDType* const sp = static_cast<const AstBasicDType*>(samep);
        return m == sp->m;
    }
    virtual bool similarDType(AstNodeDType* samep) const override {
        return type() == samep->type() && same(samep);
    }
    virtual string name() const override { return m.m_keyword.ascii(); }
    virtual string prettyDTypeName() const override;
    virtual const char* broken() const override {
        BROKEN_RTN(dtypep() != this);
        return nullptr;
    }
    AstRange* rangep() const { return VN_AS(op1p(), Range); }  // op1 = Range of variable
    void rangep(AstRange* nodep) { setNOp1p((AstNode*)nodep); }
    void setSignedState(const VSigning& signst) {
        // Note NOSIGN does NOT change the state; this is required by the parser
        if (signst == VSigning::UNSIGNED) {
            numeric(signst);
        } else if (signst == VSigning::SIGNED) {
            numeric(signst);
        }
    }
    // METHODS
    virtual AstBasicDType* basicp() const override { return (AstBasicDType*)this; }
    virtual AstNodeDType* skipRefp() const override { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    // (Slow) recurses - Structure alignment 1,2,4 or 8 bytes (arrays affect this)
    virtual int widthAlignBytes() const override;
    // (Slow) recurses - Width in bytes rounding up 1,2,4,8,12,...
    virtual int widthTotalBytes() const override;
    virtual bool isFourstate() const override { return keyword().isFourstate(); }
    VBasicDTypeKwd keyword() const {  // Avoid using - use isSomething accessors instead
        return m.m_keyword;
    }
    bool isBitLogic() const { return keyword().isBitLogic(); }
    bool isDouble() const { return keyword().isDouble(); }
    bool isEventValue() const { return keyword().isEventValue(); }
    bool isOpaque() const { return keyword().isOpaque(); }
    bool isString() const { return keyword().isString(); }
    bool isZeroInit() const { return keyword().isZeroInit(); }
    bool isRanged() const { return rangep() || m.m_nrange.ranged(); }
    bool isDpiBitVec() const {  // DPI uses svBitVecVal
        return keyword() == VBasicDTypeKwd::BIT && isRanged();
    }
    bool isDpiLogicVec() const {  // DPI uses svLogicVecVal
        return keyword().isFourstate() && !(keyword() == VBasicDTypeKwd::LOGIC && !isRanged());
    }
    bool isDpiPrimitive() const {  // DPI uses a primitive type
        return !isDpiBitVec() && !isDpiLogicVec();
    }
    // Generally the lo/hi/left/right funcs should be used instead of nrange()
    const VNumRange& nrange() const { return m.m_nrange; }
    inline int hi() const;
    inline int lo() const;
    inline int elements() const;
    int left() const { return littleEndian() ? lo() : hi(); }  // How to show a declaration
    int right() const { return littleEndian() ? hi() : lo(); }
    inline bool littleEndian() const;
    bool implicit() const { return keyword() == VBasicDTypeKwd::LOGIC_IMPLICIT; }
    VNumRange declRange() const { return isRanged() ? VNumRange{left(), right()} : VNumRange{}; }
    void cvtRangeConst();  // Convert to smaller representation
    virtual bool isCompound() const override { return isString(); }
};
class AstBracketArrayDType final : public AstNodeDType {
    // Associative/Queue/Normal array data type, ie "[dtype_or_expr]"
    // only for early parsing then becomes another data type
    // Children: DTYPE (moved to refDTypep() in V3Width)
    // Children: DTYPE (the key)
public:
    AstBracketArrayDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp, AstNode* elementsp)
        : ASTGEN_SUPER_BracketArrayDType(fl) {
        setOp1p(dtp);  // Only for parser
        setOp2p(elementsp);  // Only for parser
    }
    ASTNODE_NODE_FUNCS(BracketArrayDType)
    virtual bool similarDType(AstNodeDType* samep) const override { V3ERROR_NA_RETURN(false); }
    // op1 = Range of variable
    AstNodeDType* childDTypep() const { return VN_AS(op1p(), NodeDType); }
    virtual AstNodeDType* subDTypep() const override { return childDTypep(); }
    // op2 = Range of variable
    AstNode* elementsp() const { return op2p(); }
    // METHODS
    // Will be removed in V3Width, which relies on this
    // being a child not a dtype pointed node
    virtual bool maybePointedTo() const override { return false; }
    virtual AstBasicDType* basicp() const override { return nullptr; }
    virtual AstNodeDType* skipRefp() const override { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    virtual int widthAlignBytes() const override { V3ERROR_NA_RETURN(0); }
    virtual int widthTotalBytes() const override { V3ERROR_NA_RETURN(0); }
    virtual bool isCompound() const override { return true; }
};
class AstClassRefDType final : public AstNodeDType {
    // Reference to a class
    // Children: PINs (for parameter settings)
private:
    AstClass* m_classp;  // data type pointed to, BELOW the AstTypedef
    AstNodeModule* m_classOrPackagep = nullptr;  // Package hierarchy
public:
    AstClassRefDType(FileLine* fl, AstClass* classp, AstNode* paramsp)
        : ASTGEN_SUPER_ClassRefDType(fl)
        , m_classp{classp} {
        dtypep(this);
        addNOp4p(paramsp);
    }
    ASTNODE_NODE_FUNCS(ClassRefDType)
    // METHODS
    const char* broken() const override;
    void cloneRelink() override;
    virtual bool same(const AstNode* samep) const override {
        const AstClassRefDType* const asamep = static_cast<const AstClassRefDType*>(samep);
        return (m_classp == asamep->m_classp && m_classOrPackagep == asamep->m_classOrPackagep);
    }
    virtual bool similarDType(AstNodeDType* samep) const override {
        return this == samep || (type() == samep->type() && same(samep));
    }
    virtual void dump(std::ostream& str = std::cout) const override;
    virtual void dumpSmall(std::ostream& str) const override;
    string name() const override;
    virtual AstBasicDType* basicp() const override { return nullptr; }
    virtual AstNodeDType* skipRefp() const override { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    virtual int widthAlignBytes() const override { return 0; }
    virtual int widthTotalBytes() const override { return 0; }
    virtual AstNodeDType* virtRefDTypep() const override { return nullptr; }
    virtual void virtRefDTypep(AstNodeDType* nodep) override {}
    virtual AstNodeDType* subDTypep() const override { return nullptr; }
    AstNodeModule* classOrPackagep() const { return m_classOrPackagep; }
    void classOrPackagep(AstNodeModule* nodep) { m_classOrPackagep = nodep; }
    AstClass* classp() const { return m_classp; }
    void classp(AstClass* nodep) { m_classp = nodep; }
    AstPin* paramsp() const { return VN_AS(op4p(), Pin); }
    virtual bool isCompound() const override { return true; }
};
class AstConstDType final : public AstNodeDType {
    // const data type, ie "const some_dtype var_name [2:0]"
    // ConstDType are removed in V3LinkLValue and become AstVar::isConst.
    // When more generic types are supported AstConstDType will be propagated further.
private:
    AstNodeDType* m_refDTypep = nullptr;  // Inherit from this base data type
public:
    AstConstDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp)
        : ASTGEN_SUPER_ConstDType(fl) {
        childDTypep(dtp);  // Only for parser
        refDTypep(nullptr);  // V3Width will resolve
        dtypep(nullptr);  // V3Width will resolve
        widthFromSub(subDTypep());
    }
    ASTNODE_NODE_FUNCS(ConstDType)
    virtual const char* broken() const override {
        BROKEN_RTN(!((m_refDTypep && !childDTypep() && m_refDTypep->brokeExists())
                     || (!m_refDTypep && childDTypep())));
        return nullptr;
    }
    virtual void cloneRelink() override {
        if (m_refDTypep && m_refDTypep->clonep()) m_refDTypep = m_refDTypep->clonep();
    }
    virtual bool same(const AstNode* samep) const override {
        const AstConstDType* const sp = static_cast<const AstConstDType*>(samep);
        return (m_refDTypep == sp->m_refDTypep);
    }
    virtual bool similarDType(AstNodeDType* samep) const override {
        return skipRefp()->similarDType(samep->skipRefp());
    }
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    // op1 = Range of variable
    AstNodeDType* childDTypep() const { return VN_AS(op1p(), NodeDType); }
    void childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    virtual AstNodeDType* subDTypep() const override {
        return m_refDTypep ? m_refDTypep : childDTypep();
    }
    void refDTypep(AstNodeDType* nodep) { m_refDTypep = nodep; }
    virtual AstNodeDType* virtRefDTypep() const override { return m_refDTypep; }
    virtual void virtRefDTypep(AstNodeDType* nodep) override { refDTypep(nodep); }
    // METHODS
    virtual AstBasicDType* basicp() const override { return subDTypep()->basicp(); }
    virtual AstNodeDType* skipRefp() const override { return subDTypep()->skipRefp(); }
    virtual AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToEnump() const override { return subDTypep()->skipRefToEnump(); }
    virtual int widthAlignBytes() const override { return subDTypep()->widthAlignBytes(); }
    virtual int widthTotalBytes() const override { return subDTypep()->widthTotalBytes(); }
    virtual bool isCompound() const override {
        v3fatalSrc("call isCompound on subdata type, not reference");
        return false;
    }
};
class AstDefImplicitDType final : public AstNodeDType {
    // For parsing enum/struct/unions that are declared with a variable rather than typedef
    // This allows "var enum {...} a,b" to share the enum definition for both variables
    // After link, these become typedefs
private:
    string m_name;
    void* m_containerp;  // In what scope is the name unique, so we can know what are duplicate
                         // definitions (arbitrary value)
    const int m_uniqueNum;

public:
    AstDefImplicitDType(FileLine* fl, const string& name, void* containerp, VFlagChildDType,
                        AstNodeDType* dtp)
        : ASTGEN_SUPER_DefImplicitDType(fl)
        , m_name{name}
        , m_containerp{containerp}
        , m_uniqueNum{uniqueNumInc()} {
        childDTypep(dtp);  // Only for parser
        dtypep(nullptr);  // V3Width will resolve
    }
    ASTNODE_NODE_FUNCS(DefImplicitDType)
    int uniqueNum() const { return m_uniqueNum; }
    virtual bool same(const AstNode* samep) const override {
        const AstDefImplicitDType* const sp = static_cast<const AstDefImplicitDType*>(samep);
        return uniqueNum() == sp->uniqueNum();
    }
    virtual bool similarDType(AstNodeDType* samep) const override {
        return type() == samep->type() && same(samep);
    }
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    // op1 = Range of variable
    AstNodeDType* childDTypep() const { return VN_AS(op1p(), NodeDType); }
    void childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    virtual AstNodeDType* subDTypep() const override {
        return dtypep() ? dtypep() : childDTypep();
    }
    void* containerp() const { return m_containerp; }
    // METHODS
    // op1 = Range of variable
    AstNodeDType* dtypeSkipRefp() const { return dtypep()->skipRefp(); }
    virtual AstBasicDType* basicp() const override { return subDTypep()->basicp(); }
    virtual AstNodeDType* skipRefp() const override { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    virtual int widthAlignBytes() const override { return dtypep()->widthAlignBytes(); }
    virtual int widthTotalBytes() const override { return dtypep()->widthTotalBytes(); }
    virtual string name() const override { return m_name; }
    virtual void name(const string& flag) override { m_name = flag; }
    virtual bool isCompound() const override { return false; }
};
class AstDynArrayDType final : public AstNodeDType {
    // Dynamic array data type, ie "[]"
    // Children: DTYPE (moved to refDTypep() in V3Width)
private:
    AstNodeDType* m_refDTypep = nullptr;  // Elements of this type (after widthing)
public:
    AstDynArrayDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp)
        : ASTGEN_SUPER_DynArrayDType(fl) {
        childDTypep(dtp);  // Only for parser
        refDTypep(nullptr);
        dtypep(nullptr);  // V3Width will resolve
    }
    AstDynArrayDType(FileLine* fl, AstNodeDType* dtp)
        : ASTGEN_SUPER_DynArrayDType(fl) {
        refDTypep(dtp);
        dtypep(nullptr);  // V3Width will resolve
    }
    ASTNODE_NODE_FUNCS(DynArrayDType)
    virtual const char* broken() const override {
        BROKEN_RTN(!((m_refDTypep && !childDTypep() && m_refDTypep->brokeExists())
                     || (!m_refDTypep && childDTypep())));
        return nullptr;
    }
    virtual void cloneRelink() override {
        if (m_refDTypep && m_refDTypep->clonep()) m_refDTypep = m_refDTypep->clonep();
    }
    virtual bool same(const AstNode* samep) const override {
        const AstAssocArrayDType* const asamep = static_cast<const AstAssocArrayDType*>(samep);
        if (!asamep->subDTypep()) return false;
        return subDTypep() == asamep->subDTypep();
    }
    virtual bool similarDType(AstNodeDType* samep) const override {
        const AstAssocArrayDType* const asamep = static_cast<const AstAssocArrayDType*>(samep);
        return type() == samep->type() && asamep->subDTypep()
               && subDTypep()->skipRefp()->similarDType(asamep->subDTypep()->skipRefp());
    }
    virtual string prettyDTypeName() const override;
    virtual void dumpSmall(std::ostream& str) const override;
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    // op1 = Range of variable
    AstNodeDType* childDTypep() const { return VN_AS(op1p(), NodeDType); }
    void childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    virtual AstNodeDType* subDTypep() const override {
        return m_refDTypep ? m_refDTypep : childDTypep();
    }
    void refDTypep(AstNodeDType* nodep) { m_refDTypep = nodep; }
    virtual AstNodeDType* virtRefDTypep() const override { return m_refDTypep; }
    virtual void virtRefDTypep(AstNodeDType* nodep) override { refDTypep(nodep); }
    // METHODS
    virtual AstBasicDType* basicp() const override { return nullptr; }
    virtual AstNodeDType* skipRefp() const override { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    virtual int widthAlignBytes() const override { return subDTypep()->widthAlignBytes(); }
    virtual int widthTotalBytes() const override { return subDTypep()->widthTotalBytes(); }
    virtual bool isCompound() const override { return true; }
};
class AstEmptyQueueDType final : public AstNodeDType {
    // For EmptyQueue
public:
    explicit AstEmptyQueueDType(FileLine* fl)
        : ASTGEN_SUPER_EmptyQueueDType(fl) {
        dtypep(this);
    }
    ASTNODE_NODE_FUNCS(EmptyQueueDType)
    virtual void dumpSmall(std::ostream& str) const override;
    virtual bool hasDType() const override { return true; }
    virtual bool maybePointedTo() const override { return true; }
    virtual bool undead() const override { return true; }
    virtual AstNodeDType* subDTypep() const override { return nullptr; }
    virtual AstNodeDType* virtRefDTypep() const override { return nullptr; }
    virtual void virtRefDTypep(AstNodeDType* nodep) override {}
    virtual bool similarDType(AstNodeDType* samep) const override { return this == samep; }
    virtual AstBasicDType* basicp() const override { return nullptr; }
    // cppcheck-suppress csyleCast
    virtual AstNodeDType* skipRefp() const override { return (AstNodeDType*)this; }
    // cppcheck-suppress csyleCast
    virtual AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    // cppcheck-suppress csyleCast
    virtual AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    virtual int widthAlignBytes() const override { return 1; }
    virtual int widthTotalBytes() const override { return 1; }
    virtual bool isCompound() const override { return false; }
};
class AstEnumDType final : public AstNodeDType {
    // Parents: TYPEDEF/MODULE
    // Children: ENUMVALUEs
private:
    string m_name;  // Name from upper typedef, if any
    AstNodeDType* m_refDTypep = nullptr;  // Elements are of this type after V3Width
    const int m_uniqueNum = 0;

public:
    AstEnumDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp, AstNode* itemsp)
        : ASTGEN_SUPER_EnumDType(fl)
        , m_uniqueNum{uniqueNumInc()} {
        childDTypep(dtp);  // Only for parser
        refDTypep(nullptr);
        addNOp2p(itemsp);
        dtypep(nullptr);  // V3Width will resolve
        widthFromSub(subDTypep());
    }
    ASTNODE_NODE_FUNCS(EnumDType)
    virtual const char* broken() const override {
        BROKEN_RTN(!((m_refDTypep && !childDTypep() && m_refDTypep->brokeExists())
                     || (!m_refDTypep && childDTypep())));
        return nullptr;
    }
    virtual void cloneRelink() override {
        if (m_refDTypep && m_refDTypep->clonep()) m_refDTypep = m_refDTypep->clonep();
    }
    int uniqueNum() const { return m_uniqueNum; }
    virtual bool same(const AstNode* samep) const override {
        const AstEnumDType* const sp = static_cast<const AstEnumDType*>(samep);
        return uniqueNum() == sp->uniqueNum();
    }
    virtual bool similarDType(AstNodeDType* samep) const override { return this == samep; }
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    AstNodeDType* childDTypep() const { return VN_AS(op1p(), NodeDType); }  // op1 = Data type
    void childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    // op1 = Range of variable
    virtual AstNodeDType* subDTypep() const override {
        return m_refDTypep ? m_refDTypep : childDTypep();
    }
    void refDTypep(AstNodeDType* nodep) { m_refDTypep = nodep; }
    virtual AstNodeDType* virtRefDTypep() const override { return m_refDTypep; }
    virtual void virtRefDTypep(AstNodeDType* nodep) override { refDTypep(nodep); }
    virtual string name() const override { return m_name; }
    virtual void name(const string& flag) override { m_name = flag; }
    AstEnumItem* itemsp() const { return VN_AS(op2p(), EnumItem); }  // op2 = AstEnumItem's
    // METHODS
    virtual AstBasicDType* basicp() const override { return subDTypep()->basicp(); }
    virtual AstNodeDType* skipRefp() const override { return subDTypep()->skipRefp(); }
    virtual AstNodeDType* skipRefToConstp() const override {
        return subDTypep()->skipRefToConstp();
    }
    // cppcheck-suppress csyleCast
    virtual AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    virtual int widthAlignBytes() const override { return subDTypep()->widthAlignBytes(); }
    virtual int widthTotalBytes() const override { return subDTypep()->widthTotalBytes(); }
    int itemCount() const {
        size_t count = 0;
        for (AstNode* itemp = itemsp(); itemp; itemp = itemp->nextp()) count++;
        return count;
    }
    virtual bool isCompound() const override { return false; }
};
class AstIfaceRefDType final : public AstNodeDType {
    // Reference to an interface, either for a port, or inside parent cell
private:
    FileLine* m_modportFileline;  // Where modport token was
    string m_cellName;  // "" = no cell, such as when connects to 'input' iface
    string m_ifaceName;  // Interface name
    string m_modportName;  // "" = no modport
    AstIface* m_ifacep = nullptr;  // Pointer to interface; note cellp() should override
    AstCell* m_cellp = nullptr;  // When exact parent cell known; not a guess
    AstModport* m_modportp = nullptr;  // nullptr = unlinked or no modport
public:
    AstIfaceRefDType(FileLine* fl, const string& cellName, const string& ifaceName)
        : ASTGEN_SUPER_IfaceRefDType(fl)
        , m_modportFileline{nullptr}
        , m_cellName{cellName}
        , m_ifaceName{ifaceName}
        , m_modportName{""} {}
    AstIfaceRefDType(FileLine* fl, FileLine* modportFl, const string& cellName,
                     const string& ifaceName, const string& modport)
        : ASTGEN_SUPER_IfaceRefDType(fl)
        , m_modportFileline{modportFl}
        , m_cellName{cellName}
        , m_ifaceName{ifaceName}
        , m_modportName{modport} {}
    ASTNODE_NODE_FUNCS(IfaceRefDType)
    // METHODS
    virtual const char* broken() const override;
    virtual void dump(std::ostream& str = std::cout) const override;
    virtual void dumpSmall(std::ostream& str) const override;
    virtual void cloneRelink() override;
    virtual AstBasicDType* basicp() const override { return nullptr; }
    virtual AstNodeDType* skipRefp() const override { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    virtual bool similarDType(AstNodeDType* samep) const override { return this == samep; }
    virtual int widthAlignBytes() const override { return 1; }
    virtual int widthTotalBytes() const override { return 1; }
    FileLine* modportFileline() const { return m_modportFileline; }
    string cellName() const { return m_cellName; }
    void cellName(const string& name) { m_cellName = name; }
    string ifaceName() const { return m_ifaceName; }
    void ifaceName(const string& name) { m_ifaceName = name; }
    string modportName() const { return m_modportName; }
    AstIface* ifaceViaCellp() const;  // Use cellp or ifacep
    AstIface* ifacep() const { return m_ifacep; }
    void ifacep(AstIface* nodep) { m_ifacep = nodep; }
    AstCell* cellp() const { return m_cellp; }
    void cellp(AstCell* nodep) { m_cellp = nodep; }
    AstModport* modportp() const { return m_modportp; }
    void modportp(AstModport* modportp) { m_modportp = modportp; }
    bool isModport() { return !m_modportName.empty(); }
    virtual bool isCompound() const override { return true; }  // But not relevant
};
class AstMemberDType final : public AstNodeDType {
    // A member of a struct/union
    // PARENT: AstNodeUOrStructDType
private:
    AstNodeDType* m_refDTypep = nullptr;  // Elements of this type (after widthing)
    string m_name;  // Name of variable
    string m_tag;  // Holds the string of the verilator tag -- used in XML output.
    int m_lsb = -1;  // Within this level's packed struct, the LSB of the first bit of the member
    // UNSUP: int m_randType;    // Randomization type (IEEE)
public:
    AstMemberDType(FileLine* fl, const string& name, VFlagChildDType, AstNodeDType* dtp)
        : ASTGEN_SUPER_MemberDType(fl)
        , m_name{name} {
        childDTypep(dtp);  // Only for parser
        dtypep(nullptr);  // V3Width will resolve
        refDTypep(nullptr);
    }
    AstMemberDType(FileLine* fl, const string& name, AstNodeDType* dtp)
        : ASTGEN_SUPER_MemberDType(fl)
        , m_name{name} {
        UASSERT(dtp, "AstMember created with no dtype");
        refDTypep(dtp);
        dtypep(this);
        widthFromSub(subDTypep());
    }
    ASTNODE_NODE_FUNCS(MemberDType)
    virtual string name() const override { return m_name; }  // * = Var name
    virtual bool hasDType() const override { return true; }
    virtual bool maybePointedTo() const override { return true; }
    virtual const char* broken() const override {
        BROKEN_RTN(m_refDTypep && !m_refDTypep->brokeExists());
        return nullptr;
    }
    virtual void cloneRelink() override {
        if (m_refDTypep && m_refDTypep->clonep()) m_refDTypep = m_refDTypep->clonep();
    }
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    // op1 = Range of variable
    AstNodeDType* childDTypep() const { return VN_AS(op1p(), NodeDType); }
    void childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    virtual AstNodeDType* subDTypep() const override {
        return m_refDTypep ? m_refDTypep : childDTypep();
    }
    void refDTypep(AstNodeDType* nodep) { m_refDTypep = nodep; }
    virtual AstNodeDType* virtRefDTypep() const override { return m_refDTypep; }
    virtual void virtRefDTypep(AstNodeDType* nodep) override { refDTypep(nodep); }
    virtual bool similarDType(AstNodeDType* samep) const override { return this == samep; }
    //
    // (Slow) recurse down to find basic data type (Note don't need virtual -
    // AstVar isn't a NodeDType)
    virtual AstBasicDType* basicp() const override { return subDTypep()->basicp(); }
    // op1 = Range of variable (Note don't need virtual - AstVar isn't a NodeDType)
    AstNodeDType* dtypeSkipRefp() const { return subDTypep()->skipRefp(); }
    virtual AstNodeDType* skipRefp() const override { return subDTypep()->skipRefp(); }
    virtual AstNodeDType* skipRefToConstp() const override {
        return subDTypep()->skipRefToConstp();
    }
    virtual AstNodeDType* skipRefToEnump() const override { return subDTypep()->skipRefToEnump(); }
    // (Slow) recurses - Structure alignment 1,2,4 or 8 bytes (arrays affect this)
    virtual int widthAlignBytes() const override { return subDTypep()->widthAlignBytes(); }
    // (Slow) recurses - Width in bytes rounding up 1,2,4,8,12,...
    virtual int widthTotalBytes() const override { return subDTypep()->widthTotalBytes(); }
    // METHODS
    virtual void name(const string& name) override { m_name = name; }
    virtual void tag(const string& text) override { m_tag = text; }
    virtual string tag() const override { return m_tag; }
    int lsb() const { return m_lsb; }
    void lsb(int lsb) { m_lsb = lsb; }
    virtual bool isCompound() const override {
        v3fatalSrc("call isCompound on subdata type, not reference");
        return false;
    }
};
class AstParamTypeDType final : public AstNodeDType {
    // Parents: MODULE
    // A parameter type statement; much like a var or typedef
private:
    const VVarType m_varType;  // Type of variable (for localparam vs. param)
    string m_name;  // Name of variable
public:
    AstParamTypeDType(FileLine* fl, VVarType type, const string& name, VFlagChildDType,
                      AstNodeDType* dtp)
        : ASTGEN_SUPER_ParamTypeDType(fl)
        , m_varType{type}
        , m_name{name} {
        childDTypep(dtp);  // Only for parser
        dtypep(nullptr);  // V3Width will resolve
    }
    ASTNODE_NODE_FUNCS(ParamTypeDType)
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    // op1 = Type assigning to
    AstNodeDType* childDTypep() const { return VN_AS(op1p(), NodeDType); }
    void childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    virtual AstNodeDType* subDTypep() const override {
        return dtypep() ? dtypep() : childDTypep();
    }
    virtual AstBasicDType* basicp() const override { return subDTypep()->basicp(); }
    virtual AstNodeDType* skipRefp() const override { return subDTypep()->skipRefp(); }
    virtual AstNodeDType* skipRefToConstp() const override {
        return subDTypep()->skipRefToConstp();
    }
    virtual AstNodeDType* skipRefToEnump() const override { return subDTypep()->skipRefToEnump(); }
    virtual bool similarDType(AstNodeDType* samep) const override {
        const AstParamTypeDType* const sp = static_cast<const AstParamTypeDType*>(samep);
        return type() == samep->type() && sp
               && this->subDTypep()->skipRefp()->similarDType(sp->subDTypep()->skipRefp());
    }
    virtual int widthAlignBytes() const override { return dtypep()->widthAlignBytes(); }
    virtual int widthTotalBytes() const override { return dtypep()->widthTotalBytes(); }
    // METHODS
    virtual string name() const override { return m_name; }
    virtual bool maybePointedTo() const override { return true; }
    virtual bool hasDType() const override { return true; }
    virtual void name(const string& flag) override { m_name = flag; }
    VVarType varType() const { return m_varType; }  // * = Type of variable
    bool isParam() const { return true; }
    bool isGParam() const { return (varType() == VVarType::GPARAM); }
    virtual bool isCompound() const override {
        v3fatalSrc("call isCompound on subdata type, not reference");
        return false;
    }
};
class AstParseTypeDType final : public AstNodeDType {
    // Parents: VAR
    // During parsing, this indicates the type of a parameter is a "parameter type"
    // e.g. the data type is a container of any data type
public:
    explicit AstParseTypeDType(FileLine* fl)
        : ASTGEN_SUPER_ParseTypeDType(fl) {}
    ASTNODE_NODE_FUNCS(ParseTypeDType)
    AstNodeDType* dtypep() const { return nullptr; }
    // METHODS
    virtual bool similarDType(AstNodeDType* samep) const override { return this == samep; }
    virtual AstBasicDType* basicp() const override { return nullptr; }
    virtual AstNodeDType* skipRefp() const override { return nullptr; }
    // cppcheck-suppress csyleCast
    virtual AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    // cppcheck-suppress csyleCast
    virtual AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    virtual int widthAlignBytes() const override { return 0; }
    virtual int widthTotalBytes() const override { return 0; }
    virtual bool isCompound() const override {
        v3fatalSrc("call isCompound on subdata type, not reference");
        return false;
    }
};
class AstQueueDType final : public AstNodeDType {
    // Queue array data type, ie "[ $ ]"
    // Children: DTYPE (moved to refDTypep() in V3Width)
private:
    AstNodeDType* m_refDTypep = nullptr;  // Elements of this type (after widthing)
public:
    AstQueueDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp, AstNode* boundp)
        : ASTGEN_SUPER_QueueDType(fl) {
        setNOp2p(boundp);
        childDTypep(dtp);  // Only for parser
        refDTypep(nullptr);
        dtypep(nullptr);  // V3Width will resolve
    }
    AstQueueDType(FileLine* fl, AstNodeDType* dtp, AstNode* boundp)
        : ASTGEN_SUPER_QueueDType(fl) {
        setNOp2p(boundp);
        refDTypep(dtp);
        dtypep(dtp);
    }
    ASTNODE_NODE_FUNCS(QueueDType)
    virtual const char* broken() const override {
        BROKEN_RTN(!((m_refDTypep && !childDTypep() && m_refDTypep->brokeExists())
                     || (!m_refDTypep && childDTypep())));
        return nullptr;
    }
    virtual void cloneRelink() override {
        if (m_refDTypep && m_refDTypep->clonep()) m_refDTypep = m_refDTypep->clonep();
    }
    virtual bool same(const AstNode* samep) const override {
        const AstQueueDType* const asamep = static_cast<const AstQueueDType*>(samep);
        if (!asamep->subDTypep()) return false;
        return (subDTypep() == asamep->subDTypep());
    }
    virtual bool similarDType(AstNodeDType* samep) const override {
        const AstQueueDType* const asamep = static_cast<const AstQueueDType*>(samep);
        return type() == samep->type() && asamep->subDTypep()
               && subDTypep()->skipRefp()->similarDType(asamep->subDTypep()->skipRefp());
    }
    virtual void dumpSmall(std::ostream& str) const override;
    virtual string prettyDTypeName() const override;
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    // op1 = Range of variable
    AstNodeDType* childDTypep() const { return VN_AS(op1p(), NodeDType); }
    void childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    virtual AstNodeDType* subDTypep() const override {
        return m_refDTypep ? m_refDTypep : childDTypep();
    }
    void refDTypep(AstNodeDType* nodep) { m_refDTypep = nodep; }
    AstNode* boundp() const { return op2p(); }  // op2 = Bound, nullptr = none
    void boundp(AstNode* nodep) { setNOp2p(nodep); }
    inline int boundConst() const;
    virtual AstNodeDType* virtRefDTypep() const override { return m_refDTypep; }
    virtual void virtRefDTypep(AstNodeDType* nodep) override { refDTypep(nodep); }
    // METHODS
    virtual AstBasicDType* basicp() const override { return nullptr; }
    // cppcheck-suppress csyleCast
    virtual AstNodeDType* skipRefp() const override { return (AstNodeDType*)this; }
    // cppcheck-suppress csyleCast
    virtual AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    // cppcheck-suppress csyleCast
    virtual AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    virtual int widthAlignBytes() const override { return subDTypep()->widthAlignBytes(); }
    virtual int widthTotalBytes() const override { return subDTypep()->widthTotalBytes(); }
    virtual bool isCompound() const override { return true; }
};
class AstRefDType final : public AstNodeDType {
private:
    // Pre-Width must reference the Typeref, not what it points to, as some child
    // types like AstBracketArrayType will disappear and can't lose the handle
    AstTypedef* m_typedefp = nullptr;  // referenced type
    // Post-width typedefs are removed and point to type directly
    AstNodeDType* m_refDTypep = nullptr;  // data type pointed to, BELOW the AstTypedef
    string m_name;  // Name of an AstTypedef
    AstNodeModule* m_classOrPackagep = nullptr;  // Package hierarchy
public:
    AstRefDType(FileLine* fl, const string& name)
        : ASTGEN_SUPER_RefDType(fl)
        , m_name{name} {}
    AstRefDType(FileLine* fl, const string& name, AstNode* classOrPackagep, AstNode* paramsp)
        : ASTGEN_SUPER_RefDType(fl)
        , m_name{name} {
        setNOp3p(classOrPackagep);
        addNOp4p(paramsp);
    }
    class FlagTypeOfExpr {};  // type(expr) for parser only
    AstRefDType(FileLine* fl, FlagTypeOfExpr, AstNode* typeofp)
        : ASTGEN_SUPER_RefDType(fl) {
        setOp2p(typeofp);
    }
    ASTNODE_NODE_FUNCS(RefDType)
    // METHODS
    const char* broken() const override;
    void cloneRelink() override;
    virtual bool same(const AstNode* samep) const override {
        const AstRefDType* const asamep = static_cast<const AstRefDType*>(samep);
        return (m_typedefp == asamep->m_typedefp && m_refDTypep == asamep->m_refDTypep
                && m_name == asamep->m_name && m_classOrPackagep == asamep->m_classOrPackagep);
    }
    virtual bool similarDType(AstNodeDType* samep) const override {
        return skipRefp()->similarDType(samep->skipRefp());
    }
    virtual void dump(std::ostream& str = std::cout) const override;
    virtual string name() const override { return m_name; }
    virtual string prettyDTypeName() const override {
        return subDTypep() ? subDTypep()->name() : prettyName();
    }
    virtual AstBasicDType* basicp() const override {
        return subDTypep() ? subDTypep()->basicp() : nullptr;
    }
    AstNodeDType* subDTypep() const override;
    virtual AstNodeDType* skipRefp() const override {
        // Skip past both the Ref and the Typedef
        if (subDTypep()) {
            return subDTypep()->skipRefp();
        } else {
            v3fatalSrc("Typedef not linked");
            return nullptr;
        }
    }
    virtual AstNodeDType* skipRefToConstp() const override {
        if (subDTypep()) {
            return subDTypep()->skipRefToConstp();
        } else {
            v3fatalSrc("Typedef not linked");
            return nullptr;
        }
    }
    virtual AstNodeDType* skipRefToEnump() const override {
        if (subDTypep()) {
            return subDTypep()->skipRefToEnump();
        } else {
            v3fatalSrc("Typedef not linked");
            return nullptr;
        }
    }
    virtual int widthAlignBytes() const override { return dtypeSkipRefp()->widthAlignBytes(); }
    virtual int widthTotalBytes() const override { return dtypeSkipRefp()->widthTotalBytes(); }
    virtual void name(const string& flag) override { m_name = flag; }
    // op1 = Range of variable
    AstNodeDType* dtypeSkipRefp() const { return subDTypep()->skipRefp(); }
    AstTypedef* typedefp() const { return m_typedefp; }
    void typedefp(AstTypedef* nodep) { m_typedefp = nodep; }
    AstNodeDType* refDTypep() const { return m_refDTypep; }
    void refDTypep(AstNodeDType* nodep) { m_refDTypep = nodep; }
    virtual AstNodeDType* virtRefDTypep() const override { return refDTypep(); }
    virtual void virtRefDTypep(AstNodeDType* nodep) override { refDTypep(nodep); }
    AstNodeModule* classOrPackagep() const { return m_classOrPackagep; }
    void classOrPackagep(AstNodeModule* nodep) { m_classOrPackagep = nodep; }
    AstNode* typeofp() const { return op2p(); }
    AstNode* classOrPackageOpp() const { return op3p(); }
    AstPin* paramsp() const { return VN_AS(op4p(), Pin); }
    virtual bool isCompound() const override {
        v3fatalSrc("call isCompound on subdata type, not reference");
        return false;
    }
};
class AstUnsizedArrayDType final : public AstNodeDType {
    // Unsized/open-range Array data type, ie "some_dtype var_name []"
    // Children: DTYPE (moved to refDTypep() in V3Width)
private:
    AstNodeDType* m_refDTypep;  // Elements of this type (after widthing)
public:
    AstUnsizedArrayDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp)
        : ASTGEN_SUPER_UnsizedArrayDType(fl) {
        childDTypep(dtp);  // Only for parser
        refDTypep(nullptr);
        dtypep(nullptr);  // V3Width will resolve
    }
    ASTNODE_NODE_FUNCS(UnsizedArrayDType)
    virtual const char* broken() const override {
        BROKEN_RTN(!((m_refDTypep && !childDTypep() && m_refDTypep->brokeExists())
                     || (!m_refDTypep && childDTypep())));
        return nullptr;
    }
    virtual void cloneRelink() override {
        if (m_refDTypep && m_refDTypep->clonep()) m_refDTypep = m_refDTypep->clonep();
    }
    bool same(const AstNode* samep) const override;
    bool similarDType(AstNodeDType* samep) const override;
    virtual void dumpSmall(std::ostream& str) const override;
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    // op1 = Range of variable
    AstNodeDType* childDTypep() const { return VN_AS(op1p(), NodeDType); }
    void childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    virtual AstNodeDType* subDTypep() const override {
        return m_refDTypep ? m_refDTypep : childDTypep();
    }
    void refDTypep(AstNodeDType* nodep) { m_refDTypep = nodep; }
    virtual AstNodeDType* virtRefDTypep() const override { return m_refDTypep; }
    virtual void virtRefDTypep(AstNodeDType* nodep) override { refDTypep(nodep); }
    // METHODS
    virtual AstBasicDType* basicp() const override { return subDTypep()->basicp(); }
    virtual AstNodeDType* skipRefp() const override { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    virtual int widthAlignBytes() const override { return subDTypep()->widthAlignBytes(); }
    virtual int widthTotalBytes() const override { return subDTypep()->widthTotalBytes(); }
    virtual bool isCompound() const override { return true; }
};
class AstVoidDType final : public AstNodeDType {
    // For e.g. a function returning void
public:
    explicit AstVoidDType(FileLine* fl)
        : ASTGEN_SUPER_VoidDType(fl) {
        dtypep(this);
    }
    ASTNODE_NODE_FUNCS(VoidDType)
    virtual void dumpSmall(std::ostream& str) const override;
    virtual bool hasDType() const override { return true; }
    virtual bool maybePointedTo() const override { return true; }
    virtual bool undead() const override { return true; }
    virtual AstNodeDType* subDTypep() const override { return nullptr; }
    virtual AstNodeDType* virtRefDTypep() const override { return nullptr; }
    virtual void virtRefDTypep(AstNodeDType* nodep) override {}
    virtual bool similarDType(AstNodeDType* samep) const override { return this == samep; }
    virtual AstBasicDType* basicp() const override { return nullptr; }
    // cppcheck-suppress csyleCast
    virtual AstNodeDType* skipRefp() const override { return (AstNodeDType*)this; }
    // cppcheck-suppress csyleCast
    virtual AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    // cppcheck-suppress csyleCast
    virtual AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    virtual int widthAlignBytes() const override { return 1; }
    virtual int widthTotalBytes() const override { return 1; }
    virtual bool isCompound() const override { return false; }
};
class AstWildcardArrayDType final : public AstNodeDType {
    // Wildcard index type associative array data type, ie "some_dtype var_name [*]"
    // Children: DTYPE (moved to refDTypep() in V3Width)
private:
    AstNodeDType* m_refDTypep;  // Elements of this type (after widthing)
public:
    AstWildcardArrayDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp)
        : ASTGEN_SUPER_WildcardArrayDType(fl) {
        childDTypep(dtp);  // Only for parser
        refDTypep(nullptr);
        dtypep(nullptr);  // V3Width will resolve
    }
    ASTNODE_NODE_FUNCS(WildcardArrayDType)
    virtual const char* broken() const override {
        BROKEN_RTN(!((m_refDTypep && !childDTypep() && m_refDTypep->brokeExists())
                     || (!m_refDTypep && childDTypep())));
        return nullptr;
    }
    virtual void cloneRelink() override {
        if (m_refDTypep && m_refDTypep->clonep()) m_refDTypep = m_refDTypep->clonep();
    }
    bool same(const AstNode* samep) const override;
    bool similarDType(AstNodeDType* samep) const override;
    virtual void dumpSmall(std::ostream& str) const override;
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    // op1 = Range of variable
    AstNodeDType* childDTypep() const { return VN_AS(op1p(), NodeDType); }
    void childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    virtual AstNodeDType* subDTypep() const override {
        return m_refDTypep ? m_refDTypep : childDTypep();
    }
    void refDTypep(AstNodeDType* nodep) { m_refDTypep = nodep; }
    virtual AstNodeDType* virtRefDTypep() const override { return m_refDTypep; }
    virtual void virtRefDTypep(AstNodeDType* nodep) override { refDTypep(nodep); }
    // METHODS
    virtual AstBasicDType* basicp() const override { return subDTypep()->basicp(); }
    virtual AstNodeDType* skipRefp() const override { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    virtual int widthAlignBytes() const override {
        return sizeof(std::map<std::string, std::string>);
    }
    virtual int widthTotalBytes() const override {
        return sizeof(std::map<std::string, std::string>);
    }
    virtual bool isCompound() const override { return true; }
};

// === AstNodeArrayDType ===
class AstPackArrayDType final : public AstNodeArrayDType {
    // Packed array data type, ie "some_dtype [2:0] var_name"
    // Children: DTYPE (moved to refDTypep() in V3Width)
    // Children: RANGE (array bounds)
public:
    inline AstPackArrayDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp, AstRange* rangep);
    inline AstPackArrayDType(FileLine* fl, AstNodeDType* dtp, AstRange* rangep);
    ASTNODE_NODE_FUNCS(PackArrayDType)
    virtual string prettyDTypeName() const override;
    virtual bool isCompound() const override { return false; }
};
class AstUnpackArrayDType final : public AstNodeArrayDType {
    // Array data type, ie "some_dtype var_name [2:0]"
    // Children: DTYPE (moved to refDTypep() in V3Width)
    // Children: RANGE (array bounds)
    bool m_isCompound = false;  // Non-POD subDType, or parent requires compound
public:
    AstUnpackArrayDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp, AstRange* rangep)
        : ASTGEN_SUPER_UnpackArrayDType(fl) {
        childDTypep(dtp);  // Only for parser
        refDTypep(nullptr);
        setOp2p((AstNode*)rangep);
        dtypep(nullptr);  // V3Width will resolve
        // For backward compatibility AstNodeArrayDType and others inherit
        // width and signing from the subDType/base type
        widthFromSub(subDTypep());
    }
    AstUnpackArrayDType(FileLine* fl, AstNodeDType* dtp, AstRange* rangep)
        : ASTGEN_SUPER_UnpackArrayDType(fl) {
        refDTypep(dtp);
        setOp2p((AstNode*)rangep);
        dtypep(this);
        // For backward compatibility AstNodeArrayDType and others inherit
        // width and signing from the subDType/base type
        widthFromSub(subDTypep());
    }
    ASTNODE_NODE_FUNCS(UnpackArrayDType)
    virtual string prettyDTypeName() const override;
    virtual bool same(const AstNode* samep) const override {
        const AstUnpackArrayDType* const sp = static_cast<const AstUnpackArrayDType*>(samep);
        return m_isCompound == sp->m_isCompound;
    }
    // Outer dimension comes first. The first element is this node.
    std::vector<AstUnpackArrayDType*> unpackDimensions();
    void isCompound(bool flag) { m_isCompound = flag; }
    virtual bool isCompound() const override { return m_isCompound; }
};

// === AstNodeUOrStructDType ===
class AstStructDType final : public AstNodeUOrStructDType {
public:
    // VSigning below is mispurposed to indicate if packed or not
    AstStructDType(FileLine* fl, VSigning numericUnpack)
        : ASTGEN_SUPER_StructDType(fl, numericUnpack) {}
    ASTNODE_NODE_FUNCS(StructDType)
    virtual string verilogKwd() const override { return "struct"; }
};
class AstUnionDType final : public AstNodeUOrStructDType {
public:
    // UNSUP: bool isTagged;
    // VSigning below is mispurposed to indicate if packed or not
    AstUnionDType(FileLine* fl, VSigning numericUnpack)
        : ASTGEN_SUPER_UnionDType(fl, numericUnpack) {}
    ASTNODE_NODE_FUNCS(UnionDType)
    virtual string verilogKwd() const override { return "union"; }
};

#endif  // Guard
