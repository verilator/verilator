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
    ASTGEN_MEMBERS_AstNodeDType;
    // ACCESSORS
    void dump(std::ostream& str) const override;
    virtual void dumpSmall(std::ostream& str) const;
    bool hasDType() const override { return true; }
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
    bool maybePointedTo() const override { return true; }
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
    void widthFromSub(const AstNodeDType* nodep) {
        m_width = nodep->m_width;
        m_widthMin = nodep->m_widthMin;
        m_numeric = nodep->m_numeric;
    }
    //
    int width() const VL_MT_SAFE { return m_width; }
    void numeric(VSigning flag) { m_numeric = flag; }
    bool isSigned() const VL_MT_SAFE { return m_numeric.isSigned(); }
    bool isNosign() const VL_MT_SAFE { return m_numeric.isNosign(); }
    VSigning numeric() const { return m_numeric; }
    int widthWords() const VL_MT_SAFE { return VL_WORDS_I(width()); }
    int widthMin() const VL_MT_SAFE {  // If sized, the size,
                                       // if unsized the min digits to represent it
        return m_widthMin ? m_widthMin : m_width;
    }
    int widthPow2() const;
    void widthMinFromWidth() { m_widthMin = m_width; }
    bool widthSized() const VL_MT_SAFE { return !m_widthMin || m_widthMin == m_width; }
    bool generic() const VL_MT_SAFE { return m_generic; }
    void generic(bool flag) { m_generic = flag; }
    std::pair<uint32_t, uint32_t> dimensions(bool includeBasic);
    uint32_t arrayUnpackedElements();  // 1, or total multiplication of all dimensions
    static int uniqueNumInc() { return ++s_uniqueNum; }
    const char* charIQWN() const {
        return (isString() ? "N" : isWide() ? "W" : isQuad() ? "Q" : "I");
    }
    string cType(const string& name, bool forFunc, bool isRef) const VL_MT_SAFE;
    bool isLiteralType() const VL_MT_SAFE;  // Represents a C++ LiteralType? (can be constexpr)

private:
    class CTypeRecursed;
    CTypeRecursed cTypeRecurse(bool compound) const VL_MT_SAFE;
};
class AstNodeArrayDType VL_NOT_FINAL : public AstNodeDType {
    // Array data type, ie "some_dtype var_name [2:0]"
    // @astgen op1 := childDTypep : Optional[AstNodeDType] // moved to refDTypep() in V3Width
    // @astgen op2 := rangep : Optional[AstRange] // array bounds
private:
    AstNodeDType* m_refDTypep = nullptr;  // Elements of this type (after widthing)

    AstNode* rangenp() const { return reinterpret_cast<AstNode*>(rangep()); }

protected:
    AstNodeArrayDType(VNType t, FileLine* fl)
        : AstNodeDType{t, fl} {}

public:
    ASTGEN_MEMBERS_AstNodeArrayDType;
    void dump(std::ostream& str) const override;
    void dumpSmall(std::ostream& str) const override;
    const char* broken() const override {
        BROKEN_RTN(!((m_refDTypep && !childDTypep() && m_refDTypep->brokeExists())
                     || (!m_refDTypep && childDTypep())));
        return nullptr;
    }
    void cloneRelink() override {
        if (m_refDTypep && m_refDTypep->clonep()) m_refDTypep = m_refDTypep->clonep();
    }
    bool same(const AstNode* samep) const override {
        const AstNodeArrayDType* const asamep = static_cast<const AstNodeArrayDType*>(samep);
        return (hi() == asamep->hi() && subDTypep() == asamep->subDTypep()
                && rangenp()->sameTree(asamep->rangenp()));
    }  // HashedDT doesn't recurse, so need to check children
    bool similarDType(AstNodeDType* samep) const override {
        const AstNodeArrayDType* const asamep = static_cast<const AstNodeArrayDType*>(samep);
        return (asamep && type() == samep->type() && hi() == asamep->hi()
                && rangenp()->sameTree(asamep->rangenp())
                && subDTypep()->skipRefp()->similarDType(asamep->subDTypep()->skipRefp()));
    }
    AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    AstNodeDType* subDTypep() const override VL_MT_SAFE {
        return m_refDTypep ? m_refDTypep : childDTypep();
    }
    void refDTypep(AstNodeDType* nodep) { m_refDTypep = nodep; }
    AstNodeDType* virtRefDTypep() const override { return m_refDTypep; }
    void virtRefDTypep(AstNodeDType* nodep) override { refDTypep(nodep); }
    // METHODS
    AstBasicDType* basicp() const override VL_MT_SAFE {
        return subDTypep()->basicp();
    }  // (Slow) recurse down to find basic data type
    AstNodeDType* skipRefp() const override VL_MT_SAFE { return (AstNodeDType*)this; }
    AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    int widthAlignBytes() const override { return subDTypep()->widthAlignBytes(); }
    int widthTotalBytes() const override {
        return elementsConst() * subDTypep()->widthTotalBytes();
    }
    inline int left() const;
    inline int right() const;
    inline int hi() const;
    inline int lo() const;
    inline int elementsConst() const;
    inline VNumRange declRange() const;
};
class AstNodeUOrStructDType VL_NOT_FINAL : public AstNodeDType {
    // A struct or union; common handling
    // @astgen op1 := membersp : List[AstMemberDType]
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
    ASTGEN_MEMBERS_AstNodeUOrStructDType;
    int uniqueNum() const { return m_uniqueNum; }
    const char* broken() const override;
    void dump(std::ostream& str) const override;
    bool isCompound() const override { return false; }  // Because don't support unpacked
    // For basicp() we reuse the size to indicate a "fake" basic type of same size
    AstBasicDType* basicp() const override {
        return (isFourstate()
                    ? VN_AS(findLogicRangeDType(VNumRange{width() - 1, 0}, width(), numeric()),
                            BasicDType)
                    : VN_AS(findBitRangeDType(VNumRange{width() - 1, 0}, width(), numeric()),
                            BasicDType));
    }
    AstNodeDType* skipRefp() const override VL_MT_SAFE { return (AstNodeDType*)this; }
    AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    // (Slow) recurses - Structure alignment 1,2,4 or 8 bytes (arrays affect this)
    int widthAlignBytes() const override;
    // (Slow) recurses - Width in bytes rounding up 1,2,4,8,12,...
    int widthTotalBytes() const override;
    bool similarDType(AstNodeDType* samep) const override {
        return this == samep;  // We don't compare members, require exact equivalence
    }
    string name() const override { return m_name; }
    void name(const string& flag) override { m_name = flag; }
    bool packed() const VL_MT_SAFE { return m_packed; }
    // packed() but as don't support unpacked, presently all structs
    static bool packedUnsup() { return true; }
    void isFourstate(bool flag) { m_isFourstate = flag; }
    bool isFourstate() const override { return m_isFourstate; }
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
    // @astgen op1 := rangep : Optional[AstRange] // Range for name appending
    // @astgen op2 := valuep : Optional[AstNode]
private:
    string m_name;

public:
    // Parents: ENUM
    AstEnumItem(FileLine* fl, const string& name, AstRange* rangep, AstNode* valuep)
        : ASTGEN_SUPER_EnumItem(fl)
        , m_name{name} {
        this->rangep(rangep);
        this->valuep(valuep);
    }
    ASTGEN_MEMBERS_AstEnumItem;
    string name() const override { return m_name; }
    bool maybePointedTo() const override { return true; }
    bool hasDType() const override { return true; }
    void name(const string& flag) override { m_name = flag; }
};

// === AstNodeDType ===
class AstAssocArrayDType final : public AstNodeDType {
    // Associative array data type, ie "[some_dtype]"
    // @astgen op1 := childDTypep : Optional[AstNodeDType] // moved to refDTypep() in V3Width
    // @astgen op2 := keyChildDTypep : Optional[AstNodeDType]
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
    ASTGEN_MEMBERS_AstAssocArrayDType;
    const char* broken() const override {
        BROKEN_RTN(!((m_refDTypep && !childDTypep() && m_refDTypep->brokeExists())
                     || (!m_refDTypep && childDTypep())));
        BROKEN_RTN(!((m_keyDTypep && !childDTypep() && m_keyDTypep->brokeExists())
                     || (!m_keyDTypep && childDTypep())));
        return nullptr;
    }
    void cloneRelink() override {
        if (m_refDTypep && m_refDTypep->clonep()) m_refDTypep = m_refDTypep->clonep();
        if (m_keyDTypep && m_keyDTypep->clonep()) m_keyDTypep = m_keyDTypep->clonep();
    }
    bool same(const AstNode* samep) const override {
        const AstAssocArrayDType* const asamep = static_cast<const AstAssocArrayDType*>(samep);
        if (!asamep->subDTypep()) return false;
        if (!asamep->keyDTypep()) return false;
        return (subDTypep() == asamep->subDTypep() && keyDTypep() == asamep->keyDTypep());
    }
    bool similarDType(AstNodeDType* samep) const override {
        const AstAssocArrayDType* const asamep = static_cast<const AstAssocArrayDType*>(samep);
        return type() == samep->type() && asamep->subDTypep()
               && subDTypep()->skipRefp()->similarDType(asamep->subDTypep()->skipRefp());
    }
    string prettyDTypeName() const override;
    void dumpSmall(std::ostream& str) const override;
    AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    AstNodeDType* getChild2DTypep() const override { return keyChildDTypep(); }
    AstNodeDType* subDTypep() const override VL_MT_SAFE {
        return m_refDTypep ? m_refDTypep : childDTypep();
    }
    void refDTypep(AstNodeDType* nodep) { m_refDTypep = nodep; }
    AstNodeDType* virtRefDTypep() const override { return m_refDTypep; }
    void virtRefDTypep(AstNodeDType* nodep) override { refDTypep(nodep); }
    AstNodeDType* virtRefDType2p() const override { return m_keyDTypep; }
    void virtRefDType2p(AstNodeDType* nodep) override { keyDTypep(nodep); }
    //
    AstNodeDType* keyDTypep() const VL_MT_SAFE {
        return m_keyDTypep ? m_keyDTypep : keyChildDTypep();
    }
    void keyDTypep(AstNodeDType* nodep) { m_keyDTypep = nodep; }
    // METHODS
    AstBasicDType* basicp() const override VL_MT_SAFE { return nullptr; }
    AstNodeDType* skipRefp() const override VL_MT_SAFE { return (AstNodeDType*)this; }
    AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    int widthAlignBytes() const override { return subDTypep()->widthAlignBytes(); }
    int widthTotalBytes() const override { return subDTypep()->widthTotalBytes(); }
    bool isCompound() const override { return true; }
};
class AstBasicDType final : public AstNodeDType {
    // Builtin atomic/vectored data type
    // @astgen op1 := rangep : Optional[AstRange] // Range of variable
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
    ASTGEN_MEMBERS_AstBasicDType;
    void dump(std::ostream& str) const override;
    // width/widthMin/numeric compared elsewhere
    bool same(const AstNode* samep) const override {
        const AstBasicDType* const sp = static_cast<const AstBasicDType*>(samep);
        return m == sp->m;
    }
    bool similarDType(AstNodeDType* samep) const override {
        return type() == samep->type() && same(samep);
    }
    string name() const override { return m.m_keyword.ascii(); }
    string prettyDTypeName() const override;
    const char* broken() const override {
        BROKEN_RTN(dtypep() != this);
        return nullptr;
    }
    void setSignedState(const VSigning& signst) {
        // Note NOSIGN does NOT change the state; this is required by the parser
        if (signst == VSigning::UNSIGNED) {
            numeric(signst);
        } else if (signst == VSigning::SIGNED) {
            numeric(signst);
        }
    }
    // METHODS
    AstBasicDType* basicp() const override VL_MT_SAFE { return (AstBasicDType*)this; }
    AstNodeDType* skipRefp() const override VL_MT_SAFE { return (AstNodeDType*)this; }
    AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    // (Slow) recurses - Structure alignment 1,2,4 or 8 bytes (arrays affect this)
    int widthAlignBytes() const override;
    // (Slow) recurses - Width in bytes rounding up 1,2,4,8,12,...
    int widthTotalBytes() const override;
    bool isFourstate() const override { return keyword().isFourstate(); }
    VBasicDTypeKwd keyword() const VL_MT_SAFE {  // Avoid using - use isSomething accessors instead
        return m.m_keyword;
    }
    bool isBitLogic() const { return keyword().isBitLogic(); }
    bool isDouble() const VL_MT_SAFE { return keyword().isDouble(); }
    bool isEvent() const VL_MT_SAFE { return keyword() == VBasicDTypeKwd::EVENT; }
    bool isTriggerVec() const VL_MT_SAFE { return keyword() == VBasicDTypeKwd::TRIGGERVEC; }
    bool isForkSync() const VL_MT_SAFE { return keyword() == VBasicDTypeKwd::FORK_SYNC; }
    bool isDelayScheduler() const VL_MT_SAFE {
        return keyword() == VBasicDTypeKwd::DELAY_SCHEDULER;
    }
    bool isTriggerScheduler() const VL_MT_SAFE {
        return keyword() == VBasicDTypeKwd::TRIGGER_SCHEDULER;
    }
    bool isDynamicTriggerScheduler() const VL_MT_SAFE {
        return keyword() == VBasicDTypeKwd::DYNAMIC_TRIGGER_SCHEDULER;
    }
    bool isOpaque() const VL_MT_SAFE { return keyword().isOpaque(); }
    bool isString() const VL_MT_SAFE { return keyword().isString(); }
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
    bool isCompound() const override { return isString(); }
};
class AstBracketArrayDType final : public AstNodeDType {
    // Associative/Queue/Normal array data type, ie "[dtype_or_expr]"
    // only for early parsing then becomes another data type
    // @astgen op1 := childDTypep : Optional[AstNodeDType] // moved to refDTypep() in V3Width
    // @astgen op2 := elementsp : AstNode // ??? key dtype ???
public:
    AstBracketArrayDType(FileLine* fl, VFlagChildDType, AstNodeDType* childDTypep,
                         AstNode* elementsp)
        : ASTGEN_SUPER_BracketArrayDType(fl) {
        this->childDTypep(childDTypep);
        this->elementsp(elementsp);
    }
    ASTGEN_MEMBERS_AstBracketArrayDType;
    bool similarDType(AstNodeDType* samep) const override { V3ERROR_NA_RETURN(false); }
    AstNodeDType* subDTypep() const override { return childDTypep(); }
    // METHODS
    // Will be removed in V3Width, which relies on this
    // being a child not a dtype pointed node
    bool maybePointedTo() const override { return false; }
    AstBasicDType* basicp() const override VL_MT_SAFE { return nullptr; }
    AstNodeDType* skipRefp() const override VL_MT_SAFE { return (AstNodeDType*)this; }
    AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    int widthAlignBytes() const override { V3ERROR_NA_RETURN(0); }
    int widthTotalBytes() const override { V3ERROR_NA_RETURN(0); }
    bool isCompound() const override { return true; }
};
class AstClassRefDType final : public AstNodeDType {
    // Reference to a class
    // @astgen op1 := paramsp: List[AstPin]
private:
    AstClass* m_classp;  // data type pointed to, BELOW the AstTypedef
    AstNodeModule* m_classOrPackagep = nullptr;  // Package hierarchy
public:
    AstClassRefDType(FileLine* fl, AstClass* classp, AstPin* paramsp)
        : ASTGEN_SUPER_ClassRefDType(fl)
        , m_classp{classp} {
        this->dtypep(this);
        this->addParamsp(paramsp);
    }
    ASTGEN_MEMBERS_AstClassRefDType;
    // METHODS
    const char* broken() const override;
    void cloneRelink() override;
    bool same(const AstNode* samep) const override {
        const AstClassRefDType* const asamep = static_cast<const AstClassRefDType*>(samep);
        return (m_classp == asamep->m_classp && m_classOrPackagep == asamep->m_classOrPackagep);
    }
    bool similarDType(AstNodeDType* samep) const override {
        return this == samep || (type() == samep->type() && same(samep));
    }
    void dump(std::ostream& str = std::cout) const override;
    void dumpSmall(std::ostream& str) const override;
    string name() const override;
    AstBasicDType* basicp() const override VL_MT_SAFE { return nullptr; }
    AstNodeDType* skipRefp() const override VL_MT_SAFE { return (AstNodeDType*)this; }
    AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    int widthAlignBytes() const override { return 0; }
    int widthTotalBytes() const override { return 0; }
    AstNodeDType* virtRefDTypep() const override { return nullptr; }
    void virtRefDTypep(AstNodeDType* nodep) override {}
    AstNodeDType* subDTypep() const override { return nullptr; }
    AstNodeModule* classOrPackagep() const { return m_classOrPackagep; }
    void classOrPackagep(AstNodeModule* nodep) { m_classOrPackagep = nodep; }
    AstClass* classp() const { return m_classp; }
    void classp(AstClass* nodep) { m_classp = nodep; }
    bool isCompound() const override { return true; }
};
class AstConstDType final : public AstNodeDType {
    // const data type, ie "const some_dtype var_name [2:0]"
    // ConstDType are removed in V3LinkLValue and become AstVar::isConst.
    // When more generic types are supported AstConstDType will be propagated further.
    // @astgen op1 := childDTypep : Optional[AstNodeDType]
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
    ASTGEN_MEMBERS_AstConstDType;
    const char* broken() const override {
        BROKEN_RTN(!((m_refDTypep && !childDTypep() && m_refDTypep->brokeExists())
                     || (!m_refDTypep && childDTypep())));
        return nullptr;
    }
    void cloneRelink() override {
        if (m_refDTypep && m_refDTypep->clonep()) m_refDTypep = m_refDTypep->clonep();
    }
    bool same(const AstNode* samep) const override {
        const AstConstDType* const sp = static_cast<const AstConstDType*>(samep);
        return (m_refDTypep == sp->m_refDTypep);
    }
    bool similarDType(AstNodeDType* samep) const override {
        return skipRefp()->similarDType(samep->skipRefp());
    }
    AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    AstNodeDType* subDTypep() const override { return m_refDTypep ? m_refDTypep : childDTypep(); }
    void refDTypep(AstNodeDType* nodep) { m_refDTypep = nodep; }
    AstNodeDType* virtRefDTypep() const override { return m_refDTypep; }
    void virtRefDTypep(AstNodeDType* nodep) override { refDTypep(nodep); }
    // METHODS
    AstBasicDType* basicp() const override VL_MT_SAFE { return subDTypep()->basicp(); }
    AstNodeDType* skipRefp() const override VL_MT_SAFE { return subDTypep()->skipRefp(); }
    AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    AstNodeDType* skipRefToEnump() const override { return subDTypep()->skipRefToEnump(); }
    int widthAlignBytes() const override { return subDTypep()->widthAlignBytes(); }
    int widthTotalBytes() const override { return subDTypep()->widthTotalBytes(); }
    bool isCompound() const override {
        v3fatalSrc("call isCompound on subdata type, not reference");
        return false;
    }
};
class AstDefImplicitDType final : public AstNodeDType {
    // For parsing enum/struct/unions that are declared with a variable rather than typedef
    // This allows "var enum {...} a,b" to share the enum definition for both variables
    // After link, these become typedefs
    // @astgen op1 := childDTypep : Optional[AstNodeDType]
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
    ASTGEN_MEMBERS_AstDefImplicitDType;
    int uniqueNum() const { return m_uniqueNum; }
    bool same(const AstNode* samep) const override {
        const AstDefImplicitDType* const sp = static_cast<const AstDefImplicitDType*>(samep);
        return uniqueNum() == sp->uniqueNum();
    }
    bool similarDType(AstNodeDType* samep) const override {
        return type() == samep->type() && same(samep);
    }
    AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    AstNodeDType* subDTypep() const override { return dtypep() ? dtypep() : childDTypep(); }
    void* containerp() const { return m_containerp; }
    // METHODS
    // op1 = Range of variable
    AstNodeDType* dtypeSkipRefp() const { return dtypep()->skipRefp(); }
    AstBasicDType* basicp() const override VL_MT_SAFE { return subDTypep()->basicp(); }
    AstNodeDType* skipRefp() const override VL_MT_SAFE { return (AstNodeDType*)this; }
    AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    int widthAlignBytes() const override { return dtypep()->widthAlignBytes(); }
    int widthTotalBytes() const override { return dtypep()->widthTotalBytes(); }
    string name() const override { return m_name; }
    void name(const string& flag) override { m_name = flag; }
    bool isCompound() const override { return false; }
};
class AstDynArrayDType final : public AstNodeDType {
    // Dynamic array data type, ie "[]"
    // @astgen op1 := childDTypep : Optional[AstNodeDType] // moved to refDTypep() in V3Width
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
    ASTGEN_MEMBERS_AstDynArrayDType;
    const char* broken() const override {
        BROKEN_RTN(!((m_refDTypep && !childDTypep() && m_refDTypep->brokeExists())
                     || (!m_refDTypep && childDTypep())));
        return nullptr;
    }
    void cloneRelink() override {
        if (m_refDTypep && m_refDTypep->clonep()) m_refDTypep = m_refDTypep->clonep();
    }
    bool same(const AstNode* samep) const override {
        const AstAssocArrayDType* const asamep = static_cast<const AstAssocArrayDType*>(samep);
        if (!asamep->subDTypep()) return false;
        return subDTypep() == asamep->subDTypep();
    }
    bool similarDType(AstNodeDType* samep) const override {
        const AstAssocArrayDType* const asamep = static_cast<const AstAssocArrayDType*>(samep);
        return type() == samep->type() && asamep->subDTypep()
               && subDTypep()->skipRefp()->similarDType(asamep->subDTypep()->skipRefp());
    }
    string prettyDTypeName() const override;
    void dumpSmall(std::ostream& str) const override;
    AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    AstNodeDType* subDTypep() const override VL_MT_SAFE {
        return m_refDTypep ? m_refDTypep : childDTypep();
    }
    void refDTypep(AstNodeDType* nodep) { m_refDTypep = nodep; }
    AstNodeDType* virtRefDTypep() const override { return m_refDTypep; }
    void virtRefDTypep(AstNodeDType* nodep) override { refDTypep(nodep); }
    // METHODS
    AstBasicDType* basicp() const override VL_MT_SAFE { return nullptr; }
    AstNodeDType* skipRefp() const override VL_MT_SAFE { return (AstNodeDType*)this; }
    AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    int widthAlignBytes() const override { return subDTypep()->widthAlignBytes(); }
    int widthTotalBytes() const override { return subDTypep()->widthTotalBytes(); }
    bool isCompound() const override { return true; }
};
class AstEmptyQueueDType final : public AstNodeDType {
    // For EmptyQueue
public:
    explicit AstEmptyQueueDType(FileLine* fl)
        : ASTGEN_SUPER_EmptyQueueDType(fl) {
        dtypep(this);
    }
    ASTGEN_MEMBERS_AstEmptyQueueDType;
    void dumpSmall(std::ostream& str) const override;
    bool hasDType() const override { return true; }
    bool maybePointedTo() const override { return true; }
    bool undead() const override { return true; }
    AstNodeDType* subDTypep() const override { return nullptr; }
    AstNodeDType* virtRefDTypep() const override { return nullptr; }
    void virtRefDTypep(AstNodeDType* nodep) override {}
    bool similarDType(AstNodeDType* samep) const override { return this == samep; }
    AstBasicDType* basicp() const override VL_MT_SAFE { return nullptr; }
    // cppcheck-suppress csyleCast
    AstNodeDType* skipRefp() const override VL_MT_SAFE { return (AstNodeDType*)this; }
    // cppcheck-suppress csyleCast
    AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    // cppcheck-suppress csyleCast
    AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    int widthAlignBytes() const override { return 1; }
    int widthTotalBytes() const override { return 1; }
    bool isCompound() const override { return false; }
};
class AstEnumDType final : public AstNodeDType {
    // Parents: TYPEDEF/MODULE
    // @astgen op1 := childDTypep : Optional[AstNodeDType]
    // @astgen op2 := itemsp : List[AstEnumItem]
private:
    string m_name;  // Name from upper typedef, if any
    AstNodeDType* m_refDTypep = nullptr;  // Elements are of this type after V3Width
    const int m_uniqueNum = 0;

public:
    AstEnumDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp, AstEnumItem* itemsp)
        : ASTGEN_SUPER_EnumDType(fl)
        , m_uniqueNum{uniqueNumInc()} {
        childDTypep(dtp);  // Only for parser
        refDTypep(nullptr);
        addItemsp(itemsp);
        dtypep(nullptr);  // V3Width will resolve
        widthFromSub(subDTypep());
    }
    ASTGEN_MEMBERS_AstEnumDType;
    const char* broken() const override {
        BROKEN_RTN(!((m_refDTypep && !childDTypep() && m_refDTypep->brokeExists())
                     || (!m_refDTypep && childDTypep())));
        return nullptr;
    }
    void cloneRelink() override {
        if (m_refDTypep && m_refDTypep->clonep()) m_refDTypep = m_refDTypep->clonep();
    }
    int uniqueNum() const { return m_uniqueNum; }
    bool same(const AstNode* samep) const override {
        const AstEnumDType* const sp = static_cast<const AstEnumDType*>(samep);
        return uniqueNum() == sp->uniqueNum();
    }
    bool similarDType(AstNodeDType* samep) const override { return this == samep; }
    AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    AstNodeDType* subDTypep() const override { return m_refDTypep ? m_refDTypep : childDTypep(); }
    void refDTypep(AstNodeDType* nodep) { m_refDTypep = nodep; }
    AstNodeDType* virtRefDTypep() const override { return m_refDTypep; }
    void virtRefDTypep(AstNodeDType* nodep) override { refDTypep(nodep); }
    string name() const override { return m_name; }
    void name(const string& flag) override { m_name = flag; }
    // METHODS
    AstBasicDType* basicp() const override VL_MT_SAFE { return subDTypep()->basicp(); }
    AstNodeDType* skipRefp() const override VL_MT_SAFE { return subDTypep()->skipRefp(); }
    AstNodeDType* skipRefToConstp() const override { return subDTypep()->skipRefToConstp(); }
    // cppcheck-suppress csyleCast
    AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    int widthAlignBytes() const override { return subDTypep()->widthAlignBytes(); }
    int widthTotalBytes() const override { return subDTypep()->widthTotalBytes(); }
    int itemCount() const {
        size_t count = 0;
        for (AstNode* itemp = itemsp(); itemp; itemp = itemp->nextp()) count++;
        return count;
    }
    bool isCompound() const override { return false; }
};
class AstIfaceRefDType final : public AstNodeDType {
    // Reference to an interface, either for a port, or inside parent cell
    // @astgen op1 := paramsp : List[AstPin]
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
    AstIfaceRefDType(FileLine* fl, FileLine* modportFl, const string& cellName,
                     const string& ifaceName, const string& modport, AstPin* paramsp)
        : ASTGEN_SUPER_IfaceRefDType(fl)
        , m_modportFileline{modportFl}
        , m_cellName{cellName}
        , m_ifaceName{ifaceName} {
        addParamsp(paramsp);
    }
    ASTGEN_MEMBERS_AstIfaceRefDType;
    // METHODS
    const char* broken() const override;
    void dump(std::ostream& str = std::cout) const override;
    void dumpSmall(std::ostream& str) const override;
    void cloneRelink() override;
    AstBasicDType* basicp() const override VL_MT_SAFE { return nullptr; }
    AstNodeDType* skipRefp() const override VL_MT_SAFE { return (AstNodeDType*)this; }
    AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    bool similarDType(AstNodeDType* samep) const override { return this == samep; }
    int widthAlignBytes() const override { return 1; }
    int widthTotalBytes() const override { return 1; }
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
    bool isCompound() const override { return true; }  // But not relevant
};
class AstMemberDType final : public AstNodeDType {
    // A member of a struct/union
    // PARENT: AstNodeUOrStructDType
    // @astgen op1 := childDTypep : Optional[AstNodeDType]
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
    ASTGEN_MEMBERS_AstMemberDType;
    string name() const override { return m_name; }  // * = Var name
    bool hasDType() const override { return true; }
    bool maybePointedTo() const override { return true; }
    const char* broken() const override {
        BROKEN_RTN(m_refDTypep && !m_refDTypep->brokeExists());
        return nullptr;
    }
    void cloneRelink() override {
        if (m_refDTypep && m_refDTypep->clonep()) m_refDTypep = m_refDTypep->clonep();
    }
    AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    AstNodeDType* subDTypep() const override { return m_refDTypep ? m_refDTypep : childDTypep(); }
    void refDTypep(AstNodeDType* nodep) { m_refDTypep = nodep; }
    AstNodeDType* virtRefDTypep() const override { return m_refDTypep; }
    void virtRefDTypep(AstNodeDType* nodep) override { refDTypep(nodep); }
    bool similarDType(AstNodeDType* samep) const override { return this == samep; }
    //
    // (Slow) recurse down to find basic data type (Note don't need virtual -
    // AstVar isn't a NodeDType)
    AstBasicDType* basicp() const override VL_MT_SAFE { return subDTypep()->basicp(); }
    // op1 = Range of variable (Note don't need virtual - AstVar isn't a NodeDType)
    AstNodeDType* dtypeSkipRefp() const { return subDTypep()->skipRefp(); }
    AstNodeDType* skipRefp() const override VL_MT_SAFE { return subDTypep()->skipRefp(); }
    AstNodeDType* skipRefToConstp() const override { return subDTypep()->skipRefToConstp(); }
    AstNodeDType* skipRefToEnump() const override { return subDTypep()->skipRefToEnump(); }
    // (Slow) recurses - Structure alignment 1,2,4 or 8 bytes (arrays affect this)
    int widthAlignBytes() const override { return subDTypep()->widthAlignBytes(); }
    // (Slow) recurses - Width in bytes rounding up 1,2,4,8,12,...
    int widthTotalBytes() const override { return subDTypep()->widthTotalBytes(); }
    // METHODS
    void name(const string& name) override { m_name = name; }
    void tag(const string& text) override { m_tag = text; }
    string tag() const override { return m_tag; }
    int lsb() const { return m_lsb; }
    void lsb(int lsb) { m_lsb = lsb; }
    bool isCompound() const override {
        v3fatalSrc("call isCompound on subdata type, not reference");
        return false;
    }
};
class AstParamTypeDType final : public AstNodeDType {
    // Parents: MODULE
    // A parameter type statement; much like a var or typedef
    // @astgen op1 := childDTypep : Optional[AstNodeDType]
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
    ASTGEN_MEMBERS_AstParamTypeDType;
    void dump(std::ostream& str = std::cout) const override;
    AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    AstNodeDType* subDTypep() const override { return dtypep() ? dtypep() : childDTypep(); }
    AstBasicDType* basicp() const override VL_MT_SAFE { return subDTypep()->basicp(); }
    AstNodeDType* skipRefp() const override VL_MT_SAFE { return subDTypep()->skipRefp(); }
    AstNodeDType* skipRefToConstp() const override { return subDTypep()->skipRefToConstp(); }
    AstNodeDType* skipRefToEnump() const override { return subDTypep()->skipRefToEnump(); }
    bool similarDType(AstNodeDType* samep) const override {
        const AstParamTypeDType* const sp = static_cast<const AstParamTypeDType*>(samep);
        return type() == samep->type() && sp
               && this->subDTypep()->skipRefp()->similarDType(sp->subDTypep()->skipRefp());
    }
    int widthAlignBytes() const override { return dtypep()->widthAlignBytes(); }
    int widthTotalBytes() const override { return dtypep()->widthTotalBytes(); }
    // METHODS
    string name() const override { return m_name; }
    bool maybePointedTo() const override { return true; }
    bool hasDType() const override { return true; }
    void name(const string& flag) override { m_name = flag; }
    VVarType varType() const { return m_varType; }  // * = Type of variable
    bool isParam() const { return true; }
    bool isGParam() const { return (varType() == VVarType::GPARAM); }
    bool isCompound() const override {
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
    ASTGEN_MEMBERS_AstParseTypeDType;
    AstNodeDType* dtypep() const { return nullptr; }
    // METHODS
    bool similarDType(AstNodeDType* samep) const override { return this == samep; }
    AstBasicDType* basicp() const override VL_MT_SAFE { return nullptr; }
    AstNodeDType* skipRefp() const override VL_MT_SAFE { return nullptr; }
    // cppcheck-suppress csyleCast
    AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    // cppcheck-suppress csyleCast
    AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    int widthAlignBytes() const override { return 0; }
    int widthTotalBytes() const override { return 0; }
    bool isCompound() const override {
        v3fatalSrc("call isCompound on subdata type, not reference");
        return false;
    }
};
class AstQueueDType final : public AstNodeDType {
    // Queue array data type, ie "[ $ ]"
    // @astgen op1 := childDTypep : Optional[AstNodeDType] // moved to refDTypep() in V3Width
    // @astgen op2 := boundp : Optional[AstNode]
private:
    AstNodeDType* m_refDTypep = nullptr;  // Elements of this type (after widthing)
public:
    AstQueueDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp, AstNode* boundp)
        : ASTGEN_SUPER_QueueDType(fl) {
        this->childDTypep(dtp);
        this->boundp(boundp);
        refDTypep(nullptr);
        dtypep(nullptr);  // V3Width will resolve
    }
    AstQueueDType(FileLine* fl, AstNodeDType* dtp, AstNode* boundp)
        : ASTGEN_SUPER_QueueDType(fl) {
        this->boundp(boundp);
        refDTypep(dtp);
        dtypep(dtp);
    }
    ASTGEN_MEMBERS_AstQueueDType;
    const char* broken() const override {
        BROKEN_RTN(!((m_refDTypep && !childDTypep() && m_refDTypep->brokeExists())
                     || (!m_refDTypep && childDTypep())));
        return nullptr;
    }
    void cloneRelink() override {
        if (m_refDTypep && m_refDTypep->clonep()) m_refDTypep = m_refDTypep->clonep();
    }
    bool same(const AstNode* samep) const override {
        const AstQueueDType* const asamep = static_cast<const AstQueueDType*>(samep);
        if (!asamep->subDTypep()) return false;
        return (subDTypep() == asamep->subDTypep());
    }
    bool similarDType(AstNodeDType* samep) const override {
        const AstQueueDType* const asamep = static_cast<const AstQueueDType*>(samep);
        return type() == samep->type() && asamep->subDTypep()
               && subDTypep()->skipRefp()->similarDType(asamep->subDTypep()->skipRefp());
    }
    void dumpSmall(std::ostream& str) const override;
    string prettyDTypeName() const override;
    AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    AstNodeDType* subDTypep() const override VL_MT_SAFE {
        return m_refDTypep ? m_refDTypep : childDTypep();
    }
    void refDTypep(AstNodeDType* nodep) { m_refDTypep = nodep; }
    inline int boundConst() const;
    AstNodeDType* virtRefDTypep() const override { return m_refDTypep; }
    void virtRefDTypep(AstNodeDType* nodep) override { refDTypep(nodep); }
    // METHODS
    AstBasicDType* basicp() const override VL_MT_SAFE { return nullptr; }
    // cppcheck-suppress csyleCast
    AstNodeDType* skipRefp() const override VL_MT_SAFE { return (AstNodeDType*)this; }
    // cppcheck-suppress csyleCast
    AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    // cppcheck-suppress csyleCast
    AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    int widthAlignBytes() const override { return subDTypep()->widthAlignBytes(); }
    int widthTotalBytes() const override { return subDTypep()->widthTotalBytes(); }
    bool isCompound() const override { return true; }
};
class AstRefDType final : public AstNodeDType {
    // @astgen op1 := typeofp : Optional[AstNode]
    // @astgen op2 := classOrPackageOpp : Optional[AstNode]
    // @astgen op3 := paramsp : List[AstPin]
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
    AstRefDType(FileLine* fl, const string& name, AstNode* classOrPackagep, AstPin* paramsp)
        : ASTGEN_SUPER_RefDType(fl)
        , m_name{name} {
        this->classOrPackageOpp(classOrPackagep);
        addParamsp(paramsp);
    }
    class FlagTypeOfExpr {};  // type(expr) for parser only
    AstRefDType(FileLine* fl, FlagTypeOfExpr, AstNode* typeofp)
        : ASTGEN_SUPER_RefDType(fl) {
        this->typeofp(typeofp);
    }
    ASTGEN_MEMBERS_AstRefDType;
    // METHODS
    const char* broken() const override;
    void cloneRelink() override;
    bool same(const AstNode* samep) const override {
        const AstRefDType* const asamep = static_cast<const AstRefDType*>(samep);
        return (m_typedefp == asamep->m_typedefp && m_refDTypep == asamep->m_refDTypep
                && m_name == asamep->m_name && m_classOrPackagep == asamep->m_classOrPackagep);
    }
    bool similarDType(AstNodeDType* samep) const override {
        return skipRefp()->similarDType(samep->skipRefp());
    }
    void dump(std::ostream& str = std::cout) const override;
    string name() const override { return m_name; }
    string prettyDTypeName() const override {
        return subDTypep() ? subDTypep()->name() : prettyName();
    }
    AstBasicDType* basicp() const override VL_MT_SAFE {
        return subDTypep() ? subDTypep()->basicp() : nullptr;
    }
    AstNodeDType* subDTypep() const override;
    AstNodeDType* skipRefp() const override VL_MT_SAFE {
        // Skip past both the Ref and the Typedef
        if (subDTypep()) {
            return subDTypep()->skipRefp();
        } else {
            v3fatalSrc("Typedef not linked");
            return nullptr;
        }
    }
    AstNodeDType* skipRefToConstp() const override {
        if (subDTypep()) {
            return subDTypep()->skipRefToConstp();
        } else {
            v3fatalSrc("Typedef not linked");
            return nullptr;
        }
    }
    AstNodeDType* skipRefToEnump() const override {
        if (subDTypep()) {
            return subDTypep()->skipRefToEnump();
        } else {
            v3fatalSrc("Typedef not linked");
            return nullptr;
        }
    }
    int widthAlignBytes() const override { return dtypeSkipRefp()->widthAlignBytes(); }
    int widthTotalBytes() const override { return dtypeSkipRefp()->widthTotalBytes(); }
    void name(const string& flag) override { m_name = flag; }
    AstNodeDType* dtypeSkipRefp() const { return subDTypep()->skipRefp(); }
    AstTypedef* typedefp() const { return m_typedefp; }
    void typedefp(AstTypedef* nodep) { m_typedefp = nodep; }
    AstNodeDType* refDTypep() const { return m_refDTypep; }
    void refDTypep(AstNodeDType* nodep) { m_refDTypep = nodep; }
    AstNodeDType* virtRefDTypep() const override { return refDTypep(); }
    void virtRefDTypep(AstNodeDType* nodep) override { refDTypep(nodep); }
    AstNodeModule* classOrPackagep() const { return m_classOrPackagep; }
    void classOrPackagep(AstNodeModule* nodep) { m_classOrPackagep = nodep; }
    bool isCompound() const override {
        v3fatalSrc("call isCompound on subdata type, not reference");
        return false;
    }
};
class AstUnsizedArrayDType final : public AstNodeDType {
    // Unsized/open-range Array data type, ie "some_dtype var_name []"
    // @astgen op1 := childDTypep : Optional[AstNodeDType] // moved to refDTypep() in V3Width
private:
    AstNodeDType* m_refDTypep;  // Elements of this type (after widthing)
public:
    AstUnsizedArrayDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp)
        : ASTGEN_SUPER_UnsizedArrayDType(fl) {
        childDTypep(dtp);  // Only for parser
        refDTypep(nullptr);
        dtypep(nullptr);  // V3Width will resolve
    }
    ASTGEN_MEMBERS_AstUnsizedArrayDType;
    const char* broken() const override {
        BROKEN_RTN(!((m_refDTypep && !childDTypep() && m_refDTypep->brokeExists())
                     || (!m_refDTypep && childDTypep())));
        return nullptr;
    }
    void cloneRelink() override {
        if (m_refDTypep && m_refDTypep->clonep()) m_refDTypep = m_refDTypep->clonep();
    }
    bool same(const AstNode* samep) const override;
    bool similarDType(AstNodeDType* samep) const override;
    void dumpSmall(std::ostream& str) const override;
    AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    AstNodeDType* subDTypep() const override { return m_refDTypep ? m_refDTypep : childDTypep(); }
    void refDTypep(AstNodeDType* nodep) { m_refDTypep = nodep; }
    AstNodeDType* virtRefDTypep() const override { return m_refDTypep; }
    void virtRefDTypep(AstNodeDType* nodep) override { refDTypep(nodep); }
    // METHODS
    AstBasicDType* basicp() const override VL_MT_SAFE { return subDTypep()->basicp(); }
    AstNodeDType* skipRefp() const override VL_MT_SAFE { return (AstNodeDType*)this; }
    AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    int widthAlignBytes() const override { return subDTypep()->widthAlignBytes(); }
    int widthTotalBytes() const override { return subDTypep()->widthTotalBytes(); }
    bool isCompound() const override { return true; }
};
class AstVoidDType final : public AstNodeDType {
    // For e.g. a function returning void
public:
    explicit AstVoidDType(FileLine* fl)
        : ASTGEN_SUPER_VoidDType(fl) {
        dtypep(this);
    }
    ASTGEN_MEMBERS_AstVoidDType;
    void dumpSmall(std::ostream& str) const override;
    bool hasDType() const override { return true; }
    bool maybePointedTo() const override { return true; }
    bool undead() const override { return true; }
    AstNodeDType* subDTypep() const override { return nullptr; }
    AstNodeDType* virtRefDTypep() const override { return nullptr; }
    void virtRefDTypep(AstNodeDType* nodep) override {}
    bool similarDType(AstNodeDType* samep) const override { return this == samep; }
    AstBasicDType* basicp() const override VL_MT_SAFE { return nullptr; }
    // cppcheck-suppress csyleCast
    AstNodeDType* skipRefp() const override VL_MT_SAFE { return (AstNodeDType*)this; }
    // cppcheck-suppress csyleCast
    AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    // cppcheck-suppress csyleCast
    AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    int widthAlignBytes() const override { return 1; }
    int widthTotalBytes() const override { return 1; }
    bool isCompound() const override { return false; }
};
class AstWildcardArrayDType final : public AstNodeDType {
    // Wildcard index type associative array data type, ie "some_dtype var_name [*]"
    // @astgen op1 := childDTypep : Optional[AstNodeDType] // moved to refDTypep() in V3Width
private:
    AstNodeDType* m_refDTypep;  // Elements of this type (after widthing)
public:
    AstWildcardArrayDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp)
        : ASTGEN_SUPER_WildcardArrayDType(fl) {
        childDTypep(dtp);  // Only for parser
        refDTypep(nullptr);
        dtypep(nullptr);  // V3Width will resolve
    }
    ASTGEN_MEMBERS_AstWildcardArrayDType;
    const char* broken() const override {
        BROKEN_RTN(!((m_refDTypep && !childDTypep() && m_refDTypep->brokeExists())
                     || (!m_refDTypep && childDTypep())));
        return nullptr;
    }
    void cloneRelink() override {
        if (m_refDTypep && m_refDTypep->clonep()) m_refDTypep = m_refDTypep->clonep();
    }
    bool same(const AstNode* samep) const override;
    bool similarDType(AstNodeDType* samep) const override;
    void dumpSmall(std::ostream& str) const override;
    AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    AstNodeDType* subDTypep() const override VL_MT_SAFE {
        return m_refDTypep ? m_refDTypep : childDTypep();
    }
    void refDTypep(AstNodeDType* nodep) { m_refDTypep = nodep; }
    AstNodeDType* virtRefDTypep() const override { return m_refDTypep; }
    void virtRefDTypep(AstNodeDType* nodep) override { refDTypep(nodep); }
    // METHODS
    AstBasicDType* basicp() const override VL_MT_SAFE { return subDTypep()->basicp(); }
    AstNodeDType* skipRefp() const override VL_MT_SAFE { return (AstNodeDType*)this; }
    AstNodeDType* skipRefToConstp() const override { return (AstNodeDType*)this; }
    AstNodeDType* skipRefToEnump() const override { return (AstNodeDType*)this; }
    int widthAlignBytes() const override { return sizeof(std::map<std::string, std::string>); }
    int widthTotalBytes() const override { return sizeof(std::map<std::string, std::string>); }
    bool isCompound() const override { return true; }
};

// === AstNodeArrayDType ===
class AstPackArrayDType final : public AstNodeArrayDType {
    // Packed array data type, ie "some_dtype [2:0] var_name"
public:
    inline AstPackArrayDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp, AstRange* rangep);
    inline AstPackArrayDType(FileLine* fl, AstNodeDType* dtp, AstRange* rangep);
    ASTGEN_MEMBERS_AstPackArrayDType;
    string prettyDTypeName() const override;
    bool isCompound() const override { return false; }
};
class AstUnpackArrayDType final : public AstNodeArrayDType {
    // Array data type, ie "some_dtype var_name [2:0]"
    bool m_isCompound = false;  // Non-POD subDType, or parent requires compound
public:
    AstUnpackArrayDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp, AstRange* rangep)
        : ASTGEN_SUPER_UnpackArrayDType(fl) {
        this->childDTypep(dtp);  // Only for parser
        this->rangep(rangep);
        refDTypep(nullptr);
        dtypep(nullptr);  // V3Width will resolve
        // For backward compatibility AstNodeArrayDType and others inherit
        // width and signing from the subDType/base type
        widthFromSub(subDTypep());
    }
    AstUnpackArrayDType(FileLine* fl, AstNodeDType* dtp, AstRange* rangep)
        : ASTGEN_SUPER_UnpackArrayDType(fl) {
        this->rangep(rangep);
        refDTypep(dtp);
        dtypep(this);
        // For backward compatibility AstNodeArrayDType and others inherit
        // width and signing from the subDType/base type
        widthFromSub(subDTypep());
    }
    ASTGEN_MEMBERS_AstUnpackArrayDType;
    string prettyDTypeName() const override;
    bool same(const AstNode* samep) const override {
        const AstUnpackArrayDType* const sp = static_cast<const AstUnpackArrayDType*>(samep);
        return m_isCompound == sp->m_isCompound;
    }
    // Outer dimension comes first. The first element is this node.
    std::vector<AstUnpackArrayDType*> unpackDimensions();
    void isCompound(bool flag) { m_isCompound = flag; }
    bool isCompound() const override VL_MT_SAFE { return m_isCompound; }
};

// === AstNodeUOrStructDType ===
class AstStructDType final : public AstNodeUOrStructDType {
public:
    // VSigning below is mispurposed to indicate if packed or not
    AstStructDType(FileLine* fl, VSigning numericUnpack)
        : ASTGEN_SUPER_StructDType(fl, numericUnpack) {}
    ASTGEN_MEMBERS_AstStructDType;
    string verilogKwd() const override { return "struct"; }
};
class AstUnionDType final : public AstNodeUOrStructDType {
public:
    // UNSUP: bool isTagged;
    // VSigning below is mispurposed to indicate if packed or not
    AstUnionDType(FileLine* fl, VSigning numericUnpack)
        : ASTGEN_SUPER_UnionDType(fl, numericUnpack) {}
    ASTGEN_MEMBERS_AstUnionDType;
    string verilogKwd() const override { return "union"; }
};

#endif  // Guard
