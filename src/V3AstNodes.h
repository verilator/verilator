// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Ast node structure
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2021 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3ASTNODES_H_
#define VERILATOR_V3ASTNODES_H_

#ifndef VERILATOR_V3AST_H_
#error "Use V3Ast.h as the include"
#endif

//######################################################################
// Standard defines for all AstNode final classes

#define ASTNODE_NODE_FUNCS_NO_DTOR(name) \
    virtual void accept(AstNVisitor& v) override { v.visit(this); } \
    virtual AstNode* clone() override { return new Ast##name(*this); } \
    static Ast##name* cloneTreeNull(Ast##name* nodep, bool cloneNextLink) { \
        return nodep ? nodep->cloneTree(cloneNextLink) : nullptr; \
    } \
    Ast##name* cloneTree(bool cloneNext) { \
        return static_cast<Ast##name*>(AstNode::cloneTree(cloneNext)); \
    } \
    Ast##name* clonep() const { return static_cast<Ast##name*>(AstNode::clonep()); }

#define ASTNODE_NODE_FUNCS(name) \
    virtual ~Ast##name() override = default; \
    ASTNODE_NODE_FUNCS_NO_DTOR(name)

//######################################################################
// Macros replaced by 'astgen'

#define ASTGEN_SUPER(...)  // Roughly: <SuperClass>(AstType::at<ThisClass>, ...)

//######################################################################
//=== Ast* : Specific types
// Netlist interconnect

class AstConst final : public AstNodeMath {
    // A constant
private:
    V3Number m_num;  // Constant value
    void initWithNumber() {
        if (m_num.isDouble()) {
            dtypeSetDouble();
        } else if (m_num.isString()) {
            dtypeSetString();
        } else {
            dtypeSetLogicUnsized(m_num.width(), (m_num.sized() ? 0 : m_num.widthMin()),
                                 VSigning::fromBool(m_num.isSigned()));
        }
        m_num.nodep(this);
    }

public:
    AstConst(FileLine* fl, const V3Number& num)
        : ASTGEN_SUPER(fl)
        , m_num(num) {
        initWithNumber();
    }
    class WidthedValue {};  // for creator type-overload selection
    AstConst(FileLine* fl, WidthedValue, int width, uint32_t value)
        : ASTGEN_SUPER(fl)
        , m_num(this, width, value) {
        initWithNumber();
    }
    class DtypedValue {};  // for creator type-overload selection
    AstConst(FileLine* fl, DtypedValue, AstNodeDType* nodedtypep, uint32_t value)
        : ASTGEN_SUPER(fl)
        , m_num(this, nodedtypep->width(), value, nodedtypep->widthSized()) {
        initWithNumber();
    }
    class StringToParse {};  // for creator type-overload selection
    AstConst(FileLine* fl, StringToParse, const char* sourcep)
        : ASTGEN_SUPER(fl)
        , m_num(this, sourcep) {
        initWithNumber();
    }
    class VerilogStringLiteral {};  // for creator type-overload selection
    AstConst(FileLine* fl, VerilogStringLiteral, const string& str)
        : ASTGEN_SUPER(fl)
        , m_num(V3Number::VerilogStringLiteral(), this, str) {
        initWithNumber();
    }
    AstConst(FileLine* fl, uint32_t num)
        : ASTGEN_SUPER(fl)
        , m_num(this, 32, num) {
        dtypeSetLogicUnsized(m_num.width(), 0, VSigning::UNSIGNED);
    }
    class Unsized32 {};  // for creator type-overload selection
    AstConst(FileLine* fl, Unsized32, uint32_t num)  // Unsized 32-bit integer of specified value
        : ASTGEN_SUPER(fl)
        , m_num(this, 32, num) {
        m_num.width(32, false);
        dtypeSetLogicUnsized(32, m_num.widthMin(), VSigning::UNSIGNED);
    }
    class Signed32 {};  // for creator type-overload selection
    AstConst(FileLine* fl, Signed32, int32_t num)  // Signed 32-bit integer of specified value
        : ASTGEN_SUPER(fl)
        , m_num(this, 32, num) {
        m_num.width(32, true);
        dtypeSetLogicUnsized(32, m_num.widthMin(), VSigning::SIGNED);
    }
    class Unsized64 {};  // for creator type-overload selection
    AstConst(FileLine* fl, Unsized64, vluint64_t num)
        : ASTGEN_SUPER(fl)
        , m_num(this, 64, 0) {
        m_num.setQuad(num);
        dtypeSetLogicSized(64, VSigning::UNSIGNED);
    }
    class SizedEData {};  // for creator type-overload selection
    AstConst(FileLine* fl, SizedEData, vluint64_t num)
        : ASTGEN_SUPER(fl)
        , m_num(this, VL_EDATASIZE, 0) {
        m_num.setQuad(num);
        dtypeSetLogicSized(VL_EDATASIZE, VSigning::UNSIGNED);
    }
    class RealDouble {};  // for creator type-overload selection
    AstConst(FileLine* fl, RealDouble, double num)
        : ASTGEN_SUPER(fl)
        , m_num(this, 64) {
        m_num.setDouble(num);
        dtypeSetDouble();
    }
    class String {};  // for creator type-overload selection
    AstConst(FileLine* fl, String, const string& num)
        : ASTGEN_SUPER(fl)
        , m_num(V3Number::String(), this, num) {
        dtypeSetString();
    }
    class BitFalse {};
    AstConst(FileLine* fl, BitFalse)  // Shorthand const 0, dtype should be a logic of size 1
        : ASTGEN_SUPER(fl)
        , m_num(this, 1, 0) {
        dtypeSetBit();
    }
    // Shorthand const 1 (or with argument 0/1), dtype should be a logic of size 1
    class BitTrue {};
    AstConst(FileLine* fl, BitTrue, bool on = true)
        : ASTGEN_SUPER(fl)
        , m_num(this, 1, on) {
        dtypeSetBit();
    }
    class Null {};
    AstConst(FileLine* fl, Null)
        : ASTGEN_SUPER(fl)
        , m_num(V3Number::Null{}, this) {
        dtypeSetBit();  // Events 1 bit, objects 64 bits, so autoExtend=1 and use bit here
        initWithNumber();
    }
    ASTNODE_NODE_FUNCS(Const)
    virtual string name() const override { return num().ascii(); }  // * = Value
    const V3Number& num() const { return m_num; }  // * = Value
    V3Number& num() { return m_num; }  // * = Value
    uint32_t toUInt() const { return num().toUInt(); }
    vlsint32_t toSInt() const { return num().toSInt(); }
    vluint64_t toUQuad() const { return num().toUQuad(); }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual V3Hash sameHash() const override { return V3Hash(num().toHash()); }
    virtual bool same(const AstNode* samep) const override {
        const AstConst* sp = static_cast<const AstConst*>(samep);
        return num().isCaseEq(sp->num());
    }
    virtual int instrCount() const override { return widthInstrs(); }
    bool isEqAllOnes() const { return num().isEqAllOnes(width()); }
    bool isEqAllOnesV() const { return num().isEqAllOnes(widthMinV()); }
    // Parse string and create appropriate type of AstConst.
    // May return nullptr on parse failure.
    static AstConst* parseParamLiteral(FileLine* fl, const string& literal);
};

class AstRange final : public AstNodeRange {
    // Range specification, for use under variables and cells
public:
    AstRange(FileLine* fl, AstNode* leftp, AstNode* rightp)
        : ASTGEN_SUPER(fl) {
        setOp2p(leftp);
        setOp3p(rightp);
    }
    AstRange(FileLine* fl, int left, int right)
        : ASTGEN_SUPER(fl) {
        setOp2p(new AstConst(fl, left));
        setOp3p(new AstConst(fl, right));
    }
    AstRange(FileLine* fl, const VNumRange& range)
        : ASTGEN_SUPER(fl) {
        setOp2p(new AstConst(fl, range.left()));
        setOp3p(new AstConst(fl, range.right()));
    }
    ASTNODE_NODE_FUNCS(Range)
    AstNode* leftp() const { return op2p(); }
    AstNode* rightp() const { return op3p(); }
    int leftConst() const {
        AstConst* constp = VN_CAST(leftp(), Const);
        return (constp ? constp->toSInt() : 0);
    }
    int rightConst() const {
        AstConst* constp = VN_CAST(rightp(), Const);
        return (constp ? constp->toSInt() : 0);
    }
    int hiConst() const {
        int l = leftConst();
        int r = rightConst();
        return l > r ? l : r;
    }
    int loConst() const {
        int l = leftConst();
        int r = rightConst();
        return l > r ? r : l;
    }
    int elementsConst() const { return hiConst() - loConst() + 1; }
    bool littleEndian() const { return leftConst() < rightConst(); }
    virtual void dump(std::ostream& str) const override;
    virtual string emitC() { V3ERROR_NA_RETURN(""); }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
};

class AstBracketRange final : public AstNodeRange {
    // Parser only concept "[lhsp]", a AstUnknownRange, QueueRange or Range,
    // unknown until lhsp type is determined
public:
    AstBracketRange(FileLine* fl, AstNode* elementsp)
        : ASTGEN_SUPER(fl) {
        setOp1p(elementsp);
    }
    ASTNODE_NODE_FUNCS(BracketRange)
    virtual string emitC() { V3ERROR_NA_RETURN(""); }
    virtual string emitVerilog() { V3ERROR_NA_RETURN(""); }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    // Will be removed in V3Width, which relies on this
    // being a child not a dtype pointed node
    virtual bool maybePointedTo() const override { return false; }
    AstNode* elementsp() const { return op1p(); }
};

class AstUnsizedRange final : public AstNodeRange {
    // Unsized range specification, for open arrays
public:
    explicit AstUnsizedRange(FileLine* fl)
        : ASTGEN_SUPER(fl) {}
    ASTNODE_NODE_FUNCS(UnsizedRange)
    virtual string emitC() { V3ERROR_NA_RETURN(""); }
    virtual string emitVerilog() { return "[]"; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
};

class AstGatePin final : public AstNodeMath {
    // Possibly expand a gate primitive input pin value to match the range of the gate primitive
public:
    AstGatePin(FileLine* fl, AstNode* lhsp, AstRange* rangep)
        : ASTGEN_SUPER(fl) {
        setOp1p(lhsp);
        setOp2p(rangep);
    }
    ASTNODE_NODE_FUNCS(GatePin)
    virtual string emitVerilog() override { return "%l"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    AstNode* exprp() const { return op1p(); }  // op1 = Pin expression
    AstRange* rangep() const { return VN_CAST(op2p(), Range); }  // op2 = Range of pin
};

//######################################################################
// Classes

class AstClassPackage final : public AstNodeModule {
    // The static information portion of a class (treated similarly to a package)
    AstClass* m_classp
        = nullptr;  // Class package this is under (weak pointer, hard link is other way)
public:
    AstClassPackage(FileLine* fl, const string& name)
        : ASTGEN_SUPER(fl, name) {}
    ASTNODE_NODE_FUNCS(ClassPackage)
    virtual string verilogKwd() const override { return "/*class*/package"; }
    virtual const char* broken() const override;
    virtual bool timescaleMatters() const override { return false; }
    AstClass* classp() const { return m_classp; }
    void classp(AstClass* classp) { m_classp = classp; }
};

class AstClass final : public AstNodeModule {
    // TYPES
    using MemberNameMap = std::map<const std::string, AstNode*>;
    // MEMBERS
    MemberNameMap m_members;  // Members or method children
    AstClassPackage* m_classOrPackagep = nullptr;  // Class package this is under
    bool m_virtual = false;  // Virtual class
    bool m_extended = false;  // Is extension or extended by other classes
    void insertCache(AstNode* nodep);

public:
    AstClass(FileLine* fl, const string& name)
        : ASTGEN_SUPER(fl, name) {}
    ASTNODE_NODE_FUNCS(Class)
    virtual string verilogKwd() const override { return "class"; }
    virtual bool isHeavy() const override { return true; }
    virtual bool maybePointedTo() const override { return true; }
    virtual void dump(std::ostream& str) const override;
    virtual const char* broken() const override {
        BROKEN_BASE_RTN(AstNodeModule::broken());
        BROKEN_RTN(m_classOrPackagep && !m_classOrPackagep->brokeExists());
        return nullptr;
    }
    virtual bool timescaleMatters() const override { return false; }
    // op1/op2/op3 in AstNodeModule
    AstClassPackage* classOrPackagep() const { return m_classOrPackagep; }
    void classOrPackagep(AstClassPackage* classpackagep) { m_classOrPackagep = classpackagep; }
    AstNode* membersp() const { return stmtsp(); }  // op2 = List of statements
    void addMembersp(AstNode* nodep) {
        insertCache(nodep);
        addStmtp(nodep);
    }
    AstClassExtends* extendsp() const { return VN_CAST(op4p(), ClassExtends); }
    void extendsp(AstNode* nodep) { addNOp4p(nodep); }
    void clearCache() { m_members.clear(); }
    void repairCache();
    AstNode* findMember(const string& name) const {
        const auto it = m_members.find(name);
        return (it == m_members.end()) ? nullptr : it->second;
    }
    bool isExtended() const { return m_extended; }
    void isExtended(bool flag) { m_extended = flag; }
    bool isVirtual() const { return m_virtual; }
    void isVirtual(bool flag) { m_virtual = flag; }
    // Return true if this class is an extension of base class (SLOW)
    // Accepts nullptrs
    static bool isClassExtendedFrom(const AstClass* refClassp, const AstClass* baseClassp);
};

class AstClassExtends final : public AstNode {
    // Children: List of AstParseRef for packages/classes
    // during early parse, then moves to dtype
public:
    AstClassExtends(FileLine* fl, AstNode* classOrPkgsp)
        : ASTGEN_SUPER(fl) {
        setNOp2p(classOrPkgsp);  // Only for parser
    }
    ASTNODE_NODE_FUNCS(ClassExtends)
    virtual bool hasDType() const override { return true; }
    virtual string verilogKwd() const override { return "extends"; }
    AstNodeDType* childDTypep() const { return VN_CAST(op1p(), NodeDType); }
    void childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    AstNode* classOrPkgsp() const { return op2p(); }
    void classOrPkgsp(AstNode* nodep) { setOp2p(nodep); }
    AstClass* classp() const;  // Class being extended (after link)
};

//######################################################################
//==== Data Types

class AstParamTypeDType final : public AstNodeDType {
    // Parents: MODULE
    // A parameter type statement; much like a var or typedef
private:
    AstVarType m_varType;  // Type of variable (for localparam vs. param)
    string m_name;  // Name of variable
public:
    AstParamTypeDType(FileLine* fl, AstVarType type, const string& name, VFlagChildDType,
                      AstNodeDType* dtp)
        : ASTGEN_SUPER(fl)
        , m_varType{type}
        , m_name{name} {
        childDTypep(dtp);  // Only for parser
        dtypep(nullptr);  // V3Width will resolve
    }
    ASTNODE_NODE_FUNCS(ParamTypeDType)
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    // op1 = Type assigning to
    AstNodeDType* childDTypep() const { return VN_CAST(op1p(), NodeDType); }
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
        const AstParamTypeDType* sp = static_cast<const AstParamTypeDType*>(samep);
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
    AstVarType varType() const { return m_varType; }  // * = Type of variable
    bool isParam() const { return true; }
    bool isGParam() const { return (varType() == AstVarType::GPARAM); }
    virtual bool isCompound() const override {
        v3fatalSrc("call isCompound on subdata type, not reference");
        return false;
    }
};

class AstTypedef final : public AstNode {
private:
    string m_name;
    bool m_attrPublic;
    string m_tag;  // Holds the string of the verilator tag -- used in XML output.
public:
    AstTypedef(FileLine* fl, const string& name, AstNode* attrsp, VFlagChildDType,
               AstNodeDType* dtp)
        : ASTGEN_SUPER(fl)
        , m_name{name} {
        childDTypep(dtp);  // Only for parser
        addAttrsp(attrsp);
        dtypep(nullptr);  // V3Width will resolve
        m_attrPublic = false;
    }
    ASTNODE_NODE_FUNCS(Typedef)
    virtual void dump(std::ostream& str) const override;
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    // op1 = Type assigning to
    AstNodeDType* childDTypep() const { return VN_CAST(op1p(), NodeDType); }
    void childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    virtual AstNodeDType* subDTypep() const { return dtypep() ? dtypep() : childDTypep(); }
    void addAttrsp(AstNode* nodep) { addNOp4p(nodep); }
    AstNode* attrsp() const { return op4p(); }  // op4 = Attributes during early parse
    // METHODS
    virtual string name() const override { return m_name; }
    virtual bool maybePointedTo() const override { return true; }
    virtual bool hasDType() const override { return true; }
    virtual void name(const string& flag) override { m_name = flag; }
    bool attrPublic() const { return m_attrPublic; }
    void attrPublic(bool flag) { m_attrPublic = flag; }
    virtual void tag(const string& text) override { m_tag = text; }
    virtual string tag() const override { return m_tag; }
};

class AstTypedefFwd final : public AstNode {
    // Forward declaration of a type; stripped after netlist parsing is complete
private:
    string m_name;

public:
    AstTypedefFwd(FileLine* fl, const string& name)
        : ASTGEN_SUPER(fl)
        , m_name{name} {}
    ASTNODE_NODE_FUNCS(TypedefFwd)
    // METHODS
    virtual string name() const override { return m_name; }
    virtual bool maybePointedTo() const override { return true; }
};

class AstDefImplicitDType final : public AstNodeDType {
    // For parsing enum/struct/unions that are declared with a variable rather than typedef
    // This allows "var enum {...} a,b" to share the enum definition for both variables
    // After link, these become typedefs
private:
    string m_name;
    void* m_containerp;  // In what scope is the name unique, so we can know what are duplicate
                         // definitions (arbitrary value)
    int m_uniqueNum;

public:
    AstDefImplicitDType(FileLine* fl, const string& name, void* containerp, VFlagChildDType,
                        AstNodeDType* dtp)
        : ASTGEN_SUPER(fl)
        , m_name{name}
        , m_containerp{containerp} {
        childDTypep(dtp);  // Only for parser
        dtypep(nullptr);  // V3Width will resolve
        m_uniqueNum = uniqueNumInc();
    }
    ASTNODE_NODE_FUNCS(DefImplicitDType)
    virtual bool same(const AstNode* samep) const override {
        const AstDefImplicitDType* sp = static_cast<const AstDefImplicitDType*>(samep);
        return m_uniqueNum == sp->m_uniqueNum;
    }
    virtual bool similarDType(AstNodeDType* samep) const override {
        return type() == samep->type() && same(samep);
    }
    virtual V3Hash sameHash() const override { return V3Hash(m_uniqueNum); }
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    // op1 = Range of variable
    AstNodeDType* childDTypep() const { return VN_CAST(op1p(), NodeDType); }
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

class AstAssocArrayDType final : public AstNodeDType {
    // Associative array data type, ie "[some_dtype]"
    // Children: DTYPE (moved to refDTypep() in V3Width)
    // Children: DTYPE (the key, which remains here as a pointer)
private:
    AstNodeDType* m_refDTypep;  // Elements of this type (after widthing)
    AstNodeDType* m_keyDTypep;  // Keys of this type (after widthing)
public:
    AstAssocArrayDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp, AstNodeDType* keyDtp)
        : ASTGEN_SUPER(fl) {
        childDTypep(dtp);  // Only for parser
        keyChildDTypep(keyDtp);  // Only for parser
        refDTypep(nullptr);
        keyDTypep(nullptr);
        dtypep(nullptr);  // V3Width will resolve
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
        const AstAssocArrayDType* asamep = static_cast<const AstAssocArrayDType*>(samep);
        if (!asamep->subDTypep()) return false;
        if (!asamep->keyDTypep()) return false;
        return (subDTypep() == asamep->subDTypep() && keyDTypep() == asamep->keyDTypep());
    }
    virtual bool similarDType(AstNodeDType* samep) const override {
        const AstAssocArrayDType* asamep = static_cast<const AstAssocArrayDType*>(samep);
        return type() == samep->type() && asamep->subDTypep()
               && subDTypep()->skipRefp()->similarDType(asamep->subDTypep()->skipRefp());
    }
    virtual string prettyDTypeName() const override;
    virtual void dumpSmall(std::ostream& str) const override;
    virtual V3Hash sameHash() const override { return V3Hash(m_refDTypep); }
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    virtual AstNodeDType* getChild2DTypep() const override { return keyChildDTypep(); }
    virtual bool isHeavy() const override { return true; }
    // op1 = Range of variable
    AstNodeDType* childDTypep() const { return VN_CAST(op1p(), NodeDType); }
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
    AstNodeDType* keyChildDTypep() const { return VN_CAST(op2p(), NodeDType); }
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

class AstBracketArrayDType final : public AstNodeDType {
    // Associative/Queue/Normal array data type, ie "[dtype_or_expr]"
    // only for early parsing then becomes another data type
    // Children: DTYPE (moved to refDTypep() in V3Width)
    // Children: DTYPE (the key)
public:
    AstBracketArrayDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp, AstNode* elementsp)
        : ASTGEN_SUPER(fl) {
        setOp1p(dtp);  // Only for parser
        setOp2p(elementsp);  // Only for parser
    }
    ASTNODE_NODE_FUNCS(BracketArrayDType)
    virtual bool similarDType(AstNodeDType* samep) const override { V3ERROR_NA_RETURN(false); }
    // op1 = Range of variable
    AstNodeDType* childDTypep() const { return VN_CAST(op1p(), NodeDType); }
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

class AstDynArrayDType final : public AstNodeDType {
    // Dynamic array data type, ie "[]"
    // Children: DTYPE (moved to refDTypep() in V3Width)
private:
    AstNodeDType* m_refDTypep;  // Elements of this type (after widthing)
public:
    AstDynArrayDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp)
        : ASTGEN_SUPER(fl) {
        childDTypep(dtp);  // Only for parser
        refDTypep(nullptr);
        dtypep(nullptr);  // V3Width will resolve
    }
    AstDynArrayDType(FileLine* fl, AstNodeDType* dtp)
        : ASTGEN_SUPER(fl) {
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
        const AstAssocArrayDType* asamep = static_cast<const AstAssocArrayDType*>(samep);
        if (!asamep->subDTypep()) return false;
        return subDTypep() == asamep->subDTypep();
    }
    virtual bool similarDType(AstNodeDType* samep) const override {
        const AstAssocArrayDType* asamep = static_cast<const AstAssocArrayDType*>(samep);
        return type() == samep->type() && asamep->subDTypep()
               && subDTypep()->skipRefp()->similarDType(asamep->subDTypep()->skipRefp());
    }
    virtual string prettyDTypeName() const override;
    virtual void dumpSmall(std::ostream& str) const override;
    virtual V3Hash sameHash() const override { return V3Hash(m_refDTypep); }
    virtual bool isHeavy() const override { return true; }
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    // op1 = Range of variable
    AstNodeDType* childDTypep() const { return VN_CAST(op1p(), NodeDType); }
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

class AstPackArrayDType final : public AstNodeArrayDType {
    // Packed array data type, ie "some_dtype [2:0] var_name"
    // Children: DTYPE (moved to refDTypep() in V3Width)
    // Children: RANGE (array bounds)
public:
    AstPackArrayDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp, AstRange* rangep)
        : ASTGEN_SUPER(fl) {
        childDTypep(dtp);  // Only for parser
        refDTypep(nullptr);
        setOp2p(rangep);
        dtypep(nullptr);  // V3Width will resolve
        int width = subDTypep()->width() * rangep->elementsConst();
        widthForce(width, width);
    }
    AstPackArrayDType(FileLine* fl, AstNodeDType* dtp, AstRange* rangep)
        : ASTGEN_SUPER(fl) {
        refDTypep(dtp);
        setOp2p(rangep);
        dtypep(this);
        int width = subDTypep()->width() * rangep->elementsConst();
        widthForce(width, width);
    }
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
        : ASTGEN_SUPER(fl) {
        childDTypep(dtp);  // Only for parser
        refDTypep(nullptr);
        setOp2p(rangep);
        dtypep(nullptr);  // V3Width will resolve
        // For backward compatibility AstNodeArrayDType and others inherit
        // width and signing from the subDType/base type
        widthFromSub(subDTypep());
    }
    AstUnpackArrayDType(FileLine* fl, AstNodeDType* dtp, AstRange* rangep)
        : ASTGEN_SUPER(fl) {
        refDTypep(dtp);
        setOp2p(rangep);
        dtypep(this);
        // For backward compatibility AstNodeArrayDType and others inherit
        // width and signing from the subDType/base type
        widthFromSub(subDTypep());
    }
    ASTNODE_NODE_FUNCS(UnpackArrayDType)
    virtual string prettyDTypeName() const override;
    virtual bool same(const AstNode* samep) const override {
        const AstUnpackArrayDType* sp = static_cast<const AstUnpackArrayDType*>(samep);
        return m_isCompound == sp->m_isCompound;
    }
    // Outer dimension comes first. The first element is this node.
    std::vector<AstUnpackArrayDType*> unpackDimensions();
    void isCompound(bool flag) { m_isCompound = flag; }
    virtual bool isCompound() const override { return m_isCompound; }
};

class AstUnsizedArrayDType final : public AstNodeDType {
    // Unsized/open-range Array data type, ie "some_dtype var_name []"
    // Children: DTYPE (moved to refDTypep() in V3Width)
private:
    AstNodeDType* m_refDTypep;  // Elements of this type (after widthing)
public:
    AstUnsizedArrayDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp)
        : ASTGEN_SUPER(fl) {
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
    virtual bool same(const AstNode* samep) const override {
        const AstNodeArrayDType* asamep = static_cast<const AstNodeArrayDType*>(samep);
        if (!asamep->subDTypep()) return false;
        return (subDTypep() == asamep->subDTypep());
    }
    virtual bool similarDType(AstNodeDType* samep) const override {
        const AstNodeArrayDType* asamep = static_cast<const AstNodeArrayDType*>(samep);
        return type() == samep->type() && asamep->subDTypep()
               && subDTypep()->skipRefp()->similarDType(asamep->subDTypep()->skipRefp());
    }
    virtual void dumpSmall(std::ostream& str) const override;
    virtual V3Hash sameHash() const override { return V3Hash(m_refDTypep); }
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    // op1 = Range of variable
    AstNodeDType* childDTypep() const { return VN_CAST(op1p(), NodeDType); }
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

class AstBasicDType final : public AstNodeDType {
    // Builtin atomic/vectored data type
    // Children: RANGE (converted to constant in V3Width)
private:
    struct Members {
        AstBasicDTypeKwd m_keyword;  // (also in VBasicTypeKey) What keyword created basic type
        VNumRange m_nrange;  // (also in VBasicTypeKey) Numeric msb/lsb (if non-opaque keyword)
        bool operator==(const Members& rhs) const {
            return rhs.m_keyword == m_keyword && rhs.m_nrange == m_nrange;
        }
    } m;
    // See also in AstNodeDType: m_width, m_widthMin, m_numeric(issigned)
public:
    AstBasicDType(FileLine* fl, AstBasicDTypeKwd kwd, const VSigning& signst = VSigning::NOSIGN)
        : ASTGEN_SUPER(fl) {
        init(kwd, signst, 0, -1, nullptr);
    }
    AstBasicDType(FileLine* fl, VFlagLogicPacked, int wantwidth)
        : ASTGEN_SUPER(fl) {
        init(AstBasicDTypeKwd::LOGIC, VSigning::NOSIGN, wantwidth, -1, nullptr);
    }
    AstBasicDType(FileLine* fl, VFlagBitPacked, int wantwidth)
        : ASTGEN_SUPER(fl) {
        init(AstBasicDTypeKwd::BIT, VSigning::NOSIGN, wantwidth, -1, nullptr);
    }
    AstBasicDType(FileLine* fl, AstBasicDTypeKwd kwd, VSigning numer, int wantwidth, int widthmin)
        : ASTGEN_SUPER(fl) {
        init(kwd, numer, wantwidth, widthmin, nullptr);
    }
    AstBasicDType(FileLine* fl, AstBasicDTypeKwd kwd, VSigning numer, VNumRange range,
                  int widthmin)
        : ASTGEN_SUPER(fl) {
        init(kwd, numer, range.elements(), widthmin, nullptr);
        m.m_nrange = range;  // as init() presumes lsb==0, but range.lsb() might not be
    }
    // See also addRange in verilog.y
private:
    void init(AstBasicDTypeKwd kwd, VSigning numer, int wantwidth, int wantwidthmin,
              AstRange* rangep) {
        // wantwidth=0 means figure it out, but if a widthmin is >=0
        //    we allow width 0 so that {{0{x}},y} works properly
        // wantwidthmin=-1:  default, use wantwidth if it is non zero
        m.m_keyword = kwd;
        // Implicitness: // "parameter X" is implicit and sized from initial
        // value, "parameter reg x" not
        if (keyword() == AstBasicDTypeKwd::LOGIC_IMPLICIT) {
            if (rangep || wantwidth) m.m_keyword = AstBasicDTypeKwd::LOGIC;
        }
        if (numer == VSigning::NOSIGN) {
            if (keyword().isSigned()) {
                numer = VSigning::SIGNED;
            } else if (keyword().isUnsigned()) {
                numer = VSigning::UNSIGNED;
            }
        }
        numeric(numer);
        if (!rangep && (wantwidth || wantwidthmin >= 0)) {  // Constant width
            if (wantwidth > 1) m.m_nrange.init(wantwidth - 1, 0, false);
            int wmin = wantwidthmin >= 0 ? wantwidthmin : wantwidth;
            widthForce(wantwidth, wmin);
        } else if (!rangep) {  // Set based on keyword properties
            // V3Width will pull from this width
            if (keyword().width() > 1 && !isOpaque()) {
                m.m_nrange.init(keyword().width() - 1, 0, false);
            }
            widthForce(keyword().width(), keyword().width());
        } else {
            widthForce(rangep->elementsConst(),
                       rangep->elementsConst());  // Maybe unknown if parameters underneath it
        }
        setNOp1p(rangep);
        dtypep(this);
    }

public:
    ASTNODE_NODE_FUNCS(BasicDType)
    virtual void dump(std::ostream& str) const override;
    virtual V3Hash sameHash() const override {
        return V3Hash(V3Hash(m.m_keyword), V3Hash(m.m_nrange.hi()));
    }
    // width/widthMin/numeric compared elsewhere
    virtual bool same(const AstNode* samep) const override {
        const AstBasicDType* sp = static_cast<const AstBasicDType*>(samep);
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
    virtual bool isHeavy() const override { return keyword() == AstBasicDTypeKwd::STRING; }
    AstRange* rangep() const { return VN_CAST(op1p(), Range); }  // op1 = Range of variable
    void rangep(AstRange* nodep) { setNOp1p(nodep); }
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
    AstBasicDTypeKwd keyword() const {  // Avoid using - use isSomething accessors instead
        return m.m_keyword;
    }
    bool isBitLogic() const { return keyword().isBitLogic(); }
    bool isDouble() const { return keyword().isDouble(); }
    bool isEventValue() const { return keyword().isEventValue(); }
    bool isOpaque() const { return keyword().isOpaque(); }
    bool isString() const { return keyword().isString(); }
    bool isSloppy() const { return keyword().isSloppy(); }
    bool isZeroInit() const { return keyword().isZeroInit(); }
    bool isRanged() const { return rangep() || m.m_nrange.ranged(); }
    bool isDpiBitVec() const {  // DPI uses svBitVecVal
        return keyword() == AstBasicDTypeKwd::BIT && isRanged();
    }
    bool isDpiLogicVec() const {  // DPI uses svLogicVecVal
        return keyword().isFourstate() && !(keyword() == AstBasicDTypeKwd::LOGIC && !isRanged());
    }
    bool isDpiPrimitive() const {  // DPI uses a primitive type
        return !isDpiBitVec() && !isDpiLogicVec();
    }
    // Generally the lo/hi/left/right funcs should be used instead of nrange()
    const VNumRange& nrange() const { return m.m_nrange; }
    int hi() const { return (rangep() ? rangep()->hiConst() : m.m_nrange.hi()); }
    int lo() const { return (rangep() ? rangep()->loConst() : m.m_nrange.lo()); }
    int elements() const { return (rangep() ? rangep()->elementsConst() : m.m_nrange.elements()); }
    int left() const { return littleEndian() ? lo() : hi(); }  // How to show a declaration
    int right() const { return littleEndian() ? hi() : lo(); }
    bool littleEndian() const {
        return (rangep() ? rangep()->littleEndian() : m.m_nrange.littleEndian());
    }
    bool implicit() const { return keyword() == AstBasicDTypeKwd::LOGIC_IMPLICIT; }
    VNumRange declRange() const { return isRanged() ? VNumRange{left(), right()} : VNumRange{}; }
    void cvtRangeConst() {  // Convert to smaller representation
        if (rangep() && VN_IS(rangep()->leftp(), Const) && VN_IS(rangep()->rightp(), Const)) {
            m.m_nrange = VNumRange{rangep()->leftConst(), rangep()->rightConst()};
            rangep()->unlinkFrBackWithNext()->deleteTree();
            rangep(nullptr);
        }
    }
    virtual bool isCompound() const override { return isString(); }
};

class AstConstDType final : public AstNodeDType {
    // const data type, ie "const some_dtype var_name [2:0]"
    // ConstDType are removed in V3LinkLValue and become AstVar::isConst.
    // When more generic types are supported AstConstDType will be propagated further.
private:
    AstNodeDType* m_refDTypep;  // Inherit from this base data type
public:
    AstConstDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp)
        : ASTGEN_SUPER(fl) {
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
        const AstConstDType* sp = static_cast<const AstConstDType*>(samep);
        return (m_refDTypep == sp->m_refDTypep);
    }
    virtual bool similarDType(AstNodeDType* samep) const override {
        return skipRefp()->similarDType(samep->skipRefp());
    }
    virtual V3Hash sameHash() const override {
        return V3Hash(m_refDTypep);
    }  // node's type() included elsewhere
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    // op1 = Range of variable
    AstNodeDType* childDTypep() const { return VN_CAST(op1p(), NodeDType); }
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

class AstClassRefDType final : public AstNodeDType {
    // Reference to a class
    // Children: PINs (for parameter settings)
private:
    AstClass* m_classp;  // data type pointed to, BELOW the AstTypedef
    AstNodeModule* m_classOrPackagep = nullptr;  // Package hierarchy
public:
    AstClassRefDType(FileLine* fl, AstClass* classp, AstNode* paramsp)
        : ASTGEN_SUPER(fl)
        , m_classp{classp} {
        dtypep(this);
        addNOp4p(paramsp);
    }
    ASTNODE_NODE_FUNCS(ClassRefDType)
    // METHODS
    virtual const char* broken() const override {
        BROKEN_RTN(m_classp && !m_classp->brokeExists());
        return nullptr;
    }
    virtual void cloneRelink() override {
        if (m_classp && m_classp->clonep()) m_classp = m_classp->clonep();
    }
    virtual bool same(const AstNode* samep) const override {
        const AstClassRefDType* asamep = static_cast<const AstClassRefDType*>(samep);
        return (m_classp == asamep->m_classp && m_classOrPackagep == asamep->m_classOrPackagep);
    }
    virtual bool similarDType(AstNodeDType* samep) const override {
        return this == samep || (type() == samep->type() && same(samep));
    }
    virtual V3Hash sameHash() const override {
        return V3Hash(V3Hash(m_classp), V3Hash(m_classOrPackagep));
    }
    virtual void dump(std::ostream& str = std::cout) const override;
    virtual void dumpSmall(std::ostream& str) const override;
    virtual string name() const override { return classp() ? classp()->name() : "<unlinked>"; }
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
    AstPin* paramsp() const { return VN_CAST(op4p(), Pin); }
    virtual bool isCompound() const override { return true; }
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
        : ASTGEN_SUPER(fl)
        , m_modportFileline{nullptr}
        , m_cellName{cellName}
        , m_ifaceName{ifaceName}
        , m_modportName{""} {}
    AstIfaceRefDType(FileLine* fl, FileLine* modportFl, const string& cellName,
                     const string& ifaceName, const string& modport)
        : ASTGEN_SUPER(fl)
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
    virtual V3Hash sameHash() const override { return V3Hash(m_cellp); }
    virtual int widthAlignBytes() const override { return 1; }
    virtual int widthTotalBytes() const override { return 1; }
    FileLine* modportFileline() const { return m_modportFileline; }
    string cellName() const { return m_cellName; }
    void cellName(const string& name) { m_cellName = name; }
    string ifaceName() const { return m_ifaceName; }
    void ifaceName(const string& name) { m_ifaceName = name; }
    string modportName() const { return m_modportName; }
    void modportName(const string& name) { m_modportName = name; }
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

class AstQueueDType final : public AstNodeDType {
    // Queue array data type, ie "[ $ ]"
    // Children: DTYPE (moved to refDTypep() in V3Width)
private:
    AstNodeDType* m_refDTypep;  // Elements of this type (after widthing)
public:
    AstQueueDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp, AstNode* boundp)
        : ASTGEN_SUPER(fl) {
        setNOp2p(boundp);
        childDTypep(dtp);  // Only for parser
        refDTypep(nullptr);
        dtypep(nullptr);  // V3Width will resolve
    }
    AstQueueDType(FileLine* fl, AstNodeDType* dtp, AstNode* boundp)
        : ASTGEN_SUPER(fl) {
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
        const AstQueueDType* asamep = static_cast<const AstQueueDType*>(samep);
        if (!asamep->subDTypep()) return false;
        return (subDTypep() == asamep->subDTypep());
    }
    virtual bool similarDType(AstNodeDType* samep) const override {
        const AstQueueDType* asamep = static_cast<const AstQueueDType*>(samep);
        return type() == samep->type() && asamep->subDTypep()
               && subDTypep()->skipRefp()->similarDType(asamep->subDTypep()->skipRefp());
    }
    virtual void dumpSmall(std::ostream& str) const override;
    virtual V3Hash sameHash() const override { return V3Hash(m_refDTypep); }
    virtual string prettyDTypeName() const override;
    virtual bool isHeavy() const override { return true; }
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    // op1 = Range of variable
    AstNodeDType* childDTypep() const { return VN_CAST(op1p(), NodeDType); }
    void childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    virtual AstNodeDType* subDTypep() const override {
        return m_refDTypep ? m_refDTypep : childDTypep();
    }
    void refDTypep(AstNodeDType* nodep) { m_refDTypep = nodep; }
    AstNode* boundp() const { return op2p(); }  // op2 = Bound, nullptr = none
    void boundp(AstNode* nodep) { setNOp2p(nodep); }
    int boundConst() const {
        AstConst* constp = VN_CAST(boundp(), Const);
        return (constp ? constp->toSInt() : 0);
    }
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
        : ASTGEN_SUPER(fl)
        , m_name{name} {}
    AstRefDType(FileLine* fl, const string& name, AstNode* classOrPackagep, AstNode* paramsp)
        : ASTGEN_SUPER(fl)
        , m_name{name} {
        setNOp3p(classOrPackagep);
        addNOp4p(paramsp);
    }
    class FlagTypeOfExpr {};  // type(expr) for parser only
    AstRefDType(FileLine* fl, FlagTypeOfExpr, AstNode* typeofp)
        : ASTGEN_SUPER(fl) {
        setOp2p(typeofp);
    }
    ASTNODE_NODE_FUNCS(RefDType)
    // METHODS
    virtual const char* broken() const override {
        BROKEN_RTN(m_typedefp && !m_typedefp->brokeExists());
        BROKEN_RTN(m_refDTypep && !m_refDTypep->brokeExists());
        return nullptr;
    }
    virtual void cloneRelink() override {
        if (m_typedefp && m_typedefp->clonep()) m_typedefp = m_typedefp->clonep();
        if (m_refDTypep && m_refDTypep->clonep()) m_refDTypep = m_refDTypep->clonep();
    }
    virtual bool same(const AstNode* samep) const override {
        const AstRefDType* asamep = static_cast<const AstRefDType*>(samep);
        return (m_typedefp == asamep->m_typedefp && m_refDTypep == asamep->m_refDTypep
                && m_name == asamep->m_name && m_classOrPackagep == asamep->m_classOrPackagep);
    }
    virtual bool similarDType(AstNodeDType* samep) const override {
        return skipRefp()->similarDType(samep->skipRefp());
    }
    virtual V3Hash sameHash() const override {
        return V3Hash(V3Hash(m_typedefp), V3Hash(m_classOrPackagep));
    }
    virtual void dump(std::ostream& str = std::cout) const override;
    virtual string name() const override { return m_name; }
    virtual string prettyDTypeName() const override {
        return subDTypep() ? subDTypep()->name() : prettyName();
    }
    virtual AstBasicDType* basicp() const override {
        return subDTypep() ? subDTypep()->basicp() : nullptr;
    }
    virtual AstNodeDType* subDTypep() const override {
        if (typedefp()) return typedefp()->subDTypep();
        return refDTypep();  // Maybe nullptr
    }
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
    AstPin* paramsp() const { return VN_CAST(op4p(), Pin); }
    virtual bool isCompound() const override {
        v3fatalSrc("call isCompound on subdata type, not reference");
        return false;
    }
};

class AstStructDType final : public AstNodeUOrStructDType {
public:
    // VSigning below is mispurposed to indicate if packed or not
    AstStructDType(FileLine* fl, VSigning numericUnpack)
        : ASTGEN_SUPER(fl, numericUnpack) {}
    ASTNODE_NODE_FUNCS(StructDType)
    virtual string verilogKwd() const override { return "struct"; }
};

class AstUnionDType final : public AstNodeUOrStructDType {
public:
    // UNSUP: bool isTagged;
    // VSigning below is mispurposed to indicate if packed or not
    AstUnionDType(FileLine* fl, VSigning numericUnpack)
        : ASTGEN_SUPER(fl, numericUnpack) {}
    ASTNODE_NODE_FUNCS(UnionDType)
    virtual string verilogKwd() const override { return "union"; }
};

class AstMemberDType final : public AstNodeDType {
    // A member of a struct/union
    // PARENT: AstNodeUOrStructDType
private:
    AstNodeDType* m_refDTypep;  // Elements of this type (after widthing)
    string m_name;  // Name of variable
    string m_tag;  // Holds the string of the verilator tag -- used in XML output.
    int m_lsb = -1;  // Within this level's packed struct, the LSB of the first bit of the member
    // UNSUP: int m_randType;    // Randomization type (IEEE)
public:
    AstMemberDType(FileLine* fl, const string& name, VFlagChildDType, AstNodeDType* dtp)
        : ASTGEN_SUPER(fl)
        , m_name{name} {
        childDTypep(dtp);  // Only for parser
        dtypep(nullptr);  // V3Width will resolve
        refDTypep(nullptr);
    }
    AstMemberDType(FileLine* fl, const string& name, AstNodeDType* dtp)
        : ASTGEN_SUPER(fl)
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
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    // op1 = Range of variable
    AstNodeDType* childDTypep() const { return VN_CAST(op1p(), NodeDType); }
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

class AstVoidDType final : public AstNodeDType {
    // For e.g. a function returning void
public:
    explicit AstVoidDType(FileLine* fl)
        : ASTGEN_SUPER(fl) {
        dtypep(this);
    }
    ASTNODE_NODE_FUNCS(VoidDType)
    virtual void dumpSmall(std::ostream& str) const override;
    virtual bool hasDType() const override { return true; }
    virtual bool maybePointedTo() const override { return true; }
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
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool isCompound() const override { return false; }
};

class AstEnumItem final : public AstNode {
private:
    string m_name;

public:
    // Parents: ENUM
    AstEnumItem(FileLine* fl, const string& name, AstNode* rangep, AstNode* initp)
        : ASTGEN_SUPER(fl)
        , m_name{name} {
        addNOp1p(rangep);
        addNOp2p(initp);
    }
    ASTNODE_NODE_FUNCS(EnumItem)
    virtual string name() const override { return m_name; }
    virtual bool maybePointedTo() const override { return true; }
    virtual bool hasDType() const override { return true; }
    virtual void name(const string& flag) override { m_name = flag; }
    AstRange* rangep() const { return VN_CAST(op1p(), Range); }  // op1 = Range for name appending
    void rangep(AstNode* nodep) { addOp1p(nodep); }
    AstNode* valuep() const { return op2p(); }  // op2 = Value
    void valuep(AstNode* nodep) { addOp2p(nodep); }
};

class AstEnumItemRef final : public AstNodeMath {
private:
    AstEnumItem* m_itemp;  // [AfterLink] Pointer to item
    AstNodeModule* m_classOrPackagep;  // Package hierarchy
public:
    AstEnumItemRef(FileLine* fl, AstEnumItem* itemp, AstNodeModule* classOrPackagep)
        : ASTGEN_SUPER(fl)
        , m_itemp{itemp}
        , m_classOrPackagep{classOrPackagep} {
        dtypeFrom(m_itemp);
    }
    ASTNODE_NODE_FUNCS(EnumItemRef)
    virtual void dump(std::ostream& str) const override;
    virtual string name() const override { return itemp()->name(); }
    virtual const char* broken() const override {
        BROKEN_RTN(!VN_IS(itemp(), EnumItem));
        return nullptr;
    }
    virtual int instrCount() const override { return 0; }
    virtual void cloneRelink() override {
        if (m_itemp->clonep()) m_itemp = VN_CAST(m_itemp->clonep(), EnumItem);
    }
    virtual bool same(const AstNode* samep) const override {
        const AstEnumItemRef* sp = static_cast<const AstEnumItemRef*>(samep);
        return itemp() == sp->itemp();
    }
    AstEnumItem* itemp() const { return m_itemp; }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    AstNodeModule* classOrPackagep() const { return m_classOrPackagep; }
    void classOrPackagep(AstNodeModule* nodep) { m_classOrPackagep = nodep; }
};

class AstEnumDType final : public AstNodeDType {
    // Parents: TYPEDEF/MODULE
    // Children: ENUMVALUEs
private:
    string m_name;  // Name from upper typedef, if any
    AstNodeDType* m_refDTypep;  // Elements are of this type after V3Width
    int m_uniqueNum;

public:
    AstEnumDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp, AstNode* itemsp)
        : ASTGEN_SUPER(fl) {
        childDTypep(dtp);  // Only for parser
        refDTypep(nullptr);
        addNOp2p(itemsp);
        dtypep(nullptr);  // V3Width will resolve
        widthFromSub(subDTypep());
        m_uniqueNum = uniqueNumInc();
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
    virtual bool same(const AstNode* samep) const override {
        const AstEnumDType* sp = static_cast<const AstEnumDType*>(samep);
        return m_uniqueNum == sp->m_uniqueNum;
    }
    virtual bool similarDType(AstNodeDType* samep) const override { return this == samep; }
    virtual V3Hash sameHash() const override { return V3Hash(m_uniqueNum); }
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    AstNodeDType* childDTypep() const { return VN_CAST(op1p(), NodeDType); }  // op1 = Data type
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
    AstEnumItem* itemsp() const { return VN_CAST(op2p(), EnumItem); }  // op2 = AstEnumItem's
    void addValuesp(AstNode* nodep) { addOp2p(nodep); }
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

class AstParseTypeDType final : public AstNodeDType {
    // Parents: VAR
    // During parsing, this indicates the type of a parameter is a "parameter type"
    // e.g. the data type is a container of any data type
public:
    explicit AstParseTypeDType(FileLine* fl)
        : ASTGEN_SUPER(fl) {}
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

//######################################################################

class AstArraySel final : public AstNodeSel {
    // Parents: math|stmt
    // Children: varref|arraysel, math
private:
    void init(AstNode* fromp) {
        if (fromp && VN_IS(fromp->dtypep()->skipRefp(), NodeArrayDType)) {
            // Strip off array to find what array references
            dtypeFrom(VN_CAST(fromp->dtypep()->skipRefp(), NodeArrayDType)->subDTypep());
        }
    }

public:
    AstArraySel(FileLine* fl, AstNode* fromp, AstNode* bitp)
        : ASTGEN_SUPER(fl, fromp, bitp) {
        init(fromp);
    }
    AstArraySel(FileLine* fl, AstNode* fromp, int bit)
        : ASTGEN_SUPER(fl, fromp, new AstConst(fl, bit)) {
        init(fromp);
    }
    ASTNODE_NODE_FUNCS(ArraySel)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstArraySel(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        V3ERROR_NA; /* How can from be a const? */
    }
    virtual string emitVerilog() override { return "%k(%l%f[%r])"; }
    virtual string emitC() override { return "%li%k[%ri]"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool isGateOptimizable() const override {
        return true;
    }  // esp for V3Const::ifSameAssign
    virtual bool isPredictOptimizable() const override { return true; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    virtual int instrCount() const override { return widthInstrs(); }
    // Special operators
    // Return base var (or const) nodep dereferences
    static AstNode* baseFromp(AstNode* nodep, bool overMembers);
};

class AstAssocSel final : public AstNodeSel {
    // Parents: math|stmt
    // Children: varref|arraysel, math
private:
    void init(AstNode* fromp) {
        if (fromp && VN_IS(fromp->dtypep()->skipRefp(), AssocArrayDType)) {
            // Strip off array to find what array references
            dtypeFrom(VN_CAST(fromp->dtypep()->skipRefp(), AssocArrayDType)->subDTypep());
        }
    }

public:
    AstAssocSel(FileLine* fl, AstNode* fromp, AstNode* bitp)
        : ASTGEN_SUPER(fl, fromp, bitp) {
        init(fromp);
    }
    ASTNODE_NODE_FUNCS(AssocSel)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstAssocSel(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        V3ERROR_NA;
    }
    virtual string emitVerilog() override { return "%k(%l%f[%r])"; }
    virtual string emitC() override { return "%li%k[%ri]"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool isGateOptimizable() const override {
        return true;
    }  // esp for V3Const::ifSameAssign
    virtual bool isPredictOptimizable() const override { return false; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    virtual int instrCount() const override { return widthInstrs(); }
};

class AstWordSel final : public AstNodeSel {
    // Select a single word from a multi-word wide value
public:
    AstWordSel(FileLine* fl, AstNode* fromp, AstNode* bitp)
        : ASTGEN_SUPER(fl, fromp, bitp) {
        dtypeSetUInt32();  // Always used on WData arrays so returns edata size
    }
    ASTNODE_NODE_FUNCS(WordSel)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstWordSel(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& from, const V3Number& bit) override {
        V3ERROR_NA;
    }
    virtual string emitVerilog() override { return "%k(%l%f[%r])"; }
    virtual string emitC() override {
        return "%li[%ri]";
    }  // Not %k, as usually it's a small constant rhsp
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
};

class AstSelLoopVars final : public AstNode {
    // Parser only concept "[id, id, id]" for a foreach statement
    // Unlike normal selects elements is a list
public:
    AstSelLoopVars(FileLine* fl, AstNode* fromp, AstNode* elementsp)
        : ASTGEN_SUPER(fl) {
        setOp1p(fromp);
        addNOp2p(elementsp);
    }
    ASTNODE_NODE_FUNCS(SelLoopVars)
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    virtual bool maybePointedTo() const override { return false; }
    AstNode* fromp() const { return op1p(); }
    AstNode* elementsp() const { return op2p(); }
};

class AstSelExtract final : public AstNodePreSel {
    // Range extraction, gets replaced with AstSel
public:
    AstSelExtract(FileLine* fl, AstNode* fromp, AstNode* msbp, AstNode* lsbp)
        : ASTGEN_SUPER(fl, fromp, msbp, lsbp) {}
    ASTNODE_NODE_FUNCS(SelExtract)
    AstNode* leftp() const { return rhsp(); }
    AstNode* rightp() const { return thsp(); }
};

class AstSelBit final : public AstNodePreSel {
    // Single bit range extraction, perhaps with non-constant selection or array selection
    // Gets replaced during link with AstArraySel or AstSel
public:
    AstSelBit(FileLine* fl, AstNode* fromp, AstNode* bitp)
        : ASTGEN_SUPER(fl, fromp, bitp, nullptr) {
        UASSERT_OBJ(!v3Global.assertDTypesResolved(), this,
                    "not coded to create after dtypes resolved");
    }
    ASTNODE_NODE_FUNCS(SelBit)
    AstNode* bitp() const { return rhsp(); }
};

class AstSelPlus final : public AstNodePreSel {
    // +: range extraction, perhaps with non-constant selection
    // Gets replaced during link with AstSel
public:
    AstSelPlus(FileLine* fl, AstNode* fromp, AstNode* bitp, AstNode* widthp)
        : ASTGEN_SUPER(fl, fromp, bitp, widthp) {}
    ASTNODE_NODE_FUNCS(SelPlus)
    AstNode* bitp() const { return rhsp(); }
    AstNode* widthp() const { return thsp(); }
};

class AstSelMinus final : public AstNodePreSel {
    // -: range extraction, perhaps with non-constant selection
    // Gets replaced during link with AstSel
public:
    AstSelMinus(FileLine* fl, AstNode* fromp, AstNode* bitp, AstNode* widthp)
        : ASTGEN_SUPER(fl, fromp, bitp, widthp) {}
    ASTNODE_NODE_FUNCS(SelMinus)
    AstNode* bitp() const { return rhsp(); }
    AstNode* widthp() const { return thsp(); }
};

class AstSel final : public AstNodeTriop {
    // Multiple bit range extraction
    // Parents: math|stmt
    // Children: varref|arraysel, math, constant math
    // Tempting to have an access() style method here as LHS selects are quite
    // different, but that doesn't play well with V3Inst and bidirects which don't know direction
private:
    VNumRange m_declRange;  // Range of the 'from' array if isRanged() is set, else invalid
    int m_declElWidth;  // If a packed array, the number of bits per element
public:
    AstSel(FileLine* fl, AstNode* fromp, AstNode* lsbp, AstNode* widthp)
        : ASTGEN_SUPER(fl, fromp, lsbp, widthp)
        , m_declElWidth{1} {
        if (VN_IS(widthp, Const)) {
            dtypeSetLogicSized(VN_CAST(widthp, Const)->toUInt(), VSigning::UNSIGNED);
        }
    }
    AstSel(FileLine* fl, AstNode* fromp, int lsb, int bitwidth)
        : ASTGEN_SUPER(fl, fromp, new AstConst(fl, lsb), new AstConst(fl, bitwidth))
        , m_declElWidth{1} {
        dtypeSetLogicSized(bitwidth, VSigning::UNSIGNED);
    }
    ASTNODE_NODE_FUNCS(Sel)
    virtual void dump(std::ostream& str) const override;
    virtual void numberOperate(V3Number& out, const V3Number& from, const V3Number& bit,
                               const V3Number& width) override {
        out.opSel(from, bit.toUInt() + width.toUInt() - 1, bit.toUInt());
    }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override {
        return this->widthp()->isOne() ? "VL_BITSEL_%nq%lq%rq%tq(%nw,%lw,%rw,%tw, %P, %li, %ri)"
                                       : "VL_SEL_%nq%lq%rq%tq(%nw,%lw,%rw,%tw, %P, %li, %ri, %ti)";
    }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool cleanThs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool sizeMattersThs() const override { return false; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode*) const override { return true; }
    virtual int instrCount() const override {
        return widthInstrs() * (VN_CAST(lsbp(), Const) ? 3 : 10);
    }
    AstNode* fromp() const {
        return op1p();
    }  // op1 = Extracting what (nullptr=TBD during parsing)
    AstNode* lsbp() const { return op2p(); }  // op2 = Msb selection expression
    AstNode* widthp() const { return op3p(); }  // op3 = Width
    int widthConst() const { return VN_CAST(widthp(), Const)->toSInt(); }
    int lsbConst() const { return VN_CAST(lsbp(), Const)->toSInt(); }
    int msbConst() const { return lsbConst() + widthConst() - 1; }
    VNumRange& declRange() { return m_declRange; }
    const VNumRange& declRange() const { return m_declRange; }
    void declRange(const VNumRange& flag) { m_declRange = flag; }
    int declElWidth() const { return m_declElWidth; }
    void declElWidth(int flag) { m_declElWidth = flag; }
};

class AstSliceSel final : public AstNodeTriop {
    // Multiple array element extraction
    // Parents: math|stmt
    // Children: varref|arraysel, math, constant math
private:
    VNumRange m_declRange;  // Range of the 'from' array if isRanged() is set, else invalid
public:
    AstSliceSel(FileLine* fl, AstNode* fromp, const VNumRange& declRange)
        : ASTGEN_SUPER(fl, fromp, new AstConst(fl, declRange.lo()),
                       new AstConst(fl, declRange.elements()))
        , m_declRange{declRange} {}
    ASTNODE_NODE_FUNCS(SliceSel)
    virtual void dump(std::ostream& str) const override;
    virtual void numberOperate(V3Number& out, const V3Number& from, const V3Number& lo,
                               const V3Number& width) override {
        V3ERROR_NA;
    }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }  // Removed before EmitC
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool cleanThs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool sizeMattersThs() const override { return false; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode*) const override { return true; }
    virtual int instrCount() const override { return 10; }  // Removed before matters
    AstNode* fromp() const {
        return op1p();
    }  // op1 = Extracting what (nullptr=TBD during parsing)
    // For widthConst()/loConst etc, see declRange().elements() and other VNumRange methods
    VNumRange& declRange() { return m_declRange; }
    const VNumRange& declRange() const { return m_declRange; }
    void declRange(const VNumRange& flag) { m_declRange = flag; }
};

class AstMethodCall final : public AstNodeFTaskRef {
    // A reference to a member task (or function)
    // PARENTS: stmt/math
    // Not all calls are statments vs math.  AstNodeStmt needs isStatement() to deal.
    // Don't need the class we are extracting from, as the "fromp()"'s datatype can get us to it
public:
    AstMethodCall(FileLine* fl, AstNode* fromp, VFlagChildDType, const string& name,
                  AstNode* pinsp)
        : ASTGEN_SUPER(fl, false, name, pinsp) {
        setOp2p(fromp);
        dtypep(nullptr);  // V3Width will resolve
    }
    AstMethodCall(FileLine* fl, AstNode* fromp, const string& name, AstNode* pinsp)
        : ASTGEN_SUPER(fl, false, name, pinsp) {
        setOp2p(fromp);
    }
    ASTNODE_NODE_FUNCS(MethodCall)
    virtual const char* broken() const override {
        BROKEN_BASE_RTN(AstNodeFTaskRef::broken());
        BROKEN_RTN(!fromp());
        return nullptr;
    }
    virtual void dump(std::ostream& str) const override;
    virtual bool hasDType() const override { return true; }
    void makeStatement() {
        statement(true);
        dtypeSetVoid();
    }
    AstNode* fromp() const {
        return op2p();
    }  // op2 = Extracting what (nullptr=TBD during parsing)
    void fromp(AstNode* nodep) { setOp2p(nodep); }
};

class AstCMethodHard final : public AstNodeStmt {
    // A reference to a "C" hardcoded member task (or function)
    // PARENTS: stmt/math
    // Not all calls are statments vs math.  AstNodeStmt needs isStatement() to deal.
private:
    string m_name;  // Name of method
    bool m_pure = false;  // Pure optimizable
public:
    AstCMethodHard(FileLine* fl, AstNode* fromp, VFlagChildDType, const string& name,
                   AstNode* pinsp)
        : ASTGEN_SUPER(fl, false)
        , m_name{name} {
        setOp1p(fromp);
        dtypep(nullptr);  // V3Width will resolve
        addNOp2p(pinsp);
    }
    AstCMethodHard(FileLine* fl, AstNode* fromp, const string& name, AstNode* pinsp)
        : ASTGEN_SUPER(fl, false)
        , m_name{name} {
        setOp1p(fromp);
        addNOp2p(pinsp);
    }
    ASTNODE_NODE_FUNCS(CMethodHard)
    virtual string name() const override { return m_name; }  // * = Var name
    virtual bool hasDType() const override { return true; }
    virtual void name(const string& name) override { m_name = name; }
    virtual V3Hash sameHash() const override { return V3Hash(m_name); }
    virtual bool same(const AstNode* samep) const override {
        const AstCMethodHard* asamep = static_cast<const AstCMethodHard*>(samep);
        return (m_name == asamep->m_name);
    }
    virtual bool isPure() const override { return m_pure; }
    void pure(bool flag) { m_pure = flag; }
    void makeStatement() {
        statement(true);
        dtypeSetVoid();
    }
    AstNode* fromp() const {
        return op1p();
    }  // op1 = Extracting what (nullptr=TBD during parsing)
    void fromp(AstNode* nodep) { setOp1p(nodep); }
    AstNode* pinsp() const { return op2p(); }  // op2 = Pin interconnection list
    void addPinsp(AstNode* nodep) { addOp2p(nodep); }
};

class AstVar final : public AstNode {
    // A variable (in/out/wire/reg/param) inside a module
private:
    string m_name;  // Name of variable
    string m_origName;  // Original name before dot addition
    string m_tag;  // Holds the string of the verilator tag -- used in XML output.
    AstVarType m_varType;  // Type of variable
    VDirection m_direction;  // Direction input/output etc
    VDirection m_declDirection;  // Declared direction input/output etc
    AstBasicDTypeKwd m_declKwd;  // Keyword at declaration time
    bool m_ansi : 1;  // ANSI port list variable (for dedup check)
    bool m_declTyped : 1;  // Declared as type (for dedup check)
    bool m_tristate : 1;  // Inout or triwire or trireg
    bool m_primaryIO : 1;  // In/out to top level (or directly assigned from same)
    bool m_sc : 1;  // SystemC variable
    bool m_scClocked : 1;  // SystemC sc_clk<> needed
    bool m_scSensitive : 1;  // SystemC sensitive() needed
    bool m_sigPublic : 1;  // User C code accesses this signal or is top signal
    bool m_sigModPublic : 1;  // User C code accesses this signal and module
    bool m_sigUserRdPublic : 1;  // User C code accesses this signal, read only
    bool m_sigUserRWPublic : 1;  // User C code accesses this signal, read-write
    bool m_usedClock : 1;  // Signal used as a clock
    bool m_usedParam : 1;  // Parameter is referenced (on link; later signals not setup)
    bool m_usedLoopIdx : 1;  // Variable subject of for unrolling
    bool m_funcLocal : 1;  // Local variable for a function
    bool m_funcReturn : 1;  // Return variable for a function
    bool m_attrClockEn : 1;  // User clock enable attribute
    bool m_attrScBv : 1;  // User force bit vector attribute
    bool m_attrIsolateAssign : 1;  // User isolate_assignments attribute
    bool m_attrSFormat : 1;  // User sformat attribute
    bool m_attrSplitVar : 1;  // declared with split_var metacomment
    bool m_fileDescr : 1;  // File descriptor
    bool m_isRand : 1;  // Random variable
    bool m_isConst : 1;  // Table contains constant data
    bool m_isStatic : 1;  // Static C variable (for Verilog see instead isAutomatic)
    bool m_isPulldown : 1;  // Tri0
    bool m_isPullup : 1;  // Tri1
    bool m_isIfaceParent : 1;  // dtype is reference to interface present in this module
    bool m_isDpiOpenArray : 1;  // DPI import open array
    bool m_isHideLocal : 1;  // Verilog local
    bool m_isHideProtected : 1;  // Verilog protected
    bool m_noReset : 1;  // Do not do automated reset/randomization
    bool m_noSubst : 1;  // Do not substitute out references
    bool m_overridenParam : 1;  // Overridden parameter by #(...) or defparam
    bool m_trace : 1;  // Trace this variable
    bool m_isLatched : 1;  // Not assigned in all control paths of combo always
    VLifetime m_lifetime;  // Lifetime
    VVarAttrClocker m_attrClocker;
    MTaskIdSet m_mtaskIds;  // MTaskID's that read or write this var

    void init() {
        m_ansi = false;
        m_declTyped = false;
        m_tristate = false;
        m_primaryIO = false;
        m_sc = false;
        m_scClocked = false;
        m_scSensitive = false;
        m_usedClock = false;
        m_usedParam = false;
        m_usedLoopIdx = false;
        m_sigPublic = false;
        m_sigModPublic = false;
        m_sigUserRdPublic = false;
        m_sigUserRWPublic = false;
        m_funcLocal = false;
        m_funcReturn = false;
        m_attrClockEn = false;
        m_attrScBv = false;
        m_attrIsolateAssign = false;
        m_attrSFormat = false;
        m_attrSplitVar = false;
        m_fileDescr = false;
        m_isRand = false;
        m_isConst = false;
        m_isStatic = false;
        m_isPulldown = false;
        m_isPullup = false;
        m_isIfaceParent = false;
        m_isDpiOpenArray = false;
        m_isHideLocal = false;
        m_isHideProtected = false;
        m_noReset = false;
        m_noSubst = false;
        m_overridenParam = false;
        m_trace = false;
        m_isLatched = false;
        m_attrClocker = VVarAttrClocker::CLOCKER_UNKNOWN;
    }

public:
    AstVar(FileLine* fl, AstVarType type, const string& name, VFlagChildDType, AstNodeDType* dtp)
        : ASTGEN_SUPER(fl)
        , m_name{name}
        , m_origName{name} {
        init();
        combineType(type);
        childDTypep(dtp);  // Only for parser
        dtypep(nullptr);  // V3Width will resolve
        if (dtp->basicp()) {
            m_declKwd = dtp->basicp()->keyword();
        } else {
            m_declKwd = AstBasicDTypeKwd::LOGIC;
        }
    }
    AstVar(FileLine* fl, AstVarType type, const string& name, AstNodeDType* dtp)
        : ASTGEN_SUPER(fl)
        , m_name{name}
        , m_origName{name} {
        init();
        combineType(type);
        UASSERT(dtp, "AstVar created with no dtype");
        dtypep(dtp);
        if (dtp->basicp()) {
            m_declKwd = dtp->basicp()->keyword();
        } else {
            m_declKwd = AstBasicDTypeKwd::LOGIC;
        }
    }
    AstVar(FileLine* fl, AstVarType type, const string& name, VFlagLogicPacked, int wantwidth)
        : ASTGEN_SUPER(fl)
        , m_name{name}
        , m_origName{name} {
        init();
        combineType(type);
        dtypeSetLogicSized(wantwidth, VSigning::UNSIGNED);
        m_declKwd = AstBasicDTypeKwd::LOGIC;
    }
    AstVar(FileLine* fl, AstVarType type, const string& name, VFlagBitPacked, int wantwidth)
        : ASTGEN_SUPER(fl)
        , m_name{name}
        , m_origName{name} {
        init();
        combineType(type);
        dtypeSetBitSized(wantwidth, VSigning::UNSIGNED);
        m_declKwd = AstBasicDTypeKwd::BIT;
    }
    AstVar(FileLine* fl, AstVarType type, const string& name, AstVar* examplep)
        : ASTGEN_SUPER(fl)
        , m_name{name}
        , m_origName{name} {
        init();
        combineType(type);
        if (examplep->childDTypep()) childDTypep(examplep->childDTypep()->cloneTree(true));
        dtypeFrom(examplep);
        m_declKwd = examplep->declKwd();
    }
    ASTNODE_NODE_FUNCS(Var)
    virtual void dump(std::ostream& str) const override;
    virtual string name() const override { return m_name; }  // * = Var name
    virtual bool hasDType() const override { return true; }
    virtual bool maybePointedTo() const override { return true; }
    virtual string origName() const override { return m_origName; }  // * = Original name
    void origName(const string& name) { m_origName = name; }
    AstVarType varType() const { return m_varType; }  // * = Type of variable
    void direction(const VDirection& flag) {
        m_direction = flag;
        if (m_direction == VDirection::INOUT) m_tristate = true;
    }
    VDirection direction() const { return m_direction; }
    bool isIO() const { return m_direction != VDirection::NONE; }
    void declDirection(const VDirection& flag) { m_declDirection = flag; }
    VDirection declDirection() const { return m_declDirection; }
    void varType(AstVarType type) { m_varType = type; }
    void varType2Out() {
        m_tristate = false;
        m_direction = VDirection::OUTPUT;
    }
    void varType2In() {
        m_tristate = false;
        m_direction = VDirection::INPUT;
    }
    AstBasicDTypeKwd declKwd() const { return m_declKwd; }
    string scType() const;  // Return SysC type: bool, uint32_t, uint64_t, sc_bv
    // Return C /*public*/ type for argument: bool, uint32_t, uint64_t, etc.
    string cPubArgType(bool named, bool forReturn) const;
    string dpiArgType(bool named, bool forReturn) const;  // Return DPI-C type for argument
    string dpiTmpVarType(const string& varName) const;
    // Return Verilator internal type for argument: CData, SData, IData, WData
    string vlArgType(bool named, bool forReturn, bool forFunc, const string& namespc = "") const;
    string vlEnumType() const;  // Return VerilatorVarType: VLVT_UINT32, etc
    string vlEnumDir() const;  // Return VerilatorVarDir: VLVD_INOUT, etc
    string vlPropDecl(const string& propName) const;  // Return VerilatorVarProps declaration
    void combineType(AstVarType type);
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    // op1 = Range of variable
    AstNodeDType* childDTypep() const { return VN_CAST(op1p(), NodeDType); }
    AstNodeDType* dtypeSkipRefp() const { return subDTypep()->skipRefp(); }
    // (Slow) recurse down to find basic data type (Note don't need virtual -
    // AstVar isn't a NodeDType)
    AstBasicDType* basicp() const { return subDTypep()->basicp(); }
    // op3 = Initial value that never changes (static const)
    AstNode* valuep() const { return op3p(); }
    // It's valuep(), not constp(), as may be more complicated than an AstConst
    void valuep(AstNode* nodep) { setOp3p(nodep); }
    void addAttrsp(AstNode* nodep) { addNOp4p(nodep); }
    AstNode* attrsp() const { return op4p(); }  // op4 = Attributes during early parse
    void childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    virtual AstNodeDType* subDTypep() const { return dtypep() ? dtypep() : childDTypep(); }
    void ansi(bool flag) { m_ansi = flag; }
    void declTyped(bool flag) { m_declTyped = flag; }
    void attrClockEn(bool flag) { m_attrClockEn = flag; }
    void attrClocker(VVarAttrClocker flag) { m_attrClocker = flag; }
    void attrFileDescr(bool flag) { m_fileDescr = flag; }
    void attrScClocked(bool flag) { m_scClocked = flag; }
    void attrScBv(bool flag) { m_attrScBv = flag; }
    void attrIsolateAssign(bool flag) { m_attrIsolateAssign = flag; }
    void attrSFormat(bool flag) { m_attrSFormat = flag; }
    void attrSplitVar(bool flag) { m_attrSplitVar = flag; }
    void usedClock(bool flag) { m_usedClock = flag; }
    void usedParam(bool flag) { m_usedParam = flag; }
    void usedLoopIdx(bool flag) { m_usedLoopIdx = flag; }
    void sigPublic(bool flag) { m_sigPublic = flag; }
    void sigModPublic(bool flag) { m_sigModPublic = flag; }
    void sigUserRdPublic(bool flag) {
        m_sigUserRdPublic = flag;
        if (flag) sigPublic(true);
    }
    void sigUserRWPublic(bool flag) {
        m_sigUserRWPublic = flag;
        if (flag) sigUserRdPublic(true);
    }
    void sc(bool flag) { m_sc = flag; }
    void scSensitive(bool flag) { m_scSensitive = flag; }
    void primaryIO(bool flag) { m_primaryIO = flag; }
    void isRand(bool flag) { m_isRand = flag; }
    void isConst(bool flag) { m_isConst = flag; }
    void isStatic(bool flag) { m_isStatic = flag; }
    void isIfaceParent(bool flag) { m_isIfaceParent = flag; }
    void funcLocal(bool flag) { m_funcLocal = flag; }
    void funcReturn(bool flag) { m_funcReturn = flag; }
    void isDpiOpenArray(bool flag) { m_isDpiOpenArray = flag; }
    bool isDpiOpenArray() const { return m_isDpiOpenArray; }
    bool isHideLocal() const { return m_isHideLocal; }
    void isHideLocal(bool flag) { m_isHideLocal = flag; }
    bool isHideProtected() const { return m_isHideProtected; }
    void isHideProtected(bool flag) { m_isHideProtected = flag; }
    void noReset(bool flag) { m_noReset = flag; }
    bool noReset() const { return m_noReset; }
    void noSubst(bool flag) { m_noSubst = flag; }
    bool noSubst() const { return m_noSubst; }
    void overriddenParam(bool flag) { m_overridenParam = flag; }
    bool overriddenParam() const { return m_overridenParam; }
    void trace(bool flag) { m_trace = flag; }
    void isLatched(bool flag) { m_isLatched = flag; }
    // METHODS
    virtual void name(const string& name) override { m_name = name; }
    virtual void tag(const string& text) override { m_tag = text; }
    virtual string tag() const override { return m_tag; }
    bool isAnsi() const { return m_ansi; }
    bool isDeclTyped() const { return m_declTyped; }
    bool isInoutish() const { return m_direction.isInoutish(); }
    bool isNonOutput() const { return m_direction.isNonOutput(); }
    bool isReadOnly() const { return m_direction.isReadOnly(); }
    bool isWritable() const { return m_direction.isWritable(); }
    bool isTristate() const { return m_tristate; }
    bool isPrimaryIO() const { return m_primaryIO; }
    bool isPrimaryInish() const { return isPrimaryIO() && isNonOutput(); }
    bool isIfaceRef() const { return (varType() == AstVarType::IFACEREF); }
    bool isIfaceParent() const { return m_isIfaceParent; }
    bool isSignal() const { return varType().isSignal(); }
    bool isTemp() const { return varType().isTemp(); }
    bool isToggleCoverable() const {
        return ((isIO() || isSignal())
                && (isIO() || isBitLogic())
                // Wrapper would otherwise duplicate wrapped module's coverage
                && !isSc() && !isPrimaryIO() && !isConst() && !isDouble() && !isString());
    }
    bool isClassMember() const { return varType() == AstVarType::MEMBER; }
    bool isStatementTemp() const { return (varType() == AstVarType::STMTTEMP); }
    bool isMovableToBlock() const { return (varType() == AstVarType::BLOCKTEMP || isFuncLocal()); }
    bool isXTemp() const { return (varType() == AstVarType::XTEMP); }
    bool isParam() const {
        return (varType() == AstVarType::LPARAM || varType() == AstVarType::GPARAM);
    }
    bool isGParam() const { return (varType() == AstVarType::GPARAM); }
    bool isGenVar() const { return (varType() == AstVarType::GENVAR); }
    bool isBitLogic() const {
        AstBasicDType* bdtypep = basicp();
        return bdtypep && bdtypep->isBitLogic();
    }
    bool isUsedClock() const { return m_usedClock; }
    bool isUsedParam() const { return m_usedParam; }
    bool isUsedLoopIdx() const { return m_usedLoopIdx; }
    bool isSc() const { return m_sc; }
    bool isScQuad() const;
    bool isScBv() const;
    bool isScUint() const;
    bool isScBigUint() const;
    bool isScSensitive() const { return m_scSensitive; }
    bool isSigPublic() const;
    bool isSigModPublic() const { return m_sigModPublic; }
    bool isSigUserRdPublic() const { return m_sigUserRdPublic; }
    bool isSigUserRWPublic() const { return m_sigUserRWPublic; }
    bool isTrace() const { return m_trace; }
    bool isRand() const { return m_isRand; }
    bool isConst() const { return m_isConst; }
    bool isStatic() const { return m_isStatic; }
    bool isLatched() const { return m_isLatched; }
    bool isFuncLocal() const { return m_funcLocal; }
    bool isFuncReturn() const { return m_funcReturn; }
    bool isPullup() const { return m_isPullup; }
    bool isPulldown() const { return m_isPulldown; }
    bool attrClockEn() const { return m_attrClockEn; }
    bool attrScBv() const { return m_attrScBv; }
    bool attrFileDescr() const { return m_fileDescr; }
    bool attrScClocked() const { return m_scClocked; }
    bool attrSFormat() const { return m_attrSFormat; }
    bool attrSplitVar() const { return m_attrSplitVar; }
    bool attrIsolateAssign() const { return m_attrIsolateAssign; }
    VVarAttrClocker attrClocker() const { return m_attrClocker; }
    virtual string verilogKwd() const override;
    void lifetime(const VLifetime& flag) { m_lifetime = flag; }
    VLifetime lifetime() const { return m_lifetime; }
    void propagateAttrFrom(AstVar* fromp) {
        // This is getting connected to fromp; keep attributes
        // Note the method below too
        if (fromp->attrClockEn()) attrClockEn(true);
        if (fromp->attrFileDescr()) attrFileDescr(true);
        if (fromp->attrIsolateAssign()) attrIsolateAssign(true);
    }
    bool gateMultiInputOptimizable() const {
        // Ok to gate optimize; must return false if propagateAttrFrom would do anything
        return (!attrClockEn() && !isUsedClock());
    }
    void combineType(AstVar* typevarp) {
        // This is same as typevarp (for combining input & reg decls)
        // "this" is the input var. typevarp is the reg var.
        propagateAttrFrom(typevarp);
        combineType(typevarp->varType());
        if (typevarp->isSigPublic()) sigPublic(true);
        if (typevarp->isSigModPublic()) sigModPublic(true);
        if (typevarp->isSigUserRdPublic()) sigUserRdPublic(true);
        if (typevarp->isSigUserRWPublic()) sigUserRWPublic(true);
        if (typevarp->attrScClocked()) attrScClocked(true);
    }
    void inlineAttrReset(const string& name) {
        if (direction() == VDirection::INOUT && varType() == AstVarType::WIRE) {
            m_varType = AstVarType::TRIWIRE;
        }
        m_direction = VDirection::NONE;
        m_name = name;
    }
    static AstVar* scVarRecurse(AstNode* nodep);
    void addProducingMTaskId(int id) { m_mtaskIds.insert(id); }
    void addConsumingMTaskId(int id) { m_mtaskIds.insert(id); }
    const MTaskIdSet& mtaskIds() const { return m_mtaskIds; }
    string mtasksString() const;
};

class AstDefParam final : public AstNode {
    // A defparam assignment
    // Parents: MODULE
    // Children: math
private:
    string m_name;  // Name of variable getting set
    string m_path;  // Dotted cellname to set parameter of
public:
    AstDefParam(FileLine* fl, const string& path, const string& name, AstNode* rhsp)
        : ASTGEN_SUPER(fl) {
        setOp1p(rhsp);
        m_name = name;
        m_path = path;
    }
    virtual string name() const override { return m_name; }  // * = Scope name
    ASTNODE_NODE_FUNCS(DefParam)
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode*) const override { return true; }
    AstNode* rhsp() const { return op1p(); }  // op1 = Assign from
    string path() const { return m_path; }
};

class AstImplicit final : public AstNode {
    // Create implicit wires and do nothing else, for gates that are ignored
    // Parents: MODULE
public:
    AstImplicit(FileLine* fl, AstNode* exprsp)
        : ASTGEN_SUPER(fl) {
        addNOp1p(exprsp);
    }
    ASTNODE_NODE_FUNCS(Implicit)
    AstNode* exprsp() const { return op1p(); }  // op1 = Assign from
};

class AstScope final : public AstNode {
    // A particular usage of a cell
    // Parents: MODULE
    // Children: NODEBLOCK
private:
    // An AstScope->name() is special: . indicates an uninlined scope, __DOT__ an inlined scope
    string m_name;  // Name
    AstScope* m_aboveScopep;  // Scope above this one in the hierarchy (nullptr if top)
    AstCell* m_aboveCellp;  // Cell above this in the hierarchy (nullptr if top)
    AstNodeModule* m_modp;  // Module scope corresponds to
public:
    AstScope(FileLine* fl, AstNodeModule* modp, const string& name, AstScope* aboveScopep,
             AstCell* aboveCellp)
        : ASTGEN_SUPER(fl)
        , m_name{name}
        , m_aboveScopep{aboveScopep}
        , m_aboveCellp{aboveCellp}
        , m_modp{modp} {}
    ASTNODE_NODE_FUNCS(Scope)
    virtual void cloneRelink() override;
    virtual const char* broken() const override;
    virtual bool maybePointedTo() const override { return true; }
    virtual string name() const override { return m_name; }  // * = Scope name
    virtual void name(const string& name) override { m_name = name; }
    virtual void dump(std::ostream& str) const override;
    string nameDotless() const;
    string nameVlSym() const { return ((string("vlSymsp->")) + nameDotless()); }
    AstNodeModule* modp() const { return m_modp; }
    void addVarp(AstNode* nodep) { addOp1p(nodep); }
    AstNode* varsp() const { return op1p(); }  // op1 = AstVarScope's
    void addActivep(AstNode* nodep) { addOp2p(nodep); }
    AstNode* blocksp() const { return op2p(); }  // op2 = Block names
    void addFinalClkp(AstNode* nodep) { addOp3p(nodep); }
    AstNode* finalClksp() const { return op3p(); }  // op3 = Final assigns for clock correction
    AstScope* aboveScopep() const { return m_aboveScopep; }
    AstCell* aboveCellp() const { return m_aboveCellp; }
    bool isTop() const { return aboveScopep() == nullptr; }  // At top of hierarchy
};

class AstTopScope final : public AstNode {
    // In the top level netlist, a complete scope tree
    // There may be two of these, when we support "rare" and "usual" splitting
    // Parents: topMODULE
    // Children: SCOPEs
public:
    AstTopScope(FileLine* fl, AstScope* ascopep)
        : ASTGEN_SUPER(fl) {
        addNOp2p(ascopep);
    }
    ASTNODE_NODE_FUNCS(TopScope)
    AstNode* stmtsp() const { return op1p(); }
    void addStmtsp(AstNode* nodep) { addOp1p(nodep); }
    AstScope* scopep() const { return VN_CAST(op2p(), Scope); }  // op1 = AstVarScope's
};

class AstVarScope final : public AstNode {
    // A particular scoped usage of a variable
    // That is, as a module is used under multiple cells, we get a different
    // varscope for each var in the module
    // Parents: MODULE
    // Children: none
private:
    AstScope* m_scopep;  // Scope variable is underneath
    AstVar* m_varp;  // [AfterLink] Pointer to variable itself
    bool m_circular : 1;  // Used in circular ordering dependency, need change detect
    bool m_trace : 1;  // Tracing is turned on for this scope
public:
    AstVarScope(FileLine* fl, AstScope* scopep, AstVar* varp)
        : ASTGEN_SUPER(fl)
        , m_scopep{scopep}
        , m_varp{varp} {
        m_circular = false;
        m_trace = true;
        dtypeFrom(varp);
    }
    ASTNODE_NODE_FUNCS(VarScope)
    virtual void cloneRelink() override {
        if (m_varp && m_varp->clonep()) {
            m_varp = m_varp->clonep();
            UASSERT(m_scopep->clonep(), "No clone cross link: " << this);
            m_scopep = m_scopep->clonep();
        }
    }
    virtual const char* broken() const override {
        BROKEN_RTN(m_varp && !m_varp->brokeExists());
        BROKEN_RTN(m_scopep && !m_scopep->brokeExists());
        return nullptr;
    }
    virtual bool maybePointedTo() const override { return true; }
    virtual string name() const override { return scopep()->name() + "->" + varp()->name(); }
    virtual void dump(std::ostream& str) const override;
    virtual bool hasDType() const override { return true; }
    AstVar* varp() const { return m_varp; }  // [After Link] Pointer to variable
    AstScope* scopep() const { return m_scopep; }  // Pointer to scope it's under
    // op1 = Calculation of value of variable, nullptr=complicated
    AstNode* valuep() const { return op1p(); }
    void valuep(AstNode* valuep) { addOp1p(valuep); }
    bool isCircular() const { return m_circular; }
    void circular(bool flag) { m_circular = flag; }
    bool isTrace() const { return m_trace; }
    void trace(bool flag) { m_trace = flag; }
};

class AstVarRef final : public AstNodeVarRef {
    // A reference to a variable (lvalue or rvalue)
public:
    AstVarRef(FileLine* fl, const string& name, const VAccess& access)
        : ASTGEN_SUPER(fl, name, nullptr, access) {}
    // This form only allowed post-link because output/wire compression may
    // lead to deletion of AstVar's
    AstVarRef(FileLine* fl, AstVar* varp, const VAccess& access)
        : ASTGEN_SUPER(fl, varp->name(), varp, access) {}
    // This form only allowed post-link (see above)
    AstVarRef(FileLine* fl, AstVarScope* varscp, const VAccess& access)
        : ASTGEN_SUPER(fl, varscp->varp()->name(), varscp->varp(), access) {
        varScopep(varscp);
    }
    ASTNODE_NODE_FUNCS(VarRef)
    virtual void dump(std::ostream& str) const override;
    virtual V3Hash sameHash() const override {
        return V3Hash(V3Hash(varp()->name()), V3Hash(hiernameToProt()));
    }
    virtual bool same(const AstNode* samep) const override {
        return same(static_cast<const AstVarRef*>(samep));
    }
    inline bool same(const AstVarRef* samep) const {
        if (varScopep()) {
            return (varScopep() == samep->varScopep() && access() == samep->access());
        } else {
            return (hiernameToProt() == samep->hiernameToProt()
                    && hiernameToUnprot() == samep->hiernameToUnprot()
                    && varp()->name() == samep->varp()->name() && access() == samep->access());
        }
    }
    inline bool sameNoLvalue(AstVarRef* samep) const {
        if (varScopep()) {
            return (varScopep() == samep->varScopep());
        } else {
            return (hiernameToProt() == samep->hiernameToProt()
                    && hiernameToUnprot() == samep->hiernameToUnprot()
                    && (!hiernameToProt().empty() || !samep->hiernameToProt().empty())
                    && varp()->name() == samep->varp()->name());
        }
    }
    virtual int instrCount() const override {
        return widthInstrs() * (access().isReadOrRW() ? instrCountLd() : 1);
    }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
};

class AstVarXRef final : public AstNodeVarRef {
    // A VarRef to something in another module before AstScope.
    // Includes pin on a cell, as part of a ASSIGN statement to connect I/Os until AstScope
private:
    string m_dotted;  // Dotted part of scope the name()'ed reference is under or ""
    string m_inlinedDots;  // Dotted hierarchy flattened out
public:
    AstVarXRef(FileLine* fl, const string& name, const string& dotted, const VAccess& access)
        : ASTGEN_SUPER(fl, name, nullptr, access)
        , m_dotted{dotted} {}
    AstVarXRef(FileLine* fl, AstVar* varp, const string& dotted, const VAccess& access)
        : ASTGEN_SUPER(fl, varp->name(), varp, access)
        , m_dotted{dotted} {
        dtypeFrom(varp);
    }
    ASTNODE_NODE_FUNCS(VarXRef)
    virtual void dump(std::ostream& str) const override;
    string dotted() const { return m_dotted; }
    void dotted(const string& dotted) { m_dotted = dotted; }
    string prettyDotted() const { return prettyName(dotted()); }
    string inlinedDots() const { return m_inlinedDots; }
    void inlinedDots(const string& flag) { m_inlinedDots = flag; }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual int instrCount() const override { return widthInstrs(); }
    virtual V3Hash sameHash() const override { return V3Hash(V3Hash(varp()), V3Hash(dotted())); }
    virtual bool same(const AstNode* samep) const override {
        const AstVarXRef* asamep = static_cast<const AstVarXRef*>(samep);
        return (hiernameToProt() == asamep->hiernameToProt()
                && hiernameToUnprot() == asamep->hiernameToUnprot() && varp() == asamep->varp()
                && name() == asamep->name() && dotted() == asamep->dotted());
    }
};

class AstPin final : public AstNode {
    // A pin on a cell
private:
    int m_pinNum;  // Pin number
    string m_name;  // Pin name, or "" for number based interconnect
    AstVar* m_modVarp = nullptr;  // Input/output this pin connects to on submodule.
    AstParamTypeDType* m_modPTypep = nullptr;  // Param type this pin connects to on submodule.
    bool m_param = false;  // Pin connects to parameter
    bool m_svImplicit = false;  // Pin is SystemVerilog .name'ed
public:
    AstPin(FileLine* fl, int pinNum, const string& name, AstNode* exprp)
        : ASTGEN_SUPER(fl)
        , m_pinNum{pinNum}
        , m_name{name} {
        setNOp1p(exprp);
    }
    AstPin(FileLine* fl, int pinNum, AstVarRef* varname, AstNode* exprp)
        : ASTGEN_SUPER(fl)
        , m_pinNum{pinNum}
        , m_name{varname->name()} {
        setNOp1p(exprp);
    }
    ASTNODE_NODE_FUNCS(Pin)
    virtual void dump(std::ostream& str) const override;
    virtual const char* broken() const override {
        BROKEN_RTN(m_modVarp && !m_modVarp->brokeExists());
        BROKEN_RTN(m_modPTypep && !m_modPTypep->brokeExists());
        return nullptr;
    }
    virtual string name() const override { return m_name; }  // * = Pin name, ""=go by number
    virtual void name(const string& name) override { m_name = name; }
    virtual string prettyOperatorName() const override {
        return modVarp()
                   ? ((modVarp()->direction().isAny() ? modVarp()->direction().prettyName() + " "
                                                      : "")
                      + "port connection " + modVarp()->prettyNameQ())
                   : "port connection";
    }
    bool dotStar() const { return name() == ".*"; }  // Fake name for .* connections until linked
    int pinNum() const { return m_pinNum; }
    void exprp(AstNode* nodep) { addOp1p(nodep); }
    // op1 = Expression connected to pin, nullptr if unconnected
    AstNode* exprp() const { return op1p(); }
    AstVar* modVarp() const { return m_modVarp; }  // [After Link] Pointer to variable
    void modVarp(AstVar* nodep) { m_modVarp = nodep; }
    // [After Link] Pointer to variable
    AstParamTypeDType* modPTypep() const { return m_modPTypep; }
    void modPTypep(AstParamTypeDType* nodep) { m_modPTypep = nodep; }
    bool param() const { return m_param; }
    void param(bool flag) { m_param = flag; }
    bool svImplicit() const { return m_svImplicit; }
    void svImplicit(bool flag) { m_svImplicit = flag; }
};

class AstArg final : public AstNode {
    // An argument to a function/task
private:
    string m_name;  // Pin name, or "" for number based interconnect
public:
    AstArg(FileLine* fl, const string& name, AstNode* exprp)
        : ASTGEN_SUPER(fl)
        , m_name{name} {
        setNOp1p(exprp);
    }
    ASTNODE_NODE_FUNCS(Arg)
    virtual string name() const override { return m_name; }  // * = Pin name, ""=go by number
    virtual void name(const string& name) override { m_name = name; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    void exprp(AstNode* nodep) { addOp1p(nodep); }
    // op1 = Expression connected to pin, nullptr if unconnected
    AstNode* exprp() const { return op1p(); }
    bool emptyConnectNoNext() const { return !exprp() && name() == "" && !nextp(); }
};

class AstModule final : public AstNodeModule {
    // A module declaration
private:
    bool m_isProgram;  // Module represents a program
public:
    AstModule(FileLine* fl, const string& name, bool program = false)
        : ASTGEN_SUPER(fl, name)
        , m_isProgram{program} {}
    ASTNODE_NODE_FUNCS(Module)
    virtual string verilogKwd() const override { return m_isProgram ? "program" : "module"; }
    virtual bool timescaleMatters() const override { return true; }
};

class AstNotFoundModule final : public AstNodeModule {
    // A missing module declaration
public:
    AstNotFoundModule(FileLine* fl, const string& name)
        : ASTGEN_SUPER(fl, name) {}
    ASTNODE_NODE_FUNCS(NotFoundModule)
    virtual string verilogKwd() const override { return "/*not-found-*/ module"; }
    virtual bool timescaleMatters() const override { return false; }
};

class AstPackage final : public AstNodeModule {
    // A package declaration
public:
    AstPackage(FileLine* fl, const string& name)
        : ASTGEN_SUPER(fl, name) {}
    ASTNODE_NODE_FUNCS(Package)
    virtual string verilogKwd() const override { return "package"; }
    virtual bool timescaleMatters() const override { return !isDollarUnit(); }
    static string dollarUnitName() { return AstNode::encodeName("$unit"); }
    bool isDollarUnit() const { return name() == dollarUnitName(); }
};

class AstPrimitive final : public AstNodeModule {
    // A primitive declaration
public:
    AstPrimitive(FileLine* fl, const string& name)
        : ASTGEN_SUPER(fl, name) {}
    ASTNODE_NODE_FUNCS(Primitive)
    virtual string verilogKwd() const override { return "primitive"; }
    virtual bool timescaleMatters() const override { return false; }
};

class AstPackageExportStarStar final : public AstNode {
    // A package export *::* declaration
public:
    // cppcheck-suppress noExplicitConstructor
    AstPackageExportStarStar(FileLine* fl)
        : ASTGEN_SUPER(fl) {}
    ASTNODE_NODE_FUNCS(PackageExportStarStar)
};

class AstPackageExport final : public AstNode {
private:
    // A package export declaration
    string m_name;
    AstPackage* m_packagep;  // Package hierarchy
public:
    AstPackageExport(FileLine* fl, AstPackage* packagep, const string& name)
        : ASTGEN_SUPER(fl)
        , m_name{name}
        , m_packagep{packagep} {}
    ASTNODE_NODE_FUNCS(PackageExport)
    virtual const char* broken() const override {
        BROKEN_RTN(!m_packagep || !m_packagep->brokeExists());
        return nullptr;
    }
    virtual void cloneRelink() override {
        if (m_packagep && m_packagep->clonep()) m_packagep = m_packagep->clonep();
    }
    virtual void dump(std::ostream& str) const override;
    virtual string name() const override { return m_name; }
    AstPackage* packagep() const { return m_packagep; }
    void packagep(AstPackage* nodep) { m_packagep = nodep; }
};

class AstPackageImport final : public AstNode {
private:
    // A package import declaration
    string m_name;
    AstPackage* m_packagep;  // Package hierarchy
public:
    AstPackageImport(FileLine* fl, AstPackage* packagep, const string& name)
        : ASTGEN_SUPER(fl)
        , m_name{name}
        , m_packagep{packagep} {}
    ASTNODE_NODE_FUNCS(PackageImport)
    virtual const char* broken() const override {
        BROKEN_RTN(!m_packagep || !m_packagep->brokeExists());
        return nullptr;
    }
    virtual void cloneRelink() override {
        if (m_packagep && m_packagep->clonep()) m_packagep = m_packagep->clonep();
    }
    virtual void dump(std::ostream& str) const override;
    virtual string name() const override { return m_name; }
    AstPackage* packagep() const { return m_packagep; }
    void packagep(AstPackage* nodep) { m_packagep = nodep; }
};

class AstIface final : public AstNodeModule {
    // A module declaration
public:
    AstIface(FileLine* fl, const string& name)
        : ASTGEN_SUPER(fl, name) {}
    ASTNODE_NODE_FUNCS(Iface)
    // Interfaces have `timescale applicability but lots of code seems to
    // get false warnings if we enable this
    virtual bool timescaleMatters() const override { return false; }
};

class AstMemberSel final : public AstNodeMath {
    // Parents: math|stmt
    // Children: varref|arraysel, math
private:
    // Don't need the class we are extracting from, as the "fromp()"'s datatype can get us to it
    string m_name;
    AstVar* m_varp = nullptr;  // Post link, variable within class that is target of selection
public:
    AstMemberSel(FileLine* fl, AstNode* fromp, VFlagChildDType, const string& name)
        : ASTGEN_SUPER(fl)
        , m_name{name} {
        setOp1p(fromp);
        dtypep(nullptr);  // V3Width will resolve
    }
    AstMemberSel(FileLine* fl, AstNode* fromp, AstNodeDType* dtp)
        : ASTGEN_SUPER(fl)
        , m_name{dtp->name()} {
        setOp1p(fromp);
        dtypep(dtp);
    }
    ASTNODE_NODE_FUNCS(MemberSel)
    virtual void cloneRelink() override {
        if (m_varp && m_varp->clonep()) m_varp = m_varp->clonep();
    }
    virtual const char* broken() const override {
        BROKEN_RTN(m_varp && !m_varp->brokeExists());
        return nullptr;
    }
    virtual void dump(std::ostream& str) const override;
    virtual string name() const override { return m_name; }
    virtual V3Hash sameHash() const override { return V3Hash(m_name); }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return false; }
    virtual bool same(const AstNode* samep) const override {
        return true;
    }  // dtype comparison does it
    virtual int instrCount() const override { return widthInstrs(); }
    AstNode* fromp() const {
        return op1p();
    }  // op1 = Extracting what (nullptr=TBD during parsing)
    void fromp(AstNode* nodep) { setOp1p(nodep); }
    AstVar* varp() const { return m_varp; }
    void varp(AstVar* nodep) { m_varp = nodep; }
};

class AstModportFTaskRef final : public AstNode {
    // An import/export referenced under a modport
    // The storage for the function itself is inside the
    // interface/instantiator, thus this is a reference
    // PARENT: AstModport
private:
    string m_name;  // Name of the variable referenced
    bool m_export;  // Type of the function (import/export)
    AstNodeFTask* m_ftaskp = nullptr;  // Link to the function
public:
    AstModportFTaskRef(FileLine* fl, const string& name, bool isExport)
        : ASTGEN_SUPER(fl)
        , m_name{name}
        , m_export{isExport} {}
    ASTNODE_NODE_FUNCS(ModportFTaskRef)
    virtual const char* broken() const override {
        BROKEN_RTN(m_ftaskp && !m_ftaskp->brokeExists());
        return nullptr;
    }
    virtual void dump(std::ostream& str) const override;
    virtual string name() const override { return m_name; }
    virtual void cloneRelink() override {
        if (m_ftaskp && m_ftaskp->clonep()) m_ftaskp = m_ftaskp->clonep();
    }
    bool isImport() const { return !m_export; }
    bool isExport() const { return m_export; }
    AstNodeFTask* ftaskp() const { return m_ftaskp; }  // [After Link] Pointer to variable
    void ftaskp(AstNodeFTask* ftaskp) { m_ftaskp = ftaskp; }
};

class AstModportVarRef final : public AstNode {
    // A input/output/etc variable referenced under a modport
    // The storage for the variable itself is inside the interface, thus this is a reference
    // PARENT: AstModport
private:
    string m_name;  // Name of the variable referenced
    VDirection m_direction;  // Direction of the variable (in/out)
    AstVar* m_varp = nullptr;  // Link to the actual Var
public:
    AstModportVarRef(FileLine* fl, const string& name, VDirection::en direction)
        : ASTGEN_SUPER(fl)
        , m_name{name}
        , m_direction{direction} {}
    ASTNODE_NODE_FUNCS(ModportVarRef)
    virtual const char* broken() const override {
        BROKEN_RTN(m_varp && !m_varp->brokeExists());
        return nullptr;
    }
    virtual void dump(std::ostream& str) const override;
    virtual void cloneRelink() override {
        if (m_varp && m_varp->clonep()) m_varp = m_varp->clonep();
    }
    virtual string name() const override { return m_name; }
    void direction(const VDirection& flag) { m_direction = flag; }
    VDirection direction() const { return m_direction; }
    AstVar* varp() const { return m_varp; }  // [After Link] Pointer to variable
    void varp(AstVar* varp) { m_varp = varp; }
};

class AstModport final : public AstNode {
    // A modport in an interface
private:
    string m_name;  // Name of the modport
public:
    AstModport(FileLine* fl, const string& name, AstNode* varsp)
        : ASTGEN_SUPER(fl)
        , m_name{name} {
        addNOp1p(varsp);
    }
    virtual string name() const override { return m_name; }
    virtual bool maybePointedTo() const override { return true; }
    ASTNODE_NODE_FUNCS(Modport)
    AstNode* varsp() const { return op1p(); }  // op1 = List of Vars
};

class AstIntfRef final : public AstNode {
    // An interface reference
private:
    string m_name;  // Name of the reference
public:
    AstIntfRef(FileLine* fl, const string& name)
        : ASTGEN_SUPER(fl)
        , m_name{name} {}
    virtual string name() const override { return m_name; }
    ASTNODE_NODE_FUNCS(IntfRef)
};

class AstCell final : public AstNode {
    // A instantiation cell or interface call (don't know which until link)
private:
    FileLine* m_modNameFileline;  // Where module the cell instances token was
    string m_name;  // Cell name
    string m_origName;  // Original name before dot addition
    string m_modName;  // Module the cell instances
    AstNodeModule* m_modp = nullptr;  // [AfterLink] Pointer to module instanced
    bool m_hasIfaceVar : 1;  // True if a Var has been created for this cell
    bool m_recursive : 1;  // Self-recursive module
    bool m_trace : 1;  // Trace this cell
public:
    AstCell(FileLine* fl, FileLine* mfl, const string& instName, const string& modName,
            AstPin* pinsp, AstPin* paramsp, AstRange* rangep)
        : ASTGEN_SUPER(fl)
        , m_modNameFileline{mfl}
        , m_name{instName}
        , m_origName{instName}
        , m_modName{modName}
        , m_hasIfaceVar{false}
        , m_recursive{false}
        , m_trace{true} {
        addNOp1p(pinsp);
        addNOp2p(paramsp);
        setNOp3p(rangep);
    }
    ASTNODE_NODE_FUNCS(Cell)
    // No cloneRelink, we presume cloneee's want the same module linkages
    virtual void dump(std::ostream& str) const override;
    virtual const char* broken() const override {
        BROKEN_RTN(m_modp && !m_modp->brokeExists());
        return nullptr;
    }
    virtual bool maybePointedTo() const override { return true; }
    // ACCESSORS
    virtual string name() const override { return m_name; }  // * = Cell name
    virtual void name(const string& name) override { m_name = name; }
    virtual string origName() const override { return m_origName; }  // * = Original name
    void origName(const string& name) { m_origName = name; }
    string modName() const { return m_modName; }  // * = Instance name
    void modName(const string& name) { m_modName = name; }
    FileLine* modNameFileline() const { return m_modNameFileline; }
    AstPin* pinsp() const { return VN_CAST(op1p(), Pin); }  // op1 = List of cell ports
    // op2 = List of parameter #(##) values
    AstPin* paramsp() const { return VN_CAST(op2p(), Pin); }
    // op3 = Range of arrayed instants (nullptr=not ranged)
    AstRange* rangep() const { return VN_CAST(op3p(), Range); }
    // op4 = List of interface references
    AstIntfRef* intfRefp() const { return VN_CAST(op4p(), IntfRef); }
    AstNodeModule* modp() const { return m_modp; }  // [AfterLink] = Pointer to module instantiated
    void addPinsp(AstPin* nodep) { addOp1p(nodep); }
    void addParamsp(AstPin* nodep) { addOp2p(nodep); }
    void addIntfRefp(AstIntfRef* nodep) { addOp4p(nodep); }
    void modp(AstNodeModule* nodep) { m_modp = nodep; }
    bool hasIfaceVar() const { return m_hasIfaceVar; }
    void hasIfaceVar(bool flag) { m_hasIfaceVar = flag; }
    void trace(bool flag) { m_trace = flag; }
    bool isTrace() const { return m_trace; }
    void recursive(bool flag) { m_recursive = flag; }
    bool recursive() const { return m_recursive; }
};

class AstCellInline final : public AstNode {
    // A instantiation cell that was removed by inlining
    // For communication between V3Inline and V3LinkDot,
    // except for VPI runs where it exists until the end.
    // It is augmented with the scope in V3Scope for VPI.
    // Children: When 2 levels inlined, other CellInline under this
private:
    string m_name;  // Cell name, possibly {a}__DOT__{b}...
    string m_origModName;  // Original name of the module, ignoring name() changes, for dot lookup
    AstScope* m_scopep = nullptr;  // The scope that the cell is inlined into
    VTimescale m_timeunit;  // Parent module time unit
public:
    AstCellInline(FileLine* fl, const string& name, const string& origModName,
                  const VTimescale& timeunit)
        : ASTGEN_SUPER(fl)
        , m_name{name}
        , m_origModName{origModName}
        , m_timeunit{timeunit} {}
    ASTNODE_NODE_FUNCS(CellInline)
    virtual void dump(std::ostream& str) const override;
    virtual const char* broken() const override {
        BROKEN_RTN(m_scopep && !m_scopep->brokeExists());
        return nullptr;
    }
    // ACCESSORS
    virtual string name() const override { return m_name; }  // * = Cell name
    string origModName() const { return m_origModName; }  // * = modp()->origName() before inlining
    virtual void name(const string& name) override { m_name = name; }
    void scopep(AstScope* scp) { m_scopep = scp; }
    AstScope* scopep() const { return m_scopep; }
    void timeunit(const VTimescale& flag) { m_timeunit = flag; }
    VTimescale timeunit() const { return m_timeunit; }
};

class AstCellRef final : public AstNode {
    // As-of-yet unlinkable reference into a cell
private:
    string m_name;  // Cell name
public:
    AstCellRef(FileLine* fl, const string& name, AstNode* cellp, AstNode* exprp)
        : ASTGEN_SUPER(fl)
        , m_name{name} {
        addNOp1p(cellp);
        addNOp2p(exprp);
    }
    ASTNODE_NODE_FUNCS(CellRef)
    // ACCESSORS
    virtual string name() const override { return m_name; }  // * = Array name
    AstNode* cellp() const { return op1p(); }  // op1 = Cell
    AstNode* exprp() const { return op2p(); }  // op2 = Expression
};

class AstCellArrayRef final : public AstNode {
    // As-of-yet unlinkable reference into an array of cells
private:
    string m_name;  // Array name
public:
    AstCellArrayRef(FileLine* fl, const string& name, AstNode* selectExprp)
        : ASTGEN_SUPER(fl)
        , m_name{name} {
        addNOp1p(selectExprp);
    }
    ASTNODE_NODE_FUNCS(CellArrayRef)
    // ACCESSORS
    virtual string name() const override { return m_name; }  // * = Array name
    AstNode* selp() const { return op1p(); }  // op1 = Select expression
};

class AstUnlinkedRef final : public AstNode {
    // As-of-yet unlinkable Ref
private:
    string m_name;  // Var name
public:
    AstUnlinkedRef(FileLine* fl, AstNode* refp, const string& name, AstNode* crp)
        : ASTGEN_SUPER(fl)
        , m_name{name} {
        addNOp1p(refp);
        addNOp2p(crp);
    }
    ASTNODE_NODE_FUNCS(UnlinkedRef)
    // ACCESSORS
    virtual string name() const override { return m_name; }  // * = Var name
    AstNode* refp() const { return op1p(); }  // op1 = VarXRef or AstNodeFTaskRef
    AstNode* cellrefp() const { return op2p(); }  // op2 = CellArrayRef or CellRef
};

class AstBind final : public AstNode {
    // Parents: MODULE
    // Children: CELL
private:
    string m_name;  // Binding to name
public:
    AstBind(FileLine* fl, const string& name, AstNode* cellsp)
        : ASTGEN_SUPER(fl)
        , m_name{name} {
        UASSERT_OBJ(VN_IS(cellsp, Cell), cellsp, "Only instances allowed to be bound");
        addNOp1p(cellsp);
    }
    ASTNODE_NODE_FUNCS(Bind)
    // ACCESSORS
    virtual string name() const override { return m_name; }  // * = Bind Target name
    virtual void name(const string& name) override { m_name = name; }
    AstNode* cellsp() const { return op1p(); }  // op1 = cells
};

class AstPort final : public AstNode {
    // A port (in/out/inout) on a module
private:
    int m_pinNum;  // Pin number
    string m_name;  // Name of pin
public:
    AstPort(FileLine* fl, int pinnum, const string& name)
        : ASTGEN_SUPER(fl)
        , m_pinNum{pinnum}
        , m_name{name} {}
    ASTNODE_NODE_FUNCS(Port)
    virtual string name() const override { return m_name; }  // * = Port name
    int pinNum() const { return m_pinNum; }  // * = Pin number, for order based instantiation
    AstNode* exprp() const { return op1p(); }  // op1 = Expression connected to port
};

//######################################################################

class AstParseRef final : public AstNode {
    // A reference to a variable, function or task
    // We don't know which at parse time due to bison constraints
    // The link stages will replace this with AstVarRef, or AstTaskRef, etc.
    // Parents: math|stmt
    // Children: TEXT|DOT|SEL*|TASK|FUNC (or expression under sel)
private:
    VParseRefExp m_expect;  // Type we think it should resolve to
    string m_name;

public:
    AstParseRef(FileLine* fl, VParseRefExp expect, const string& name, AstNode* lhsp = nullptr,
                AstNodeFTaskRef* ftaskrefp = nullptr)
        : ASTGEN_SUPER(fl)
        , m_expect{expect}
        , m_name{name} {
        setNOp1p(lhsp);
        setNOp2p(ftaskrefp);
    }
    ASTNODE_NODE_FUNCS(ParseRef)
    virtual void dump(std::ostream& str) const override;
    virtual string name() const override { return m_name; }  // * = Var name
    virtual V3Hash sameHash() const override { return V3Hash(V3Hash(m_expect), V3Hash(m_name)); }
    virtual bool same(const AstNode* samep) const override {
        const AstParseRef* asamep = static_cast<const AstParseRef*>(samep);
        return (expect() == asamep->expect() && m_name == asamep->m_name);
    }
    virtual void name(const string& name) override { m_name = name; }
    VParseRefExp expect() const { return m_expect; }
    void expect(VParseRefExp exp) { m_expect = exp; }
    // op1 = Components
    AstNode* lhsp() const { return op1p(); }  // op1 = List of statements
    AstNode* ftaskrefp() const { return op2p(); }  // op2 = Function/task reference
    void ftaskrefp(AstNodeFTaskRef* nodep) { setNOp2p(nodep); }  // op2 = Function/task reference
};

class AstClassOrPackageRef final : public AstNode {
private:
    string m_name;
    // Node not NodeModule to appease some early parser usage
    AstNode* m_classOrPackageNodep;  // Package hierarchy
public:
    AstClassOrPackageRef(FileLine* fl, const string& name, AstNode* classOrPackageNodep,
                         AstNode* paramsp)
        : ASTGEN_SUPER(fl)
        , m_name{name}
        , m_classOrPackageNodep{classOrPackageNodep} {
        addNOp4p(paramsp);
    }
    ASTNODE_NODE_FUNCS(ClassOrPackageRef)
    // METHODS
    virtual const char* broken() const override {
        BROKEN_RTN(m_classOrPackageNodep && !m_classOrPackageNodep->brokeExists());
        return nullptr;
    }
    virtual void cloneRelink() override {
        if (m_classOrPackageNodep && m_classOrPackageNodep->clonep()) {
            m_classOrPackageNodep = m_classOrPackageNodep->clonep();
        }
    }
    virtual bool same(const AstNode* samep) const override {
        return (m_classOrPackageNodep
                == static_cast<const AstClassOrPackageRef*>(samep)->m_classOrPackageNodep);
    }
    virtual V3Hash sameHash() const override { return V3Hash(m_classOrPackageNodep); }
    virtual void dump(std::ostream& str = std::cout) const override;
    virtual string name() const override { return m_name; }  // * = Var name
    AstNode* classOrPackageNodep() const { return m_classOrPackageNodep; }
    void classOrPackageNodep(AstNode* nodep) { m_classOrPackageNodep = nodep; }
    AstNodeModule* classOrPackagep() const { return VN_CAST(m_classOrPackageNodep, NodeModule); }
    AstPackage* packagep() const { return VN_CAST(classOrPackageNodep(), Package); }
    void classOrPackagep(AstNodeModule* nodep) { m_classOrPackageNodep = nodep; }
    AstPin* paramsp() const { return VN_CAST(op4p(), Pin); }
};

class AstDot final : public AstNode {
    // A dot separating paths in an AstVarXRef, AstFuncRef or AstTaskRef
    // These are eliminated in the link stage
    bool m_colon;  // Is a "::" instead of a "." (lhs must be package/class)
public:
    AstDot(FileLine* fl, bool colon, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl)
        , m_colon{colon} {
        setOp1p(lhsp);
        setOp2p(rhsp);
    }
    ASTNODE_NODE_FUNCS(Dot)
    // For parser, make only if non-null package
    static AstNode* newIfPkg(FileLine* fl, AstNode* packageOrClassp, AstNode* rhsp) {
        if (!packageOrClassp) return rhsp;
        return new AstDot(fl, true, packageOrClassp, rhsp);
    }
    virtual void dump(std::ostream& str) const override;
    AstNode* lhsp() const { return op1p(); }
    AstNode* rhsp() const { return op2p(); }
    bool colon() const { return m_colon; }
};

class AstUnbounded final : public AstNodeMath {
    // A $ in the parser, used for unbounded and queues
    // Due to where is used, treated as Signed32
public:
    explicit AstUnbounded(FileLine* fl)
        : ASTGEN_SUPER(fl) {
        dtypeSetSigned32();
    }
    ASTNODE_NODE_FUNCS(Unbounded)
    virtual string emitVerilog() override { return "$"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
};

//######################################################################

class AstTask final : public AstNodeFTask {
    // A task inside a module
public:
    AstTask(FileLine* fl, const string& name, AstNode* stmtp)
        : ASTGEN_SUPER(fl, name, stmtp) {}
    ASTNODE_NODE_FUNCS(Task)
};

class AstFunc final : public AstNodeFTask {
    // A function inside a module
public:
    AstFunc(FileLine* fl, const string& name, AstNode* stmtp, AstNode* fvarsp)
        : ASTGEN_SUPER(fl, name, stmtp) {
        addNOp1p(fvarsp);
    }
    ASTNODE_NODE_FUNCS(Func)
    virtual bool hasDType() const override { return true; }
};

class AstTaskRef final : public AstNodeFTaskRef {
    // A reference to a task
public:
    AstTaskRef(FileLine* fl, AstParseRef* namep, AstNode* pinsp)
        : ASTGEN_SUPER(fl, true, namep, pinsp) {
        statement(true);
    }
    AstTaskRef(FileLine* fl, const string& name, AstNode* pinsp)
        : ASTGEN_SUPER(fl, true, name, pinsp) {}
    ASTNODE_NODE_FUNCS(TaskRef)
};

class AstFuncRef final : public AstNodeFTaskRef {
    // A reference to a function
public:
    AstFuncRef(FileLine* fl, AstParseRef* namep, AstNode* pinsp)
        : ASTGEN_SUPER(fl, false, namep, pinsp) {}
    AstFuncRef(FileLine* fl, const string& name, AstNode* pinsp)
        : ASTGEN_SUPER(fl, false, name, pinsp) {}
    ASTNODE_NODE_FUNCS(FuncRef)
    virtual bool hasDType() const override { return true; }
};

class AstDpiExport final : public AstNode {
    // We could put an AstNodeFTaskRef instead of the verilog function name,
    // however we're not *calling* it, so that seems somehow wrong.
    // (Probably AstNodeFTaskRef should be renamed AstNodeFTaskCall and have-a AstNodeFTaskRef)
private:
    string m_name;  // Name of function
    string m_cname;  // Name of function on c side
public:
    AstDpiExport(FileLine* fl, const string& vname, const string& cname)
        : ASTGEN_SUPER(fl)
        , m_name{vname}
        , m_cname{cname} {}
    ASTNODE_NODE_FUNCS(DpiExport)
    virtual string name() const override { return m_name; }
    virtual void name(const string& name) override { m_name = name; }
    string cname() const { return m_cname; }
    void cname(const string& cname) { m_cname = cname; }
};

class AstWithParse final : public AstNodeStmt {
    // In early parse, FUNC(index) WITH equation-using-index
    // Replaced with AstWith
    // Parents: math|stmt
    // Children: funcref, math
public:
    AstWithParse(FileLine* fl, bool stmt, AstNode* funcrefp, AstNode* exprp)
        : ASTGEN_SUPER(fl) {
        statement(stmt);
        setOp1p(funcrefp);
        addNOp2p(exprp);
    }
    ASTNODE_NODE_FUNCS(WithParse)
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    //
    AstNode* funcrefp() const { return op1p(); }
    AstNode* exprp() const { return op2p(); }
};

class AstLambdaArgRef final : public AstNodeMath {
    // Lambda argument usage
    // These are not AstVarRefs because we need to be able to delete/clone lambdas during
    // optimizations and AstVar's are painful to remove.
private:
    string m_name;  // Name of variable
    bool m_index;  // Index, not value

public:
    AstLambdaArgRef(FileLine* fl, const string& name, bool index)
        : ASTGEN_SUPER(fl)
        , m_name{name}
        , m_index(index) {}
    ASTNODE_NODE_FUNCS(LambdaArgRef)
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    virtual string emitVerilog() override { return name(); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual bool hasDType() const override { return true; }
    virtual int instrCount() const override { return widthInstrs(); }
    virtual string name() const override { return m_name; }  // * = Var name
    virtual void name(const string& name) override { m_name = name; }
    bool index() const { return m_index; }
};

class AstWith final : public AstNodeStmt {
    // Used as argument to method, then to AstCMethodHard
    // dtypep() contains the with lambda's return dtype
    // Parents: funcref (similar to AstArg)
    // Children: LambdaArgRef that declares the item variable
    // Children: LambdaArgRef that declares the item.index variable
    // Children: math (equation establishing the with)
public:
    AstWith(FileLine* fl, AstLambdaArgRef* indexArgRefp, AstLambdaArgRef* valueArgRefp,
            AstNode* exprp)
        : ASTGEN_SUPER(fl) {
        addOp1p(indexArgRefp);
        addOp2p(valueArgRefp);
        addNOp3p(exprp);
    }
    ASTNODE_NODE_FUNCS(With)
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    virtual bool hasDType() const override { return true; }
    virtual const char* broken() const override {
        BROKEN_RTN(!indexArgRefp());  // varp needed to know lambda's arg dtype
        BROKEN_RTN(!valueArgRefp());  // varp needed to know lambda's arg dtype
        return nullptr;
    }
    //
    AstLambdaArgRef* indexArgRefp() const { return VN_CAST(op1p(), LambdaArgRef); }
    AstLambdaArgRef* valueArgRefp() const { return VN_CAST(op2p(), LambdaArgRef); }
    AstNode* exprp() const { return op3p(); }
};

//######################################################################

class AstSenItem final : public AstNode {
    // Parents:  SENTREE
    // Children: (optional) VARREF
private:
    VEdgeType m_edgeType;  // Edge type
public:
    class Combo {};  // for creator type-overload selection
    class Illegal {};  // for creator type-overload selection
    class Initial {};  // for creator type-overload selection
    class Settle {};  // for creator type-overload selection
    class Never {};  // for creator type-overload selection
    AstSenItem(FileLine* fl, VEdgeType edgeType, AstNode* varrefp)
        : ASTGEN_SUPER(fl)
        , m_edgeType{edgeType} {
        setOp1p(varrefp);
    }
    AstSenItem(FileLine* fl, Combo)
        : ASTGEN_SUPER(fl)
        , m_edgeType{VEdgeType::ET_COMBO} {}
    AstSenItem(FileLine* fl, Illegal)
        : ASTGEN_SUPER(fl)
        , m_edgeType{VEdgeType::ET_ILLEGAL} {}
    AstSenItem(FileLine* fl, Initial)
        : ASTGEN_SUPER(fl)
        , m_edgeType{VEdgeType::ET_INITIAL} {}
    AstSenItem(FileLine* fl, Settle)
        : ASTGEN_SUPER(fl)
        , m_edgeType{VEdgeType::ET_SETTLE} {}
    AstSenItem(FileLine* fl, Never)
        : ASTGEN_SUPER(fl)
        , m_edgeType{VEdgeType::ET_NEVER} {}
    ASTNODE_NODE_FUNCS(SenItem)
    virtual void dump(std::ostream& str) const override;
    virtual V3Hash sameHash() const override { return V3Hash(edgeType()); }
    virtual bool same(const AstNode* samep) const override {
        return edgeType() == static_cast<const AstSenItem*>(samep)->edgeType();
    }
    VEdgeType edgeType() const { return m_edgeType; }  // * = Posedge/negedge
    void edgeType(VEdgeType type) {
        m_edgeType = type;
        editCountInc();
    }  // * = Posedge/negedge
    AstNode* sensp() const { return op1p(); }  // op1 = Signal sensitized
    AstNodeVarRef* varrefp() const {
        return VN_CAST(op1p(), NodeVarRef);
    }  // op1 = Signal sensitized
    //
    bool isClocked() const { return edgeType().clockedStmt(); }
    bool isCombo() const { return edgeType() == VEdgeType::ET_COMBO; }
    bool isInitial() const { return edgeType() == VEdgeType::ET_INITIAL; }
    bool isIllegal() const { return edgeType() == VEdgeType::ET_ILLEGAL; }
    bool isSettle() const { return edgeType() == VEdgeType::ET_SETTLE; }
    bool isNever() const { return edgeType() == VEdgeType::ET_NEVER; }
    bool hasVar() const { return !(isCombo() || isInitial() || isSettle() || isNever()); }
};

class AstSenTree final : public AstNode {
    // A list of senitems
    // Parents:  MODULE | SBLOCK
    // Children: SENITEM list
private:
    bool m_multi = false;  // Created from combo logic by ORing multiple clock domains
public:
    AstSenTree(FileLine* fl, AstSenItem* sensesp)
        : ASTGEN_SUPER(fl) {
        addNOp1p(sensesp);
    }
    ASTNODE_NODE_FUNCS(SenTree)
    virtual void dump(std::ostream& str) const override;
    virtual bool maybePointedTo() const override { return true; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    bool isMulti() const { return m_multi; }
    // op1 = Sensitivity list
    AstSenItem* sensesp() const { return VN_CAST(op1p(), SenItem); }
    void addSensesp(AstSenItem* nodep) { addOp1p(nodep); }
    void multi(bool flag) { m_multi = true; }
    // METHODS
    bool hasClocked() const;  // Includes a clocked statement
    bool hasSettle() const;  // Includes a SETTLE SenItem
    bool hasInitial() const;  // Includes a INITIAL SenItem
    bool hasCombo() const;  // Includes a COMBO SenItem
};

class AstFinal final : public AstNodeProcedure {
public:
    AstFinal(FileLine* fl, AstNode* bodysp)
        : ASTGEN_SUPER(fl, bodysp) {}
    ASTNODE_NODE_FUNCS(Final)
};

class AstInitial final : public AstNodeProcedure {
public:
    AstInitial(FileLine* fl, AstNode* bodysp)
        : ASTGEN_SUPER(fl, bodysp) {}
    ASTNODE_NODE_FUNCS(Initial)
};

class AstAlways final : public AstNodeProcedure {
    VAlwaysKwd m_keyword;

public:
    AstAlways(FileLine* fl, VAlwaysKwd keyword, AstSenTree* sensesp, AstNode* bodysp)
        : ASTGEN_SUPER(fl, bodysp)
        , m_keyword{keyword} {
        addNOp1p(sensesp);
    }
    ASTNODE_NODE_FUNCS(Always)
    //
    virtual void dump(std::ostream& str) const override;
    AstSenTree* sensesp() const { return VN_CAST(op1p(), SenTree); }  // op1 = Sensitivity list
    void sensesp(AstSenTree* nodep) { setOp1p(nodep); }
    VAlwaysKwd keyword() const { return m_keyword; }
};
class AstAlwaysPostponed final : public AstNodeProcedure {
    // Like always but postponement scheduling region

public:
    AstAlwaysPostponed(FileLine* fl, AstNode* bodysp)
        : ASTGEN_SUPER(fl, bodysp) {}
    ASTNODE_NODE_FUNCS(AlwaysPostponed)
};

class AstAlwaysPublic final : public AstNodeStmt {
    // "Fake" sensitivity created by /*verilator public_flat_rw @(edgelist)*/
    // Body statements are just AstVarRefs to the public signals
public:
    AstAlwaysPublic(FileLine* fl, AstSenTree* sensesp, AstNode* bodysp)
        : ASTGEN_SUPER(fl) {
        addNOp1p(sensesp);
        addNOp2p(bodysp);
    }
    ASTNODE_NODE_FUNCS(AlwaysPublic)
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    //
    AstSenTree* sensesp() const { return VN_CAST(op1p(), SenTree); }  // op1 = Sensitivity list
    AstNode* bodysp() const { return op2p(); }  // op2 = Statements to evaluate
    void addStmtp(AstNode* nodep) { addOp2p(nodep); }
    // Special accessors
    bool isJustOneBodyStmt() const { return bodysp() && !bodysp()->nextp(); }
};

class AstAlwaysPost final : public AstNode {
    // Like always but post assignments for memory assignment IFs
public:
    AstAlwaysPost(FileLine* fl, AstSenTree* sensesp, AstNode* bodysp)
        : ASTGEN_SUPER(fl) {
        addNOp1p(sensesp);
        addNOp2p(bodysp);
    }
    ASTNODE_NODE_FUNCS(AlwaysPost)
    //
    AstNode* bodysp() const { return op2p(); }  // op2 = Statements to evaluate
    void addBodysp(AstNode* newp) { addOp2p(newp); }
};

class AstAssign final : public AstNodeAssign {
public:
    AstAssign(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(Assign)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstAssign(this->fileline(), lhsp, rhsp);
    }
    virtual bool brokeLhsMustBeLvalue() const override { return true; }
};

class AstAssignAlias final : public AstNodeAssign {
    // Like AstAssignW, but a true bidirect interconnection alias
    // If both sides are wires, there's no LHS vs RHS,
public:
    AstAssignAlias(FileLine* fl, AstVarRef* lhsp, AstVarRef* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(AssignAlias)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        V3ERROR_NA_RETURN(nullptr);
    }
    virtual bool brokeLhsMustBeLvalue() const override { return false; }
};

class AstAssignDly final : public AstNodeAssign {
public:
    AstAssignDly(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(AssignDly)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstAssignDly(this->fileline(), lhsp, rhsp);
    }
    virtual bool isGateOptimizable() const override { return false; }
    virtual string verilogKwd() const override { return "<="; }
    virtual bool brokeLhsMustBeLvalue() const override { return true; }
};

class AstAssignW final : public AstNodeAssign {
    // Like assign, but wire/assign's in verilog, the only setting of the specified variable
public:
    AstAssignW(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(AssignW)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstAssignW(this->fileline(), lhsp, rhsp);
    }
    virtual bool brokeLhsMustBeLvalue() const override { return true; }
    AstAlways* convertToAlways() {
        AstNode* lhs1p = lhsp()->unlinkFrBack();
        AstNode* rhs1p = rhsp()->unlinkFrBack();
        AstAlways* newp = new AstAlways(fileline(), VAlwaysKwd::ALWAYS, nullptr,
                                        new AstAssign(fileline(), lhs1p, rhs1p));
        replaceWith(newp);  // User expected to then deleteTree();
        return newp;
    }
};

class AstAssignVarScope final : public AstNodeAssign {
    // Assign two VarScopes to each other
public:
    AstAssignVarScope(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeFrom(rhsp);
    }
    ASTNODE_NODE_FUNCS(AssignVarScope)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstAssignVarScope(this->fileline(), lhsp, rhsp);
    }
    virtual bool brokeLhsMustBeLvalue() const override { return false; }
};

class AstPull final : public AstNode {
private:
    bool m_direction;

public:
    AstPull(FileLine* fl, AstNode* lhsp, bool direction)
        : ASTGEN_SUPER(fl) {
        setOp1p(lhsp);
        m_direction = direction;
    }
    ASTNODE_NODE_FUNCS(Pull)
    virtual bool same(const AstNode* samep) const override {
        return direction() == static_cast<const AstPull*>(samep)->direction();
    }
    void lhsp(AstNode* np) { setOp1p(np); }
    AstNode* lhsp() const { return op1p(); }  // op1 = Assign to
    uint32_t direction() const { return (uint32_t)m_direction; }
};

class AstAssignPre final : public AstNodeAssign {
    // Like Assign, but predelayed assignment requiring special order handling
public:
    AstAssignPre(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(AssignPre)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstAssignPre(this->fileline(), lhsp, rhsp);
    }
    virtual bool brokeLhsMustBeLvalue() const override { return true; }
};

class AstAssignPost final : public AstNodeAssign {
    // Like Assign, but predelayed assignment requiring special order handling
public:
    AstAssignPost(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(AssignPost)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstAssignPost(this->fileline(), lhsp, rhsp);
    }
    virtual bool brokeLhsMustBeLvalue() const override { return true; }
};

class AstExprStmt final : public AstNodeMath {
    // Perform a statement, often assignment inside an expression/math node,
    // the parent gets passed the 'resultp()'.
    // resultp is evaluated AFTER the statement(s).
public:
    AstExprStmt(FileLine* fl, AstNode* stmtsp, AstNode* resultp)
        : ASTGEN_SUPER(fl) {
        addOp1p(stmtsp);
        setOp2p(resultp);  // Possibly in future nullptr could mean return rhsp()
        dtypeFrom(resultp);
    }
    ASTNODE_NODE_FUNCS(ExprStmt)
    // ACCESSORS
    AstNode* stmtsp() const { return op1p(); }
    void addStmtsp(AstNode* nodep) { addOp1p(nodep); }
    AstNode* resultp() const { return op2p(); }
    // METHODS
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return false; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode*) const override { return true; }
};

class AstComment final : public AstNodeStmt {
    // Some comment to put into the output stream
    // Parents:  {statement list}
    // Children: none
private:
    bool m_showAt;  // Show "at <fileline>"
    string m_name;  // Text of comment
public:
    AstComment(FileLine* fl, const string& name, bool showAt = false)
        : ASTGEN_SUPER(fl)
        , m_showAt{showAt}
        , m_name{name} {}
    ASTNODE_NODE_FUNCS(Comment)
    virtual string name() const override { return m_name; }  // * = Text
    virtual V3Hash sameHash() const override { return V3Hash(); }  // Ignore name in comments
    virtual bool same(const AstNode* samep) const override {
        return true;
    }  // Ignore name in comments
    virtual bool showAt() const { return m_showAt; }
};

class AstCond final : public AstNodeCond {
    // Conditional ?: statement
    // Parents:  MATH
    // Children: MATH
public:
    AstCond(FileLine* fl, AstNode* condp, AstNode* expr1p, AstNode* expr2p)
        : ASTGEN_SUPER(fl, condp, expr1p, expr2p) {}
    ASTNODE_NODE_FUNCS(Cond)
    virtual AstNode* cloneType(AstNode* condp, AstNode* expr1p, AstNode* expr2p) override {
        return new AstCond(this->fileline(), condp, expr1p, expr2p);
    }
};

class AstCondBound final : public AstNodeCond {
    // Conditional ?: statement, specially made for safety checking of array bounds
    // Parents:  MATH
    // Children: MATH
public:
    AstCondBound(FileLine* fl, AstNode* condp, AstNode* expr1p, AstNode* expr2p)
        : ASTGEN_SUPER(fl, condp, expr1p, expr2p) {}
    ASTNODE_NODE_FUNCS(CondBound)
    virtual AstNode* cloneType(AstNode* condp, AstNode* expr1p, AstNode* expr2p) override {
        return new AstCondBound(this->fileline(), condp, expr1p, expr2p);
    }
};

class AstCoverDecl final : public AstNodeStmt {
    // Coverage analysis point declaration
    // Parents:  {statement list}
    // Children: none
private:
    AstCoverDecl* m_dataDeclp;  // [After V3CoverageJoin] Pointer to duplicate declaration to get
                                // data from instead
    string m_page;
    string m_text;
    string m_hier;
    string m_linescov;
    int m_offset;  // Offset column numbers to uniq-ify IFs
    int m_binNum;  // Set by V3EmitCSyms to tell final V3Emit what to increment
public:
    AstCoverDecl(FileLine* fl, const string& page, const string& comment, const string& linescov,
                 int offset)
        : ASTGEN_SUPER(fl) {
        m_page = page;
        m_text = comment;
        m_linescov = linescov;
        m_offset = offset;
        m_binNum = 0;
        m_dataDeclp = nullptr;
    }
    ASTNODE_NODE_FUNCS(CoverDecl)
    virtual const char* broken() const override {
        BROKEN_RTN(m_dataDeclp && !m_dataDeclp->brokeExists());
        if (m_dataDeclp && m_dataDeclp->m_dataDeclp) {  // Avoid O(n^2) accessing
            v3fatalSrc("dataDeclp should point to real data, not be a list");
        }
        return nullptr;
    }
    virtual void cloneRelink() override {
        if (m_dataDeclp && m_dataDeclp->clonep()) m_dataDeclp = m_dataDeclp->clonep();
    }
    virtual void dump(std::ostream& str) const override;
    virtual int instrCount() const override { return 1 + 2 * instrCountLd(); }
    virtual bool maybePointedTo() const override { return true; }
    void binNum(int flag) { m_binNum = flag; }
    int binNum() const { return m_binNum; }
    int offset() const { return m_offset; }
    const string& comment() const { return m_text; }  // text to insert in code
    const string& linescov() const { return m_linescov; }
    const string& page() const { return m_page; }
    const string& hier() const { return m_hier; }
    void hier(const string& flag) { m_hier = flag; }
    void comment(const string& flag) { m_text = flag; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override {
        const AstCoverDecl* asamep = static_cast<const AstCoverDecl*>(samep);
        return (fileline() == asamep->fileline() && linescov() == asamep->linescov()
                && hier() == asamep->hier() && comment() == asamep->comment());
    }
    virtual bool isPredictOptimizable() const override { return false; }
    void dataDeclp(AstCoverDecl* nodep) { m_dataDeclp = nodep; }
    // dataDecl nullptr means "use this one", but often you want "this" to
    // indicate to get data from here
    AstCoverDecl* dataDeclNullp() const { return m_dataDeclp; }
    AstCoverDecl* dataDeclThisp() { return dataDeclNullp() ? dataDeclNullp() : this; }
};

class AstCoverInc final : public AstNodeStmt {
    // Coverage analysis point; increment coverage count
    // Parents:  {statement list}
    // Children: none
private:
    AstCoverDecl* m_declp;  // [After V3Coverage] Pointer to declaration
public:
    AstCoverInc(FileLine* fl, AstCoverDecl* declp)
        : ASTGEN_SUPER(fl)
        , m_declp{declp} {}
    ASTNODE_NODE_FUNCS(CoverInc)
    virtual const char* broken() const override {
        BROKEN_RTN(!declp()->brokeExists());
        return nullptr;
    }
    virtual void cloneRelink() override {
        if (m_declp->clonep()) m_declp = m_declp->clonep();
    }
    virtual void dump(std::ostream& str) const override;
    virtual int instrCount() const override { return 1 + 2 * instrCountLd(); }
    virtual V3Hash sameHash() const override { return V3Hash(declp()); }
    virtual bool same(const AstNode* samep) const override {
        return declp() == static_cast<const AstCoverInc*>(samep)->declp();
    }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    // but isPure()  true
    AstCoverDecl* declp() const { return m_declp; }  // Where defined
};

class AstCoverToggle final : public AstNodeStmt {
    // Toggle analysis of given signal
    // Parents:  MODULE
    // Children: AstCoverInc, orig var, change det var
public:
    AstCoverToggle(FileLine* fl, AstCoverInc* incp, AstNode* origp, AstNode* changep)
        : ASTGEN_SUPER(fl) {
        setOp1p(incp);
        setOp2p(origp);
        setOp3p(changep);
    }
    ASTNODE_NODE_FUNCS(CoverToggle)
    virtual int instrCount() const override { return 3 + instrCountBranch() + instrCountLd(); }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return true; }
    virtual bool isOutputter() const override {
        return false;  // Though the AstCoverInc under this is an outputter
    }
    // but isPure()  true
    AstCoverInc* incp() const { return VN_CAST(op1p(), CoverInc); }
    void incp(AstCoverInc* nodep) { setOp1p(nodep); }
    AstNode* origp() const { return op2p(); }
    AstNode* changep() const { return op3p(); }
};

class AstDelay final : public AstNodeStmt {
    // Delay statement
public:
    AstDelay(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl) {
        setOp1p(lhsp);
    }
    ASTNODE_NODE_FUNCS(Delay)
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    //
    AstNode* lhsp() const { return op1p(); }  // op2 = Statements to evaluate
    void lhsp(AstNode* nodep) { setOp1p(nodep); }
};

class AstGenCase final : public AstNodeCase {
    // Generate Case statement
    // Parents:  {statement list}
    // exprp Children:  MATHs
    // casesp Children: CASEITEMs
public:
    AstGenCase(FileLine* fl, AstNode* exprp, AstNode* casesp)
        : ASTGEN_SUPER(fl, exprp, casesp) {}
    ASTNODE_NODE_FUNCS(GenCase)
};

class AstCase final : public AstNodeCase {
    // Case statement
    // Parents:  {statement list}
    // exprp Children:  MATHs
    // casesp Children: CASEITEMs
private:
    VCaseType m_casex;  // 0=case, 1=casex, 2=casez
    bool m_fullPragma = false;  // Synthesis full_case
    bool m_parallelPragma = false;  // Synthesis parallel_case
    bool m_uniquePragma = false;  // unique case
    bool m_unique0Pragma = false;  // unique0 case
    bool m_priorityPragma = false;  // priority case
public:
    AstCase(FileLine* fl, VCaseType casex, AstNode* exprp, AstNode* casesp)
        : ASTGEN_SUPER(fl, exprp, casesp)
        , m_casex{casex} {}
    ASTNODE_NODE_FUNCS(Case)
    virtual string verilogKwd() const override {
        return casez() ? "casez" : casex() ? "casex" : "case";
    }
    virtual bool same(const AstNode* samep) const override {
        return m_casex == static_cast<const AstCase*>(samep)->m_casex;
    }
    bool casex() const { return m_casex == VCaseType::CT_CASEX; }
    bool casez() const { return m_casex == VCaseType::CT_CASEZ; }
    bool caseInside() const { return m_casex == VCaseType::CT_CASEINSIDE; }
    bool caseSimple() const { return m_casex == VCaseType::CT_CASE; }
    void caseInsideSet() { m_casex = VCaseType::CT_CASEINSIDE; }
    bool fullPragma() const { return m_fullPragma; }
    void fullPragma(bool flag) { m_fullPragma = flag; }
    bool parallelPragma() const { return m_parallelPragma; }
    void parallelPragma(bool flag) { m_parallelPragma = flag; }
    bool uniquePragma() const { return m_uniquePragma; }
    void uniquePragma(bool flag) { m_uniquePragma = flag; }
    bool unique0Pragma() const { return m_unique0Pragma; }
    void unique0Pragma(bool flag) { m_unique0Pragma = flag; }
    bool priorityPragma() const { return m_priorityPragma; }
    void priorityPragma(bool flag) { m_priorityPragma = flag; }
};

class AstCaseItem final : public AstNode {
    // Single item of a case statement
    // Parents:  CASE
    // condsp Children: MATH  (Null condition used for default block)
    // bodysp Children: Statements
private:
    bool m_ignoreOverlap = false;  // Default created by assertions; ignore overlaps
public:
    AstCaseItem(FileLine* fl, AstNode* condsp, AstNode* bodysp)
        : ASTGEN_SUPER(fl) {
        addNOp1p(condsp);
        addNOp2p(bodysp);
    }
    ASTNODE_NODE_FUNCS(CaseItem)
    virtual int instrCount() const override { return widthInstrs() + instrCountBranch(); }
    AstNode* condsp() const { return op1p(); }  // op1 = list of possible matching expressions
    AstNode* bodysp() const { return op2p(); }  // op2 = what to do
    void condsp(AstNode* nodep) { setOp1p(nodep); }
    void addBodysp(AstNode* newp) { addOp2p(newp); }
    bool isDefault() const { return condsp() == nullptr; }
    bool ignoreOverlap() const { return m_ignoreOverlap; }
    void ignoreOverlap(bool flag) { m_ignoreOverlap = flag; }
};

class AstSFormatF final : public AstNode {
    // Convert format to string, generally under an AstDisplay or AstSFormat
    // Also used as "real" function for /*verilator sformat*/ functions
    string m_text;
    bool m_hidden;  // Under display, etc
    bool m_hasFormat;  // Has format code
    char m_missingArgChar;  // Format code when argument without format, 'h'/'o'/'b'
    VTimescale m_timeunit;  // Parent module time unit
public:
    class NoFormat {};
    AstSFormatF(FileLine* fl, const string& text, bool hidden, AstNode* exprsp,
                char missingArgChar = 'd')
        : ASTGEN_SUPER(fl)
        , m_text{text}
        , m_hidden{hidden}
        , m_hasFormat{true}
        , m_missingArgChar{missingArgChar} {
        dtypeSetString();
        addNOp1p(exprsp);
        addNOp2p(nullptr);
    }
    AstSFormatF(FileLine* fl, NoFormat, AstNode* exprsp, char missingArgChar = 'd',
                bool hidden = true)
        : ASTGEN_SUPER(fl)
        , m_text{""}
        , m_hidden{hidden}
        , m_hasFormat{false}
        , m_missingArgChar{missingArgChar} {
        dtypeSetString();
        addNOp1p(exprsp);
        addNOp2p(nullptr);
    }
    ASTNODE_NODE_FUNCS(SFormatF)
    virtual string name() const override { return m_text; }
    virtual int instrCount() const override { return instrCountPli(); }
    virtual V3Hash sameHash() const override { return V3Hash(text()); }
    virtual bool hasDType() const override { return true; }
    virtual bool same(const AstNode* samep) const override {
        return text() == static_cast<const AstSFormatF*>(samep)->text();
    }
    virtual string verilogKwd() const override { return "$sformatf"; }
    void addExprsp(AstNode* nodep) { addOp1p(nodep); }  // op1 = Expressions to output
    AstNode* exprsp() const { return op1p(); }  // op1 = Expressions to output
    string text() const { return m_text; }  // * = Text to display
    void text(const string& text) { m_text = text; }
    AstScopeName* scopeNamep() const { return VN_CAST(op2p(), ScopeName); }
    void scopeNamep(AstNode* nodep) { setNOp2p(nodep); }
    bool formatScopeTracking() const {  // Track scopeNamep();  Ok if false positive
        return (name().find("%m") != string::npos || name().find("%M") != string::npos);
    }
    bool hidden() const { return m_hidden; }
    void hasFormat(bool flag) { m_hasFormat = flag; }
    bool hasFormat() const { return m_hasFormat; }
    char missingArgChar() const { return m_missingArgChar; }
    void timeunit(const VTimescale& flag) { m_timeunit = flag; }
    VTimescale timeunit() const { return m_timeunit; }
};

class AstDisplay final : public AstNodeStmt {
    // Parents: stmtlist
    // Children: file which must be a varref
    // Children: SFORMATF to generate print string
private:
    AstDisplayType m_displayType;

public:
    AstDisplay(FileLine* fl, AstDisplayType dispType, const string& text, AstNode* filep,
               AstNode* exprsp, char missingArgChar = 'd')
        : ASTGEN_SUPER(fl) {
        setOp1p(new AstSFormatF(fl, text, true, exprsp, missingArgChar));
        setNOp3p(filep);
        m_displayType = dispType;
    }
    AstDisplay(FileLine* fl, AstDisplayType dispType, AstNode* filep, AstNode* exprsp,
               char missingArgChar = 'd')
        : ASTGEN_SUPER(fl) {
        setOp1p(new AstSFormatF(fl, AstSFormatF::NoFormat(), exprsp, missingArgChar));
        setNOp3p(filep);
        m_displayType = dispType;
    }
    ASTNODE_NODE_FUNCS(Display)
    virtual void dump(std::ostream& str) const override;
    virtual const char* broken() const override {
        BROKEN_RTN(!fmtp());
        return nullptr;
    }
    virtual string verilogKwd() const override {
        return (filep() ? string("$f") + string(displayType().ascii())
                        : string("$") + string(displayType().ascii()));
    }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override {
        return false;
    }  // SPECIAL: $display has 'visual' ordering
    virtual bool isOutputter() const override { return true; }  // SPECIAL: $display makes output
    virtual bool isUnlikely() const override { return true; }
    virtual V3Hash sameHash() const override { return V3Hash(displayType()); }
    virtual bool same(const AstNode* samep) const override {
        return displayType() == static_cast<const AstDisplay*>(samep)->displayType();
    }
    virtual int instrCount() const override { return instrCountPli(); }
    AstDisplayType displayType() const { return m_displayType; }
    void displayType(AstDisplayType type) { m_displayType = type; }
    // * = Add a newline for $display
    bool addNewline() const { return displayType().addNewline(); }
    void fmtp(AstSFormatF* nodep) { addOp1p(nodep); }  // op1 = To-String formatter
    AstSFormatF* fmtp() const { return VN_CAST(op1p(), SFormatF); }
    AstNode* filep() const { return op3p(); }
    void filep(AstNodeVarRef* nodep) { setNOp3p(nodep); }
};

class AstDumpCtl final : public AstNodeStmt {
    // $dumpon etc
    // Parents: expr
    // Child: expr based on type of control statement
    VDumpCtlType m_ctlType;  // Type of operation
public:
    AstDumpCtl(FileLine* fl, VDumpCtlType ctlType, AstNode* exprp = nullptr)
        : ASTGEN_SUPER(fl)
        , m_ctlType{ctlType} {
        setNOp1p(exprp);
    }
    ASTNODE_NODE_FUNCS(DumpCtl)
    virtual string verilogKwd() const override { return ctlType().ascii(); }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isHeavy() const override { return true; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    virtual bool cleanOut() const { return true; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    VDumpCtlType ctlType() const { return m_ctlType; }
    AstNode* exprp() const { return op1p(); }  // op2 = Expressions to output
    void exprp(AstNode* nodep) { setOp1p(nodep); }
};

class AstElabDisplay final : public AstNode {
    // Parents: stmtlist
    // Children: SFORMATF to generate print string
private:
    AstDisplayType m_displayType;

public:
    AstElabDisplay(FileLine* fl, AstDisplayType dispType, AstNode* exprsp)
        : ASTGEN_SUPER(fl) {
        setOp1p(new AstSFormatF(fl, AstSFormatF::NoFormat(), exprsp));
        m_displayType = dispType;
    }
    ASTNODE_NODE_FUNCS(ElabDisplay)
    virtual const char* broken() const override {
        BROKEN_RTN(!fmtp());
        return nullptr;
    }
    virtual string verilogKwd() const override {
        return (string("$") + string(displayType().ascii()));
    }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override {
        return false;
    }  // SPECIAL: $display has 'visual' ordering
    virtual bool isOutputter() const override { return true; }  // SPECIAL: $display makes output
    virtual bool isUnlikely() const override { return true; }
    virtual V3Hash sameHash() const override { return V3Hash(displayType()); }
    virtual bool same(const AstNode* samep) const override {
        return displayType() == static_cast<const AstElabDisplay*>(samep)->displayType();
    }
    virtual int instrCount() const override { return instrCountPli(); }
    AstDisplayType displayType() const { return m_displayType; }
    void displayType(AstDisplayType type) { m_displayType = type; }
    void fmtp(AstSFormatF* nodep) { addOp1p(nodep); }  // op1 = To-String formatter
    AstSFormatF* fmtp() const { return VN_CAST(op1p(), SFormatF); }
};

class AstSFormat final : public AstNodeStmt {
    // Parents: statement container
    // Children: string to load
    // Children: SFORMATF to generate print string
public:
    AstSFormat(FileLine* fl, AstNode* lhsp, const string& text, AstNode* exprsp,
               char missingArgChar = 'd')
        : ASTGEN_SUPER(fl) {
        setOp1p(new AstSFormatF(fl, text, true, exprsp, missingArgChar));
        setOp3p(lhsp);
    }
    AstSFormat(FileLine* fl, AstNode* lhsp, AstNode* exprsp, char missingArgChar = 'd')
        : ASTGEN_SUPER(fl) {
        setOp1p(new AstSFormatF(fl, AstSFormatF::NoFormat(), exprsp, missingArgChar));
        setOp3p(lhsp);
    }
    ASTNODE_NODE_FUNCS(SFormat)
    virtual const char* broken() const override {
        BROKEN_RTN(!fmtp());
        return nullptr;
    }
    virtual string verilogKwd() const override { return "$sformat"; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return true; }
    virtual bool isPure() const override { return true; }
    virtual bool isOutputter() const override { return false; }
    virtual bool cleanOut() const { return false; }
    virtual int instrCount() const override { return instrCountPli(); }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    void fmtp(AstSFormatF* nodep) { addOp1p(nodep); }  // op1 = To-String formatter
    AstSFormatF* fmtp() const { return VN_CAST(op1p(), SFormatF); }
    AstNode* lhsp() const { return op3p(); }
    void lhsp(AstNode* nodep) { setOp3p(nodep); }
};

class AstSysFuncAsTask final : public AstNodeStmt {
    // Call what is normally a system function (with a return) in a non-return context
    // Parents: stmtlist
    // Children: a system function
public:
    AstSysFuncAsTask(FileLine* fl, AstNode* exprsp)
        : ASTGEN_SUPER(fl) {
        addNOp1p(exprsp);
    }
    ASTNODE_NODE_FUNCS(SysFuncAsTask)
    virtual string verilogKwd() const override { return ""; }
    virtual bool isGateOptimizable() const override { return true; }
    virtual bool isPredictOptimizable() const override { return true; }
    virtual bool isPure() const override { return true; }
    virtual bool isOutputter() const override { return false; }
    virtual int instrCount() const override { return 0; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    AstNode* lhsp() const { return op1p(); }  // op1 = Expressions to eval
    void lhsp(AstNode* nodep) { addOp1p(nodep); }  // op1 = Expressions to eval
};

class AstSysIgnore final : public AstNodeStmt {
    // Parents: stmtlist
    // Children: varrefs or exprs
public:
    AstSysIgnore(FileLine* fl, AstNode* exprsp)
        : ASTGEN_SUPER(fl) {
        addNOp1p(exprsp);
    }
    ASTNODE_NODE_FUNCS(SysIgnore)
    virtual string verilogKwd() const override { return "$ignored"; }
    virtual bool isGateOptimizable() const override { return false; }  // Though deleted before opt
    virtual bool isPredictOptimizable() const override {
        return false;
    }  // Though deleted before opt
    virtual bool isPure() const override { return false; }  // Though deleted before opt
    virtual bool isOutputter() const override { return true; }  // Though deleted before opt
    virtual int instrCount() const override { return instrCountPli(); }
    AstNode* exprsp() const { return op1p(); }  // op1 = Expressions to output
    void exprsp(AstNode* nodep) { addOp1p(nodep); }  // op1 = Expressions to output
};

class AstFClose final : public AstNodeStmt {
    // Parents: stmtlist
    // Children: file which must be a varref
public:
    AstFClose(FileLine* fl, AstNode* filep)
        : ASTGEN_SUPER(fl) {
        setNOp2p(filep);
    }
    ASTNODE_NODE_FUNCS(FClose)
    virtual string verilogKwd() const override { return "$fclose"; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    virtual bool isUnlikely() const override { return true; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    AstNode* filep() const { return op2p(); }
    void filep(AstNodeVarRef* nodep) { setNOp2p(nodep); }
};

class AstFOpen final : public AstNodeStmt {
    // Although a system function in IEEE, here a statement which sets the file pointer (MCD)
public:
    AstFOpen(FileLine* fl, AstNode* filep, AstNode* filenamep, AstNode* modep)
        : ASTGEN_SUPER(fl) {
        setOp1p(filep);
        setOp2p(filenamep);
        setOp3p(modep);
    }
    ASTNODE_NODE_FUNCS(FOpen)
    virtual string verilogKwd() const override { return "$fopen"; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isHeavy() const override { return true; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    virtual bool isUnlikely() const override { return true; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    AstNode* filep() const { return op1p(); }
    AstNode* filenamep() const { return op2p(); }
    AstNode* modep() const { return op3p(); }
};

class AstFOpenMcd final : public AstNodeStmt {
    // Although a system function in IEEE, here a statement which sets the file pointer (MCD)
public:
    AstFOpenMcd(FileLine* fl, AstNode* filep, AstNode* filenamep)
        : ASTGEN_SUPER(fl) {
        setOp1p(filep);
        setOp2p(filenamep);
    }
    ASTNODE_NODE_FUNCS(FOpenMcd)
    virtual string verilogKwd() const override { return "$fopen"; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isHeavy() const override { return true; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    virtual bool isUnlikely() const override { return true; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    AstNode* filep() const { return op1p(); }
    AstNode* filenamep() const { return op2p(); }
};

class AstFFlush final : public AstNodeStmt {
    // Parents: stmtlist
    // Children: file which must be a varref
public:
    AstFFlush(FileLine* fl, AstNode* filep)
        : ASTGEN_SUPER(fl) {
        setNOp2p(filep);
    }
    ASTNODE_NODE_FUNCS(FFlush)
    virtual string verilogKwd() const override { return "$fflush"; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    virtual bool isUnlikely() const override { return true; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    AstNode* filep() const { return op2p(); }
    void filep(AstNodeVarRef* nodep) { setNOp2p(nodep); }
};

class AstFRead final : public AstNodeMath {
    // Parents: expr
    // Children: varrefs to load
    // Children: file which must be a varref
    // Children: low index
    // Children: count
public:
    AstFRead(FileLine* fl, AstNode* memp, AstNode* filep, AstNode* startp, AstNode* countp)
        : ASTGEN_SUPER(fl) {
        setOp1p(memp);
        setOp2p(filep);
        setNOp3p(startp);
        setNOp4p(countp);
    }
    ASTNODE_NODE_FUNCS(FRead)
    virtual string verilogKwd() const override { return "$fread"; }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }  // SPECIAL: has 'visual' ordering
    virtual bool isOutputter() const override { return true; }  // SPECIAL: makes output
    virtual bool cleanOut() const override { return false; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    AstNode* memp() const { return op1p(); }
    void memp(AstNode* nodep) { setOp1p(nodep); }
    AstNode* filep() const { return op2p(); }
    void filep(AstNode* nodep) { setOp2p(nodep); }
    AstNode* startp() const { return op3p(); }
    void startp(AstNode* nodep) { setNOp3p(nodep); }
    AstNode* countp() const { return op4p(); }
    void countp(AstNode* nodep) { setNOp4p(nodep); }
};

class AstFRewind final : public AstNodeMath {
    // Parents: stmtlist
    // Children: file which must be a varref
public:
    AstFRewind(FileLine* fl, AstNode* filep)
        : ASTGEN_SUPER(fl) {
        setNOp2p(filep);
    }
    ASTNODE_NODE_FUNCS(FRewind)
    virtual string verilogKwd() const override { return "$frewind"; }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    virtual bool isUnlikely() const override { return true; }
    virtual bool cleanOut() const override { return false; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    AstNode* filep() const { return op2p(); }
    void filep(AstNodeVarRef* nodep) { setNOp2p(nodep); }
};

class AstFTell final : public AstNodeMath {
    // Parents: stmtlist
    // Children: file which must be a varref
public:
    AstFTell(FileLine* fl, AstNode* filep)
        : ASTGEN_SUPER(fl) {
        setNOp2p(filep);
    }
    ASTNODE_NODE_FUNCS(FTell)
    virtual string verilogKwd() const override { return "$ftell"; }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    virtual bool isUnlikely() const override { return true; }
    virtual bool cleanOut() const override { return false; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    AstNode* filep() const { return op2p(); }
    void filep(AstNodeVarRef* nodep) { setNOp2p(nodep); }
};

class AstFSeek final : public AstNodeMath {
    // Parents: expr
    // Children: file which must be a varref
    // Children: offset
    // Children: operation
public:
    AstFSeek(FileLine* fl, AstNode* filep, AstNode* offset, AstNode* operation)
        : ASTGEN_SUPER(fl) {
        setOp2p(filep);
        setNOp3p(offset);
        setNOp4p(operation);
    }
    ASTNODE_NODE_FUNCS(FSeek)
    virtual string verilogKwd() const override { return "$fseek"; }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }  // SPECIAL: has 'visual' ordering
    virtual bool isOutputter() const override { return true; }  // SPECIAL: makes output
    virtual bool cleanOut() const override { return false; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    AstNode* filep() const { return op2p(); }
    void filep(AstNode* nodep) { setOp2p(nodep); }
    AstNode* offset() const { return op3p(); }
    void offset(AstNode* nodep) { setNOp3p(nodep); }
    AstNode* operation() const { return op4p(); }
    void operation(AstNode* nodep) { setNOp4p(nodep); }
};

class AstFScanF final : public AstNodeMath {
    // Parents: expr
    // Children: file which must be a varref
    // Children: varrefs to load
private:
    string m_text;

public:
    AstFScanF(FileLine* fl, const string& text, AstNode* filep, AstNode* exprsp)
        : ASTGEN_SUPER(fl)
        , m_text{text} {
        addNOp1p(exprsp);
        setNOp2p(filep);
    }
    ASTNODE_NODE_FUNCS(FScanF)
    virtual string name() const override { return m_text; }
    virtual string verilogKwd() const override { return "$fscanf"; }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }  // SPECIAL: has 'visual' ordering
    virtual bool isOutputter() const override { return true; }  // SPECIAL: makes output
    virtual bool cleanOut() const override { return false; }
    virtual V3Hash sameHash() const override { return V3Hash(text()); }
    virtual bool same(const AstNode* samep) const override {
        return text() == static_cast<const AstFScanF*>(samep)->text();
    }
    AstNode* exprsp() const { return op1p(); }  // op1 = Expressions to output
    void exprsp(AstNode* nodep) { addOp1p(nodep); }  // op1 = Expressions to output
    string text() const { return m_text; }  // * = Text to display
    void text(const string& text) { m_text = text; }
    AstNode* filep() const { return op2p(); }
    void filep(AstNodeVarRef* nodep) { setNOp2p(nodep); }
};

class AstSScanF final : public AstNodeMath {
    // Parents: expr
    // Children: file which must be a varref
    // Children: varrefs to load
private:
    string m_text;

public:
    AstSScanF(FileLine* fl, const string& text, AstNode* fromp, AstNode* exprsp)
        : ASTGEN_SUPER(fl)
        , m_text{text} {
        addNOp1p(exprsp);
        setOp2p(fromp);
    }
    ASTNODE_NODE_FUNCS(SScanF)
    virtual string name() const override { return m_text; }
    virtual string verilogKwd() const override { return "$sscanf"; }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }  // SPECIAL: has 'visual' ordering
    virtual bool isOutputter() const override { return true; }  // SPECIAL: makes output
    virtual bool cleanOut() const override { return false; }
    virtual V3Hash sameHash() const override { return V3Hash(text()); }
    virtual bool same(const AstNode* samep) const override {
        return text() == static_cast<const AstSScanF*>(samep)->text();
    }
    AstNode* exprsp() const { return op1p(); }  // op1 = Expressions to output
    void exprsp(AstNode* nodep) { addOp1p(nodep); }  // op1 = Expressions to output
    string text() const { return m_text; }  // * = Text to display
    void text(const string& text) { m_text = text; }
    AstNode* fromp() const { return op2p(); }
    void fromp(AstNode* nodep) { setOp2p(nodep); }
};

class AstNodeReadWriteMem VL_NOT_FINAL : public AstNodeStmt {
private:
    bool m_isHex;  // readmemh, not readmemb
public:
    AstNodeReadWriteMem(AstType t, FileLine* fl, bool hex, AstNode* filenamep, AstNode* memp,
                        AstNode* lsbp, AstNode* msbp)
        : AstNodeStmt(t, fl)
        , m_isHex(hex) {
        setOp1p(filenamep);
        setOp2p(memp);
        setNOp3p(lsbp);
        setNOp4p(msbp);
    }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isHeavy() const override { return true; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    virtual bool isUnlikely() const override { return true; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override {
        return isHex() == static_cast<const AstNodeReadWriteMem*>(samep)->isHex();
    }
    bool isHex() const { return m_isHex; }
    AstNode* filenamep() const { return op1p(); }
    AstNode* memp() const { return op2p(); }
    AstNode* lsbp() const { return op3p(); }
    AstNode* msbp() const { return op4p(); }
    virtual const char* cFuncPrefixp() const = 0;
};

class AstReadMem final : public AstNodeReadWriteMem {
public:
    AstReadMem(FileLine* fl, bool hex, AstNode* filenamep, AstNode* memp, AstNode* lsbp,
               AstNode* msbp)
        : ASTGEN_SUPER(fl, hex, filenamep, memp, lsbp, msbp) {}
    ASTNODE_NODE_FUNCS(ReadMem);
    virtual string verilogKwd() const override { return (isHex() ? "$readmemh" : "$readmemb"); }
    virtual const char* cFuncPrefixp() const override { return "VL_READMEM_"; }
};

class AstWriteMem final : public AstNodeReadWriteMem {
public:
    AstWriteMem(FileLine* fl, bool hex, AstNode* filenamep, AstNode* memp, AstNode* lsbp,
                AstNode* msbp)
        : ASTGEN_SUPER(fl, hex, filenamep, memp, lsbp, msbp) {}
    ASTNODE_NODE_FUNCS(WriteMem)
    virtual string verilogKwd() const override { return (isHex() ? "$writememh" : "$writememb"); }
    virtual const char* cFuncPrefixp() const override { return "VL_WRITEMEM_"; }
};

class AstMonitorOff final : public AstNodeStmt {
    bool m_off;  // Monitor off.  Using 0=on allows faster init and comparison

public:
    AstMonitorOff(FileLine* fl, bool off)
        : ASTGEN_SUPER(fl)
        , m_off{off} {}
    ASTNODE_NODE_FUNCS(MonitorOff)
    virtual string verilogKwd() const override { return m_off ? "$monitoroff" : "$monitoron"; }
    virtual bool isGateOptimizable() const override { return false; }  // Though deleted before opt
    virtual bool isPredictOptimizable() const override {
        return false;
    }  // Though deleted before opt
    virtual bool isPure() const override { return false; }  // Though deleted before opt
    virtual bool isOutputter() const override { return true; }  // Though deleted before opt
    virtual int instrCount() const override { return instrCountPli(); }
    virtual V3Hash sameHash() const override { return V3Hash(m_off); }
    virtual bool same(const AstNode* samep) const override {
        return m_off == static_cast<const AstMonitorOff*>(samep)->m_off;
    }
    bool off() const { return m_off; }
};

class AstSystemT final : public AstNodeStmt {
    // $system used as task
public:
    AstSystemT(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl) {
        setOp1p(lhsp);
    }
    ASTNODE_NODE_FUNCS(SystemT)
    virtual string verilogKwd() const override { return "$system"; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    virtual bool isUnlikely() const override { return true; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    AstNode* lhsp() const { return op1p(); }
};

class AstSystemF final : public AstNodeMath {
    // $system used as function
public:
    AstSystemF(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl) {
        setOp1p(lhsp);
    }
    ASTNODE_NODE_FUNCS(SystemF)
    virtual string verilogKwd() const override { return "$system"; }
    virtual string emitVerilog() override { return verilogKwd(); }
    virtual string emitC() override { return "VL_SYSTEM_%nq(%lw, %P)"; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    virtual bool isUnlikely() const override { return true; }
    virtual bool cleanOut() const override { return true; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    AstNode* lhsp() const { return op1p(); }
};

class AstValuePlusArgs final : public AstNodeMath {
    // Parents: expr
    // Child: variable to set.  If nullptr then this is a $test$plusargs instead of $value$plusargs
public:
    AstValuePlusArgs(FileLine* fl, AstNode* searchp, AstNode* outp)
        : ASTGEN_SUPER(fl) {
        setOp1p(searchp);
        setOp2p(outp);
    }
    ASTNODE_NODE_FUNCS(ValuePlusArgs)
    virtual string verilogKwd() const override { return "$value$plusargs"; }
    virtual string emitVerilog() override { return "%f$value$plusargs(%l, %k%r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isHeavy() const override { return true; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool cleanOut() const override { return true; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    AstNode* searchp() const { return op1p(); }  // op1 = Search expression
    void searchp(AstNode* nodep) { setOp1p(nodep); }
    AstNode* outp() const { return op2p(); }  // op2 = Expressions to output
    void outp(AstNode* nodep) { setOp2p(nodep); }
};

class AstTestPlusArgs final : public AstNodeMath {
    // Parents: expr
    // Child: variable to set.  If nullptr then this is a $test$plusargs instead of $value$plusargs
private:
    string m_text;

public:
    AstTestPlusArgs(FileLine* fl, const string& text)
        : ASTGEN_SUPER(fl)
        , m_text{text} {}
    ASTNODE_NODE_FUNCS(TestPlusArgs)
    virtual string name() const override { return m_text; }
    virtual string verilogKwd() const override { return "$test$plusargs"; }
    virtual string emitVerilog() override { return verilogKwd(); }
    virtual string emitC() override { return "VL_VALUEPLUSARGS_%nq(%lw, %P, nullptr)"; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool cleanOut() const override { return true; }
    virtual V3Hash sameHash() const override { return V3Hash(text()); }
    virtual bool same(const AstNode* samep) const override {
        return text() == static_cast<const AstTestPlusArgs*>(samep)->text();
    }
    string text() const { return m_text; }  // * = Text to display
    void text(const string& text) { m_text = text; }
};

class AstGenFor final : public AstNodeFor {
public:
    AstGenFor(FileLine* fl, AstNode* initsp, AstNode* condp, AstNode* incsp, AstNode* bodysp)
        : ASTGEN_SUPER(fl, initsp, condp, incsp, bodysp) {}
    ASTNODE_NODE_FUNCS(GenFor)
};

class AstForeach final : public AstNodeStmt {
public:
    AstForeach(FileLine* fl, AstNode* arrayp, AstNode* bodysp)
        : ASTGEN_SUPER(fl) {
        setOp1p(arrayp);
        addNOp4p(bodysp);
    }
    ASTNODE_NODE_FUNCS(Foreach)
    AstNode* arrayp() const { return op1p(); }  // op1 = array and index vars
    AstNode* bodysp() const { return op4p(); }  // op4 = body of loop
    virtual bool isGateOptimizable() const override { return false; }
    virtual int instrCount() const override { return instrCountBranch(); }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
};

class AstRepeat final : public AstNodeStmt {
public:
    AstRepeat(FileLine* fl, AstNode* countp, AstNode* bodysp)
        : ASTGEN_SUPER(fl) {
        setOp2p(countp);
        addNOp3p(bodysp);
    }
    ASTNODE_NODE_FUNCS(Repeat)
    AstNode* countp() const { return op2p(); }  // op2 = condition to continue
    AstNode* bodysp() const { return op3p(); }  // op3 = body of loop
    virtual bool isGateOptimizable() const override {
        return false;
    }  // Not relevant - converted to FOR
    virtual int instrCount() const override { return instrCountBranch(); }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
};

class AstWait final : public AstNodeStmt {
public:
    AstWait(FileLine* fl, AstNode* condp, AstNode* bodysp)
        : ASTGEN_SUPER(fl) {
        setOp2p(condp);
        addNOp3p(bodysp);
    }
    ASTNODE_NODE_FUNCS(Wait)
    AstNode* bodysp() const { return op3p(); }  // op3 = body of loop
};

class AstWhile final : public AstNodeStmt {
public:
    AstWhile(FileLine* fl, AstNode* condp, AstNode* bodysp, AstNode* incsp = nullptr)
        : ASTGEN_SUPER(fl) {
        setOp2p(condp);
        addNOp3p(bodysp);
        addNOp4p(incsp);
    }
    ASTNODE_NODE_FUNCS(While)
    // op1 = prepare statements for condition (exec every loop)
    AstNode* precondsp() const { return op1p(); }
    AstNode* condp() const { return op2p(); }  // op2 = condition to continue
    AstNode* bodysp() const { return op3p(); }  // op3 = body of loop
    AstNode* incsp() const { return op4p(); }  // op4 = increment (if from a FOR loop)
    void addPrecondsp(AstNode* newp) { addOp1p(newp); }
    void addBodysp(AstNode* newp) { addOp3p(newp); }
    void addIncsp(AstNode* newp) { addOp4p(newp); }
    virtual bool isGateOptimizable() const override { return false; }
    virtual int instrCount() const override { return instrCountBranch(); }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    // Stop statement searchback here
    virtual void addBeforeStmt(AstNode* newp, AstNode* belowp) override;
    // Stop statement searchback here
    virtual void addNextStmt(AstNode* newp, AstNode* belowp) override;
};

class AstBreak final : public AstNodeStmt {
public:
    explicit AstBreak(FileLine* fl)
        : ASTGEN_SUPER(fl) {}
    ASTNODE_NODE_FUNCS(Break)
    virtual string verilogKwd() const override { return "break"; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool isBrancher() const override {
        return true;  // SPECIAL: We don't process code after breaks
    }
};

class AstContinue final : public AstNodeStmt {
public:
    explicit AstContinue(FileLine* fl)
        : ASTGEN_SUPER(fl) {}
    ASTNODE_NODE_FUNCS(Continue)
    virtual string verilogKwd() const override { return "continue"; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool isBrancher() const override {
        return true;  // SPECIAL: We don't process code after breaks
    }
};

class AstDisable final : public AstNodeStmt {
private:
    string m_name;  // Name of block
public:
    AstDisable(FileLine* fl, const string& name)
        : ASTGEN_SUPER(fl)
        , m_name{name} {}
    ASTNODE_NODE_FUNCS(Disable)
    virtual string name() const override { return m_name; }  // * = Block name
    virtual void name(const string& flag) override { m_name = flag; }
    virtual bool isBrancher() const override {
        return true;  // SPECIAL: We don't process code after breaks
    }
};

class AstDisableFork final : public AstNodeStmt {
    // A "disable fork" statement
public:
    explicit AstDisableFork(FileLine* fl)
        : ASTGEN_SUPER(fl) {}
    ASTNODE_NODE_FUNCS(DisableFork)
};

class AstWaitFork final : public AstNodeStmt {
    // A "wait fork" statement
public:
    explicit AstWaitFork(FileLine* fl)
        : ASTGEN_SUPER(fl) {}
    ASTNODE_NODE_FUNCS(WaitFork)
};

class AstReturn final : public AstNodeStmt {
public:
    explicit AstReturn(FileLine* fl, AstNode* lhsp = nullptr)
        : ASTGEN_SUPER(fl) {
        setNOp1p(lhsp);
    }
    ASTNODE_NODE_FUNCS(Return)
    virtual string verilogKwd() const override { return "return"; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    AstNode* lhsp() const { return op1p(); }
    virtual bool isBrancher() const override {
        return true;  // SPECIAL: We don't process code after breaks
    }
};

class AstGenIf final : public AstNodeIf {
public:
    AstGenIf(FileLine* fl, AstNode* condp, AstNode* ifsp, AstNode* elsesp)
        : ASTGEN_SUPER(fl, condp, ifsp, elsesp) {}
    ASTNODE_NODE_FUNCS(GenIf)
};

class AstIf final : public AstNodeIf {
private:
    bool m_uniquePragma;  // unique case
    bool m_unique0Pragma;  // unique0 case
    bool m_priorityPragma;  // priority case
public:
    AstIf(FileLine* fl, AstNode* condp, AstNode* ifsp, AstNode* elsesp = nullptr)
        : ASTGEN_SUPER(fl, condp, ifsp, elsesp) {
        m_uniquePragma = false;
        m_unique0Pragma = false;
        m_priorityPragma = false;
    }
    ASTNODE_NODE_FUNCS(If)
    bool uniquePragma() const { return m_uniquePragma; }
    void uniquePragma(bool flag) { m_uniquePragma = flag; }
    bool unique0Pragma() const { return m_unique0Pragma; }
    void unique0Pragma(bool flag) { m_unique0Pragma = flag; }
    bool priorityPragma() const { return m_priorityPragma; }
    void priorityPragma(bool flag) { m_priorityPragma = flag; }
};

class AstJumpBlock final : public AstNodeStmt {
    // Block of code including a JumpGo and JumpLabel
    // Parents:  {statement list}
    // Children: {statement list, with JumpGo and JumpLabel below}
private:
    AstJumpLabel* m_labelp = nullptr;  // [After V3Jump] Pointer to declaration
    int m_labelNum = 0;  // Set by V3EmitCSyms to tell final V3Emit what to increment
public:
    // After construction must call ->labelp to associate with appropriate label
    AstJumpBlock(FileLine* fl, AstNode* stmtsp)
        : ASTGEN_SUPER(fl) {
        addNOp1p(stmtsp);
    }
    virtual const char* broken() const override;
    virtual void cloneRelink() override;
    ASTNODE_NODE_FUNCS(JumpBlock)
    virtual int instrCount() const override { return 0; }
    virtual bool maybePointedTo() const override { return true; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    // op1 = Statements
    AstNode* stmtsp() const { return op1p(); }  // op1 = List of statements
    void addStmtsp(AstNode* nodep) { addNOp1p(nodep); }
    AstNode* endStmtsp() const { return op2p(); }  // op1 = List of end-of-block
    void addEndStmtsp(AstNode* nodep) { addNOp2p(nodep); }
    int labelNum() const { return m_labelNum; }
    void labelNum(int flag) { m_labelNum = flag; }
    AstJumpLabel* labelp() const { return m_labelp; }
    void labelp(AstJumpLabel* labelp) { m_labelp = labelp; }
};

class AstJumpLabel final : public AstNodeStmt {
    // Jump point declaration
    // Parents:  {statement list with JumpBlock above}
    // Children: none
private:
    AstJumpBlock* m_blockp;  // [After V3Jump] Pointer to declaration
public:
    AstJumpLabel(FileLine* fl, AstJumpBlock* blockp)
        : ASTGEN_SUPER(fl)
        , m_blockp{blockp} {}
    ASTNODE_NODE_FUNCS(JumpLabel)
    virtual bool maybePointedTo() const override { return true; }
    virtual const char* broken() const override {
        BROKEN_RTN(!blockp()->brokeExistsAbove());
        BROKEN_RTN(blockp()->labelp() != this);
        return nullptr;
    }
    virtual void cloneRelink() override {
        if (m_blockp->clonep()) m_blockp = m_blockp->clonep();
    }
    virtual void dump(std::ostream& str) const override;
    virtual int instrCount() const override { return 0; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override {
        return blockp() == static_cast<const AstJumpLabel*>(samep)->blockp();
    }
    AstJumpBlock* blockp() const { return m_blockp; }
};

class AstJumpGo final : public AstNodeStmt {
    // Jump point; branch down to a JumpLabel
    // No support for backward jumps at present
    // Parents:  {statement list with JumpBlock above}
    // Children: none
private:
    AstJumpLabel* m_labelp;  // [After V3Jump] Pointer to declaration
public:
    AstJumpGo(FileLine* fl, AstJumpLabel* labelp)
        : ASTGEN_SUPER(fl)
        , m_labelp{labelp} {}
    ASTNODE_NODE_FUNCS(JumpGo);
    virtual const char* broken() const override {
        BROKEN_RTN(!labelp()->brokeExistsBelow());
        return nullptr;
    }
    virtual void cloneRelink() override {
        if (m_labelp->clonep()) m_labelp = m_labelp->clonep();
    }
    virtual void dump(std::ostream& str) const override;
    virtual int instrCount() const override { return instrCountBranch(); }
    virtual V3Hash sameHash() const override { return V3Hash(labelp()); }
    virtual bool same(const AstNode* samep) const override {
        return labelp() == static_cast<const AstJumpGo*>(samep)->labelp();
    }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isBrancher() const override {
        return true;  // SPECIAL: We don't process code after breaks
    }
    AstJumpLabel* labelp() const { return m_labelp; }
};

class AstChangeXor final : public AstNodeBiComAsv {
    // A comparison to determine change detection, common & must be fast.
    // Returns 32-bit or 64-bit value where 0 indicates no change.
    // Parents: OR or LOGOR
    // Children: VARREF
public:
    AstChangeXor(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetUInt32();  // Always used on, and returns word entities
    }
    ASTNODE_NODE_FUNCS(ChangeXor)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstChangeXor(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opChangeXor(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f^ %r)"; }
    virtual string emitC() override { return "VL_CHANGEXOR_%li(%lw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "^"; }
    virtual bool cleanOut() const override { return false; }  // Lclean && Rclean
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs(); }
};

class AstChangeDet final : public AstNodeStmt {
    // A comparison to determine change detection, common & must be fast.
private:
    bool m_clockReq;  // Type of detection
public:
    // Null lhs+rhs used to indicate change needed with no spec vars
    AstChangeDet(FileLine* fl, AstNode* lhsp, AstNode* rhsp, bool clockReq)
        : ASTGEN_SUPER(fl) {
        setNOp1p(lhsp);
        setNOp2p(rhsp);
        m_clockReq = clockReq;
    }
    ASTNODE_NODE_FUNCS(ChangeDet)
    AstNode* lhsp() const { return op1p(); }
    AstNode* rhsp() const { return op2p(); }
    bool isClockReq() const { return m_clockReq; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual int instrCount() const override { return widthInstrs(); }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
};

class AstConsAssoc final : public AstNodeMath {
    // Construct an assoc array and return object, '{}
    // Parents: math
    // Children: expression (elements or other queues)
public:
    AstConsAssoc(FileLine* fl, AstNode* defaultp)
        : ASTGEN_SUPER(fl) {
        setNOp1p(defaultp);
    }
    ASTNODE_NODE_FUNCS(ConsAssoc)
    virtual string emitVerilog() override { return "'{}"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual int instrCount() const override { return widthInstrs(); }
    AstNode* defaultp() const { return op1p(); }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
};
class AstSetAssoc final : public AstNodeMath {
    // Set an assoc array element and return object, '{}
    // Parents: math
    // Children: expression (elements or other queues)
public:
    AstSetAssoc(FileLine* fl, AstNode* lhsp, AstNode* keyp, AstNode* valuep)
        : ASTGEN_SUPER(fl) {
        setOp1p(lhsp);
        setNOp2p(keyp);
        setOp3p(valuep);
    }
    ASTNODE_NODE_FUNCS(SetAssoc)
    virtual string emitVerilog() override { return "'{}"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual int instrCount() const override { return widthInstrs(); }
    AstNode* lhsp() const { return op1p(); }
    AstNode* keyp() const { return op2p(); }
    AstNode* valuep() const { return op3p(); }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
};

class AstConsDynArray final : public AstNodeMath {
    // Construct a queue and return object, '{}. '{lhs}, '{lhs. rhs}
    // Parents: math
    // Children: expression (elements or other queues)
public:
    explicit AstConsDynArray(FileLine* fl, AstNode* lhsp = nullptr, AstNode* rhsp = nullptr)
        : ASTGEN_SUPER(fl) {
        setNOp1p(lhsp);
        setNOp2p(rhsp);
    }
    ASTNODE_NODE_FUNCS(ConsDynArray)
    virtual string emitVerilog() override { return "'{%l, %r}"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual int instrCount() const override { return widthInstrs(); }
    AstNode* lhsp() const { return op1p(); }  // op1 = expression
    AstNode* rhsp() const { return op2p(); }  // op2 = expression
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
};

class AstConsQueue final : public AstNodeMath {
    // Construct a queue and return object, '{}. '{lhs}, '{lhs. rhs}
    // Parents: math
    // Children: expression (elements or other queues)
public:
    explicit AstConsQueue(FileLine* fl, AstNode* lhsp = nullptr, AstNode* rhsp = nullptr)
        : ASTGEN_SUPER(fl) {
        setNOp1p(lhsp);
        setNOp2p(rhsp);
    }
    ASTNODE_NODE_FUNCS(ConsQueue)
    virtual string emitVerilog() override { return "'{%l, %r}"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual int instrCount() const override { return widthInstrs(); }
    AstNode* lhsp() const { return op1p(); }  // op1 = expression
    AstNode* rhsp() const { return op2p(); }  // op2 = expression
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
};

class AstBegin final : public AstNodeBlock {
    // A Begin/end named block, only exists shortly after parsing until linking
    // Parents: statement
    // Children: statements
private:
    bool m_generate;  // Underneath a generate
    bool m_implied;  // Not inserted by user
public:
    // Node that simply puts name into the output stream
    AstBegin(FileLine* fl, const string& name, AstNode* stmtsp, bool generate = false,
             bool implied = false)
        : ASTGEN_SUPER(fl, name, stmtsp)
        , m_generate{generate}
        , m_implied{implied} {}
    ASTNODE_NODE_FUNCS(Begin)
    virtual void dump(std::ostream& str) const override;
    // op1p is statements in NodeBlock
    AstNode* genforp() const { return op2p(); }  // op2 = GENFOR, if applicable,
    // might NOT be a GenFor, as loop unrolling replaces with Begin
    void addGenforp(AstGenFor* nodep) { addOp2p(nodep); }
    void generate(bool flag) { m_generate = flag; }
    bool generate() const { return m_generate; }
    bool implied() const { return m_implied; }
};

class AstFork final : public AstNodeBlock {
    // A fork named block
    // Parents: statement
    // Children: statements
private:
    VJoinType m_joinType;  // Join keyword type
public:
    // Node that simply puts name into the output stream
    AstFork(FileLine* fl, const string& name, AstNode* stmtsp)
        : ASTGEN_SUPER(fl, name, stmtsp) {}
    ASTNODE_NODE_FUNCS(Fork)
    virtual void dump(std::ostream& str) const override;
    VJoinType joinType() const { return m_joinType; }
    void joinType(const VJoinType& flag) { m_joinType = flag; }
};

class AstInside final : public AstNodeMath {
public:
    AstInside(FileLine* fl, AstNode* exprp, AstNode* itemsp)
        : ASTGEN_SUPER(fl) {
        addOp1p(exprp);
        addOp2p(itemsp);
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(Inside)
    AstNode* exprp() const { return op1p(); }  // op1 = LHS expression to compare with
    // op2 = RHS, possibly a list of expr or AstInsideRange
    AstNode* itemsp() const { return op2p(); }
    virtual string emitVerilog() override { return "%l inside { %r }"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return false; }  // NA
};

class AstInsideRange final : public AstNodeMath {
public:
    AstInsideRange(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl) {
        addOp1p(lhsp);
        addOp2p(rhsp);
    }
    ASTNODE_NODE_FUNCS(InsideRange)
    AstNode* lhsp() const { return op1p(); }  // op1 = LHS
    AstNode* rhsp() const { return op2p(); }  // op2 = RHS
    virtual string emitVerilog() override { return "[%l:%r]"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return false; }  // NA
    // Create AstAnd(AstGte(...), AstLte(...))
    AstNode* newAndFromInside(AstNode* exprp, AstNode* lhsp, AstNode* rhsp);
};

class AstInitItem final : public AstNode {
    // Container for a item in an init array
    // This container is present so that the value underneath may get replaced with a new nodep
    // and the upper AstInitArray's map will remain correct (pointing to this InitItem)
public:
    // Parents: INITARRAY
    AstInitItem(FileLine* fl, AstNode* valuep)
        : ASTGEN_SUPER(fl) {
        addOp1p(valuep);
    }
    ASTNODE_NODE_FUNCS(InitItem)
    virtual bool maybePointedTo() const override { return true; }
    virtual bool hasDType() const override { return false; }  // See valuep()'s dtype instead
    virtual V3Hash sameHash() const override { return V3Hash(); }
    AstNode* valuep() const { return op1p(); }  // op1 = Value
    void valuep(AstNode* nodep) { addOp1p(nodep); }
};

class AstInitArray final : public AstNode {
    // Set a var to a map of values
    // The list of initsp() is not relevant
    // If default is specified, the vector may be sparse, and not provide each value.
    // Key values are C++ array style, with lo() at index 0
    // Parents: ASTVAR::init()
    // Children: AstInitItem
public:
    using KeyItemMap = std::map<uint32_t, AstInitItem*>;

private:
    KeyItemMap m_map;  // Node value for each array index
public:
    AstInitArray(FileLine* fl, AstNodeArrayDType* newDTypep, AstNode* defaultp)
        : ASTGEN_SUPER(fl) {
        dtypep(newDTypep);
        addNOp1p(defaultp);
    }
    ASTNODE_NODE_FUNCS(InitArray)
    virtual void dump(std::ostream& str) const override;
    virtual const char* broken() const override {
        for (KeyItemMap::const_iterator it = m_map.begin(); it != m_map.end(); ++it) {
            BROKEN_RTN(!VN_IS(it->second, InitItem));
            BROKEN_RTN(!it->second->brokeExists());
        }
        return nullptr;
    }
    virtual void cloneRelink() override {
        for (KeyItemMap::iterator it = m_map.begin(); it != m_map.end(); ++it) {
            if (it->second->clonep()) it->second = it->second->clonep();
        }
    }
    virtual bool hasDType() const override { return true; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override {
        // Only works if exact same children, instead should override comparison
        // of children list, and instead use map-vs-map key/value compare
        return m_map == static_cast<const AstInitArray*>(samep)->m_map;
    }
    AstNode* defaultp() const { return op1p(); }  // op1 = Default if sparse
    void defaultp(AstNode* newp) { setOp1p(newp); }
    AstNode* initsp() const { return op2p(); }  // op2 = Initial value expressions
    void addValuep(AstNode* newp) { addIndexValuep(m_map.size(), newp); }
    const KeyItemMap& map() const { return m_map; }
    AstNode* addIndexValuep(uint32_t index, AstNode* newp) {
        // Returns old value, caller must garbage collect
        AstNode* oldp = nullptr;
        const auto it = m_map.find(index);
        if (it != m_map.end()) {
            oldp = it->second->valuep();
            it->second->valuep(newp);
        } else {
            AstInitItem* itemp = new AstInitItem(fileline(), newp);
            m_map.emplace(index, itemp);
            addOp2p(itemp);
        }
        return oldp;
    }
    AstNode* getIndexValuep(uint32_t index) const {
        const auto it = m_map.find(index);
        if (it == m_map.end()) {
            return nullptr;
        } else {
            return it->second->valuep();
        }
    }
    AstNode* getIndexDefaultedValuep(uint32_t index) const {
        AstNode* valuep = getIndexValuep(index);
        if (!valuep) valuep = defaultp();
        return valuep;
    }
};

class AstNew final : public AstNodeFTaskRef {
    // New as constructor
    // Don't need the class we are extracting from, as the "fromp()"'s datatype can get us to it
    // Parents: math|stmt
    // Children: varref|arraysel, math
public:
    AstNew(FileLine* fl, AstNode* pinsp)
        : ASTGEN_SUPER(fl, false, "new", pinsp) {}
    ASTNODE_NODE_FUNCS(New)
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool cleanOut() const { return true; }
    virtual bool same(const AstNode* samep) const override { return true; }
    virtual bool hasDType() const override { return true; }
    virtual int instrCount() const override { return widthInstrs(); }
};

class AstNewCopy final : public AstNodeMath {
    // New as shallow copy
    // Parents: math|stmt
    // Children: varref|arraysel, math
public:
    AstNewCopy(FileLine* fl, AstNode* rhsp)
        : ASTGEN_SUPER(fl) {
        dtypeFrom(rhsp);  // otherwise V3Width will resolve
        setNOp1p(rhsp);
    }
    ASTNODE_NODE_FUNCS(NewCopy)
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual string emitVerilog() override { return "new"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual bool same(const AstNode* samep) const override { return true; }
    virtual int instrCount() const override { return widthInstrs(); }
    AstNode* rhsp() const { return op1p(); }
};

class AstNewDynamic final : public AstNodeMath {
    // New for dynamic array
    // Parents: math|stmt
    // Children: varref|arraysel, math
public:
    AstNewDynamic(FileLine* fl, AstNode* sizep, AstNode* rhsp)
        : ASTGEN_SUPER(fl) {
        dtypeFrom(rhsp);  // otherwise V3Width will resolve
        setNOp1p(sizep);
        setNOp2p(rhsp);
    }
    ASTNODE_NODE_FUNCS(NewDynamic)
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual string emitVerilog() override { return "new"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual bool same(const AstNode* samep) const override { return true; }
    virtual int instrCount() const override { return widthInstrs(); }
    AstNode* sizep() const { return op1p(); }
    AstNode* rhsp() const { return op2p(); }
};

class AstPragma final : public AstNode {
private:
    AstPragmaType m_pragType;  // Type of pragma
public:
    // Pragmas don't result in any output code, they're just flags that affect
    // other processing in verilator.
    AstPragma(FileLine* fl, AstPragmaType pragType)
        : ASTGEN_SUPER(fl)
        , m_pragType{pragType} {}
    ASTNODE_NODE_FUNCS(Pragma)
    AstPragmaType pragType() const { return m_pragType; }  // *=type of the pragma
    virtual V3Hash sameHash() const override { return V3Hash(pragType()); }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool same(const AstNode* samep) const override {
        return pragType() == static_cast<const AstPragma*>(samep)->pragType();
    }
};

class AstPrintTimeScale final : public AstNodeStmt {
    // Parents: stmtlist
    string m_name;  // Parent module name
    VTimescale m_timeunit;  // Parent module time unit
public:
    explicit AstPrintTimeScale(FileLine* fl)
        : ASTGEN_SUPER(fl) {}
    ASTNODE_NODE_FUNCS(PrintTimeScale)
    virtual void name(const string& name) override { m_name = name; }
    virtual string name() const override { return m_name; }  // * = Var name
    virtual void dump(std::ostream& str) const override;
    virtual string verilogKwd() const override { return "$printtimescale"; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    virtual int instrCount() const override { return instrCountPli(); }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    void timeunit(const VTimescale& flag) { m_timeunit = flag; }
    VTimescale timeunit() const { return m_timeunit; }
};

class AstStop final : public AstNodeStmt {
public:
    AstStop(FileLine* fl, bool maybe)
        : ASTGEN_SUPER(fl) {}
    ASTNODE_NODE_FUNCS(Stop)
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override {
        return false;
    }  // SPECIAL: $display has 'visual' ordering
    virtual bool isOutputter() const override { return true; }  // SPECIAL: $display makes output
    virtual bool isUnlikely() const override { return true; }
    virtual int instrCount() const override { return 0; }  // Rarely executes
    virtual V3Hash sameHash() const override { return V3Hash(fileline()->lineno()); }
    virtual bool same(const AstNode* samep) const override {
        return fileline() == samep->fileline();
    }
};

class AstFinish final : public AstNodeStmt {
public:
    explicit AstFinish(FileLine* fl)
        : ASTGEN_SUPER(fl) {}
    ASTNODE_NODE_FUNCS(Finish)
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override {
        return false;
    }  // SPECIAL: $display has 'visual' ordering
    virtual bool isOutputter() const override { return true; }  // SPECIAL: $display makes output
    virtual bool isUnlikely() const override { return true; }
    virtual int instrCount() const override { return 0; }  // Rarely executes
    virtual V3Hash sameHash() const override { return V3Hash(fileline()->lineno()); }
    virtual bool same(const AstNode* samep) const override {
        return fileline() == samep->fileline();
    }
};

class AstNullCheck final : public AstNodeUniop {
    // Return LHS after checking that LHS is non-null
    // Children: VarRef or something returning pointer
public:
    AstNullCheck(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(NullCheck)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { V3ERROR_NA; }
    virtual int instrCount() const override { return 1; }  // Rarely executes
    virtual string emitVerilog() override { return "%l"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual V3Hash sameHash() const override { return V3Hash(fileline()->lineno()); }
    virtual bool same(const AstNode* samep) const override {
        return fileline() == samep->fileline();
    }
};

class AstTimingControl final : public AstNodeStmt {
    // Parents: stmtlist
public:
    AstTimingControl(FileLine* fl, AstSenTree* sensesp, AstNode* stmtsp)
        : ASTGEN_SUPER(fl) {
        setNOp1p(sensesp);
        setNOp2p(stmtsp);
    }
    ASTNODE_NODE_FUNCS(TimingControl)
    virtual string verilogKwd() const override { return "@(%l) %r"; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }
    virtual bool isOutputter() const override { return false; }
    virtual int instrCount() const override { return 0; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    AstSenTree* sensesp() const { return VN_CAST(op1p(), SenTree); }
    AstNode* stmtsp() const { return op2p(); }
};

class AstTimeFormat final : public AstNodeStmt {
    // Parents: stmtlist
public:
    AstTimeFormat(FileLine* fl, AstNode* unitsp, AstNode* precisionp, AstNode* suffixp,
                  AstNode* widthp)
        : ASTGEN_SUPER(fl) {
        setOp1p(unitsp);
        setOp2p(precisionp);
        setOp3p(suffixp);
        setOp4p(widthp);
    }
    ASTNODE_NODE_FUNCS(TimeFormat)
    virtual string verilogKwd() const override { return "$timeformat"; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    virtual int instrCount() const override { return instrCountPli(); }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    AstNode* unitsp() const { return op1p(); }
    AstNode* precisionp() const { return op2p(); }
    AstNode* suffixp() const { return op3p(); }
    AstNode* widthp() const { return op4p(); }
};

class AstTraceDecl final : public AstNodeStmt {
    // Trace point declaration
    // Separate from AstTraceInc; as a declaration can't be deleted
    // Parents:  {statement list}
    // Children: expression being traced
private:
    uint32_t m_code = 0;  // Trace identifier code; converted to ASCII by trace routines
    const string m_showname;  // Name of variable
    const VNumRange m_bitRange;  // Property of var the trace details
    const VNumRange m_arrayRange;  // Property of var the trace details
    const uint32_t m_codeInc;  // Code increment
    const AstVarType m_varType;  // Type of variable (for localparam vs. param)
    const AstBasicDTypeKwd m_declKwd;  // Keyword at declaration time
    const VDirection m_declDirection;  // Declared direction input/output etc
    const bool m_isScoped;  // Uses run-time scope (for interfaces)
public:
    AstTraceDecl(FileLine* fl, const string& showname,
                 AstVar* varp,  // For input/output state etc
                 AstNode* valuep, const VNumRange& bitRange, const VNumRange& arrayRange,
                 bool isScoped)
        : ASTGEN_SUPER(fl)
        , m_showname{showname}
        , m_bitRange{bitRange}
        , m_arrayRange{arrayRange}
        , m_codeInc(
              ((arrayRange.ranged() ? arrayRange.elements() : 1) * valuep->dtypep()->widthWords()
               * (VL_EDATASIZE / 32)))  // A code is always 32-bits
        , m_varType{varp->varType()}
        , m_declKwd{varp->declKwd()}
        , m_declDirection{varp->declDirection()}
        , m_isScoped{isScoped} {
        dtypeFrom(valuep);
        addNOp1p(valuep);
    }
    virtual int instrCount() const override { return 100; }  // Large...
    ASTNODE_NODE_FUNCS(TraceDecl)
    virtual string name() const override { return m_showname; }
    virtual bool maybePointedTo() const override { return true; }
    virtual bool hasDType() const override { return true; }
    virtual bool same(const AstNode* samep) const override { return false; }
    string showname() const { return m_showname; }  // * = Var name
    // Details on what we're tracing
    uint32_t code() const { return m_code; }
    void code(uint32_t code) { m_code = code; }
    uint32_t codeInc() const { return m_codeInc; }
    const VNumRange& bitRange() const { return m_bitRange; }
    const VNumRange& arrayRange() const { return m_arrayRange; }
    AstVarType varType() const { return m_varType; }
    AstBasicDTypeKwd declKwd() const { return m_declKwd; }
    VDirection declDirection() const { return m_declDirection; }
    bool isScoped() const { return m_isScoped; }
    AstNode* valuep() const { return op1p(); }
};

class AstTraceInc final : public AstNodeStmt {
    // Trace point dump
    // Parents:  {statement list}
    // Children: op1: things to emit before this node,
    //           op2: expression being traced (from decl)

private:
    AstTraceDecl* m_declp;  // Pointer to declaration
    const bool m_full;  // Is this a full vs incremental dump
public:
    AstTraceInc(FileLine* fl, AstTraceDecl* declp, bool full)
        : ASTGEN_SUPER(fl)
        , m_declp{declp}
        , m_full{full} {
        dtypeFrom(declp);
        addOp2p(declp->valuep()->cloneTree(true));
    }
    ASTNODE_NODE_FUNCS(TraceInc)
    virtual const char* broken() const override {
        BROKEN_RTN(!declp()->brokeExists());
        return nullptr;
    }
    virtual void cloneRelink() override {
        if (m_declp->clonep()) m_declp = m_declp->clonep();
    }
    virtual void dump(std::ostream& str) const override;
    virtual int instrCount() const override { return 10 + 2 * instrCountLd(); }
    virtual bool hasDType() const override { return true; }
    virtual V3Hash sameHash() const override { return V3Hash(declp()); }
    virtual bool same(const AstNode* samep) const override {
        return declp() == static_cast<const AstTraceInc*>(samep)->declp();
    }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    // but isPure()  true
    // op1 = Statements before the value
    AstNode* precondsp() const { return op1p(); }
    void addPrecondsp(AstNode* newp) { addOp1p(newp); }
    AstNode* valuep() const { return op2p(); }
    AstTraceDecl* declp() const { return m_declp; }
    bool full() const { return m_full; }
};

class AstActive final : public AstNode {
    // Block of code with sensitivity activation
    // Parents:  MODULE | CFUNC
    // Children: SENTREE, statements
private:
    string m_name;
    AstSenTree* m_sensesp;

public:
    AstActive(FileLine* fl, const string& name, AstSenTree* sensesp)
        : ASTGEN_SUPER(fl) {
        m_name = name;  // Copy it
        UASSERT(sensesp, "Sensesp required arg");
        m_sensesp = sensesp;
    }
    ASTNODE_NODE_FUNCS(Active)
    virtual void dump(std::ostream& str = std::cout) const override;
    virtual string name() const override { return m_name; }
    virtual const char* broken() const override {
        BROKEN_RTN(m_sensesp && !m_sensesp->brokeExists());
        return nullptr;
    }
    virtual void cloneRelink() override {
        if (m_sensesp->clonep()) {
            m_sensesp = m_sensesp->clonep();
            UASSERT(m_sensesp, "Bad clone cross link: " << this);
        }
    }
    // Statements are broken into pieces, as some must come before others.
    void sensesp(AstSenTree* nodep) { m_sensesp = nodep; }
    AstSenTree* sensesp() const { return m_sensesp; }
    // op1 = Sensitivity tree, if a clocked block in early stages
    void sensesStorep(AstSenTree* nodep) { addOp1p(nodep); }
    AstSenTree* sensesStorep() const { return VN_CAST(op1p(), SenTree); }
    // op2 = Combo logic
    AstNode* stmtsp() const { return op2p(); }
    void addStmtsp(AstNode* nodep) { addOp2p(nodep); }
    // METHODS
    bool hasInitial() const { return m_sensesp->hasInitial(); }
    bool hasSettle() const { return m_sensesp->hasSettle(); }
    bool hasClocked() const { return m_sensesp->hasClocked(); }
};

class AstAttrOf final : public AstNode {
private:
    // Return a value of a attribute, for example a LSB or array LSB of a signal
    AstAttrType m_attrType;  // What sort of extraction
public:
    AstAttrOf(FileLine* fl, AstAttrType attrtype, AstNode* fromp = nullptr,
              AstNode* dimp = nullptr)
        : ASTGEN_SUPER(fl) {
        setNOp1p(fromp);
        setNOp2p(dimp);
        m_attrType = attrtype;
    }
    ASTNODE_NODE_FUNCS(AttrOf)
    AstNode* fromp() const { return op1p(); }
    AstNode* dimp() const { return op2p(); }
    AstAttrType attrType() const { return m_attrType; }
    virtual V3Hash sameHash() const override { return V3Hash(m_attrType); }
    virtual void dump(std::ostream& str = std::cout) const override;
};

class AstScopeName final : public AstNodeMath {
    // For display %m and DPI context imports
    // Parents:  DISPLAY
    // Children: TEXT
private:
    bool m_dpiExport = false;  // Is for dpiExport
    string scopeNameFormatter(AstText* scopeTextp) const;
    string scopePrettyNameFormatter(AstText* scopeTextp) const;

public:
    explicit AstScopeName(FileLine* fl)
        : ASTGEN_SUPER(fl) {
        dtypeSetUInt64();
    }
    ASTNODE_NODE_FUNCS(ScopeName)
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override {
        return m_dpiExport == static_cast<const AstScopeName*>(samep)->m_dpiExport;
    }
    virtual string emitVerilog() override { return ""; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    AstText* scopeAttrp() const { return VN_CAST(op1p(), Text); }
    void scopeAttrp(AstNode* nodep) { addOp1p(nodep); }
    AstText* scopeEntrp() const { return VN_CAST(op2p(), Text); }
    void scopeEntrp(AstNode* nodep) { addOp2p(nodep); }
    string scopeSymName() const {  // Name for __Vscope variable including children
        return scopeNameFormatter(scopeAttrp());
    }
    string scopeDpiName() const {  // Name for DPI import scope
        return scopeNameFormatter(scopeEntrp());
    }
    string scopePrettySymName() const {  // Name for __Vscope variable including children
        return scopePrettyNameFormatter(scopeAttrp());
    }
    string scopePrettyDpiName() const {  // Name for __Vscope variable including children
        return scopePrettyNameFormatter(scopeEntrp());
    }
    bool dpiExport() const { return m_dpiExport; }
    void dpiExport(bool flag) { m_dpiExport = flag; }
};

class AstUdpTable final : public AstNode {
public:
    AstUdpTable(FileLine* fl, AstNode* bodysp)
        : ASTGEN_SUPER(fl) {
        addNOp1p(bodysp);
    }
    ASTNODE_NODE_FUNCS(UdpTable)
    // op1 = List of UdpTableLines
    AstUdpTableLine* bodysp() const { return VN_CAST(op1p(), UdpTableLine); }
};

class AstUdpTableLine final : public AstNode {
    string m_text;

public:
    AstUdpTableLine(FileLine* fl, const string& text)
        : ASTGEN_SUPER(fl)
        , m_text{text} {}
    ASTNODE_NODE_FUNCS(UdpTableLine)
    virtual string name() const override { return m_text; }
    string text() const { return m_text; }
};

//======================================================================
// non-ary ops

class AstRand final : public AstNodeMath {
    // $random/$random(seed) or $urandom/$urandom(seed)
    // Return a random number, based upon width()
private:
    bool m_urandom = false;  // $urandom vs $random
    bool m_reset = false;  // Random reset, versus always random
public:
    class Reset {};
    AstRand(FileLine* fl, Reset, AstNodeDType* dtp, bool reset)
        : ASTGEN_SUPER(fl)
        , m_reset{reset} {
        dtypep(dtp);
    }
    AstRand(FileLine* fl, AstNode* seedp, bool urandom)
        : ASTGEN_SUPER(fl)
        , m_urandom(urandom) {
        setNOp1p(seedp);
    }
    ASTNODE_NODE_FUNCS(Rand)
    virtual string emitVerilog() override {
        return seedp() ? (m_urandom ? "%f$urandom(%l)" : "%f$random(%l)")
                       : (m_urandom ? "%f$urandom()" : "%f$random()");
    }
    virtual string emitC() override {
        return m_reset
                   ? "VL_RAND_RESET_%nq(%nw, %P)"
                   : seedp() ? "VL_RANDOM_SEEDED_%nq%lq(%nw, %P, %li)" : "VL_RANDOM_%nq(%nw, %P)";
    }
    virtual bool cleanOut() const override { return true; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual int instrCount() const override { return instrCountPli(); }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    AstNode* seedp() const { return op1p(); }
    bool reset() const { return m_reset; }
    bool urandom() const { return m_urandom; }
};

class AstURandomRange final : public AstNodeBiop {
    // $urandom_range
public:
    explicit AstURandomRange(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetUInt32();  // Says IEEE
    }
    ASTNODE_NODE_FUNCS(URandomRange)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstURandomRange(fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        V3ERROR_NA;
    }
    virtual string emitVerilog() override { return "%f$urandom_range(%l, %r)"; }
    virtual string emitC() override { return "VL_URANDOM_RANGE_%nq(%li, %ri)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual int instrCount() const override { return instrCountPli(); }
};

class AstTime final : public AstNodeTermop {
    VTimescale m_timeunit;  // Parent module time unit
public:
    AstTime(FileLine* fl, const VTimescale& timeunit)
        : ASTGEN_SUPER(fl)
        , m_timeunit{timeunit} {
        dtypeSetUInt64();
    }
    ASTNODE_NODE_FUNCS(Time)
    virtual string emitVerilog() override { return "%f$time"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual int instrCount() const override { return instrCountTime(); }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    virtual void dump(std::ostream& str = std::cout) const override;
    void timeunit(const VTimescale& flag) { m_timeunit = flag; }
    VTimescale timeunit() const { return m_timeunit; }
};

class AstTimeD final : public AstNodeTermop {
    VTimescale m_timeunit;  // Parent module time unit
public:
    AstTimeD(FileLine* fl, const VTimescale& timeunit)
        : ASTGEN_SUPER(fl)
        , m_timeunit{timeunit} {
        dtypeSetDouble();
    }
    ASTNODE_NODE_FUNCS(TimeD)
    virtual string emitVerilog() override { return "%f$realtime"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual int instrCount() const override { return instrCountTime(); }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    virtual void dump(std::ostream& str = std::cout) const override;
    void timeunit(const VTimescale& flag) { m_timeunit = flag; }
    VTimescale timeunit() const { return m_timeunit; }
};

class AstUCFunc final : public AstNodeMath {
    // User's $c function
    // Perhaps this should be an AstNodeListop; but there's only one list math right now
public:
    AstUCFunc(FileLine* fl, AstNode* exprsp)
        : ASTGEN_SUPER(fl) {
        addNOp1p(exprsp);
    }
    ASTNODE_NODE_FUNCS(UCFunc)
    virtual bool cleanOut() const override { return false; }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    AstNode* bodysp() const { return op1p(); }  // op1 = expressions to print
    virtual bool isPure() const override { return false; }  // SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const override { return true; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isSubstOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual int instrCount() const override { return instrCountPli(); }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
};

//======================================================================
// Unary ops

class AstNegate final : public AstNodeUniop {
public:
    AstNegate(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(Negate)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opNegate(lhs); }
    virtual string emitVerilog() override { return "%f(- %l)"; }
    virtual string emitC() override { return "VL_NEGATE_%lq(%lW, %P, %li)"; }
    virtual string emitSimpleOperator() override { return "-"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return true; }
};
class AstNegateD final : public AstNodeUniop {
public:
    AstNegateD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {
        dtypeSetDouble();
    }
    ASTNODE_NODE_FUNCS(NegateD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opNegateD(lhs); }
    virtual string emitVerilog() override { return "%f(- %l)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return "-"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual int instrCount() const override { return instrCountDouble(); }
    virtual bool doubleFlavor() const override { return true; }
};
class AstRedAnd final : public AstNodeUniop {
public:
    AstRedAnd(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(RedAnd)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opRedAnd(lhs); }
    virtual string emitVerilog() override { return "%f(& %l)"; }
    virtual string emitC() override { return "VL_REDAND_%nq%lq(%nw,%lw, %P, %li)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
};
class AstRedOr final : public AstNodeUniop {
public:
    AstRedOr(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(RedOr)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opRedOr(lhs); }
    virtual string emitVerilog() override { return "%f(| %l)"; }
    virtual string emitC() override { return "VL_REDOR_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
};
class AstRedXor final : public AstNodeUniop {
public:
    AstRedXor(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(RedXor)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opRedXor(lhs); }
    virtual string emitVerilog() override { return "%f(^ %l)"; }
    virtual string emitC() override { return "VL_REDXOR_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override {
        int w = lhsp()->width();
        return (w != 1 && w != 2 && w != 4 && w != 8 && w != 16);
    }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual int instrCount() const override { return 1 + V3Number::log2b(width()); }
};

class AstLenN final : public AstNodeUniop {
    // Length of a string
public:
    AstLenN(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {
        dtypeSetSigned32();
    }
    ASTNODE_NODE_FUNCS(LenN)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opLenN(lhs); }
    virtual string emitVerilog() override { return "%f(%l)"; }
    virtual string emitC() override { return "VL_LEN_IN(%li)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
};
class AstLogNot final : public AstNodeUniop {
public:
    AstLogNot(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(LogNot)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opLogNot(lhs); }
    virtual string emitVerilog() override { return "%f(! %l)"; }
    virtual string emitC() override { return "VL_LOGNOT_%nq%lq(%nw,%lw, %P, %li)"; }
    virtual string emitSimpleOperator() override { return "!"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
};
class AstNot final : public AstNodeUniop {
public:
    AstNot(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(Not)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opNot(lhs); }
    virtual string emitVerilog() override { return "%f(~ %l)"; }
    virtual string emitC() override { return "VL_NOT_%lq(%lW, %P, %li)"; }
    virtual string emitSimpleOperator() override { return "~"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return true; }
};
class AstExtend final : public AstNodeUniop {
    // Expand a value into a wider entity by 0 extension.  Width is implied from nodep->width()
public:
    AstExtend(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {}
    AstExtend(FileLine* fl, AstNode* lhsp, int width)
        : ASTGEN_SUPER(fl, lhsp) {
        dtypeSetLogicSized(width, VSigning::UNSIGNED);
    }
    ASTNODE_NODE_FUNCS(Extend)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opAssign(lhs); }
    virtual string emitVerilog() override { return "%l"; }
    virtual string emitC() override { return "VL_EXTEND_%nq%lq(%nw,%lw, %P, %li)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override {
        return false;  // Because the EXTEND operator self-casts
    }
    virtual int instrCount() const override { return 0; }
};
class AstExtendS final : public AstNodeUniop {
    // Expand a value into a wider entity by sign extension.  Width is implied from nodep->width()
public:
    AstExtendS(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {}
    AstExtendS(FileLine* fl, AstNode* lhsp, int width)
        // Important that widthMin be correct, as opExtend requires it after V3Expand
        : ASTGEN_SUPER(fl, lhsp) {
        dtypeSetLogicSized(width, VSigning::UNSIGNED);
    }
    ASTNODE_NODE_FUNCS(ExtendS)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.opExtendS(lhs, lhsp()->widthMinV());
    }
    virtual string emitVerilog() override { return "%l"; }
    virtual string emitC() override { return "VL_EXTENDS_%nq%lq(%nw,%lw, %P, %li)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override {
        return false;  // Because the EXTEND operator self-casts
    }
    virtual int instrCount() const override { return 0; }
    virtual bool signedFlavor() const override { return true; }
};
class AstSigned final : public AstNodeUniop {
    // $signed(lhs)
public:
    AstSigned(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {
        UASSERT_OBJ(!v3Global.assertDTypesResolved(), this,
                    "not coded to create after dtypes resolved");
    }
    ASTNODE_NODE_FUNCS(Signed)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.opAssign(lhs);
        out.isSigned(false);
    }
    virtual string emitVerilog() override { return "%f$signed(%l)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }  // Eliminated before matters
    virtual bool sizeMattersLhs() const override { return true; }  // Eliminated before matters
    virtual int instrCount() const override { return 0; }
};
class AstUnsigned final : public AstNodeUniop {
    // $unsigned(lhs)
public:
    AstUnsigned(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {
        UASSERT_OBJ(!v3Global.assertDTypesResolved(), this,
                    "not coded to create after dtypes resolved");
    }
    ASTNODE_NODE_FUNCS(Unsigned)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.opAssign(lhs);
        out.isSigned(false);
    }
    virtual string emitVerilog() override { return "%f$unsigned(%l)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }  // Eliminated before matters
    virtual bool sizeMattersLhs() const override { return true; }  // Eliminated before matters
    virtual int instrCount() const override { return 0; }
};
class AstRToIS final : public AstNodeUniop {
    // $rtoi(lhs)
public:
    AstRToIS(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {
        dtypeSetSigned32();
    }
    ASTNODE_NODE_FUNCS(RToIS)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opRToIS(lhs); }
    virtual string emitVerilog() override { return "%f$rtoi(%l)"; }
    virtual string emitC() override { return "VL_RTOI_I_D(%li)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }  // Eliminated before matters
    virtual bool sizeMattersLhs() const override { return false; }  // Eliminated before matters
    virtual int instrCount() const override { return instrCountDouble(); }
};
class AstRToIRoundS final : public AstNodeUniop {
    // Convert real to integer, with arbitrary sized output (not just "integer" format)
public:
    AstRToIRoundS(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {
        dtypeSetSigned32();
    }
    ASTNODE_NODE_FUNCS(RToIRoundS)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.opRToIRoundS(lhs);
    }
    virtual string emitVerilog() override { return "%f$rtoi_rounded(%l)"; }
    virtual string emitC() override { return "VL_RTOIROUND_%nq_D(%nw, %P, %li)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual int instrCount() const override { return instrCountDouble(); }
};
class AstIToRD final : public AstNodeUniop {
    // $itor where lhs is unsigned
public:
    AstIToRD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {
        dtypeSetDouble();
    }
    ASTNODE_NODE_FUNCS(IToRD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opIToRD(lhs); }
    virtual string emitVerilog() override { return "%f$itor(%l)"; }
    virtual string emitC() override { return "VL_ITOR_D_%lq(%lw, %li)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual int instrCount() const override { return instrCountDouble(); }
};
class AstISToRD final : public AstNodeUniop {
    // $itor where lhs is signed
public:
    AstISToRD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {
        dtypeSetDouble();
    }
    ASTNODE_NODE_FUNCS(ISToRD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opISToRD(lhs); }
    virtual string emitVerilog() override { return "%f$itor($signed(%l))"; }
    virtual string emitC() override { return "VL_ISTOR_D_%lq(%lw, %li)"; }
    virtual bool emitCheckMaxWords() override { return true; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual int instrCount() const override { return instrCountDouble(); }
};
class AstRealToBits final : public AstNodeUniop {
public:
    AstRealToBits(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {
        dtypeSetUInt64();
    }
    ASTNODE_NODE_FUNCS(RealToBits)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.opRealToBits(lhs);
    }
    virtual string emitVerilog() override { return "%f$realtobits(%l)"; }
    virtual string emitC() override { return "VL_CVT_Q_D(%li)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }  // Eliminated before matters
    virtual bool sizeMattersLhs() const override { return false; }  // Eliminated before matters
    virtual int instrCount() const override { return instrCountDouble(); }
};
class AstBitsToRealD final : public AstNodeUniop {
public:
    AstBitsToRealD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {
        dtypeSetDouble();
    }
    ASTNODE_NODE_FUNCS(BitsToRealD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.opBitsToRealD(lhs);
    }
    virtual string emitVerilog() override { return "%f$bitstoreal(%l)"; }
    virtual string emitC() override { return "VL_CVT_D_Q(%li)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }  // Eliminated before matters
    virtual bool sizeMattersLhs() const override { return false; }  // Eliminated before matters
    virtual int instrCount() const override { return instrCountDouble(); }
};

class AstCLog2 final : public AstNodeUniop {
public:
    AstCLog2(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(CLog2)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opCLog2(lhs); }
    virtual string emitVerilog() override { return "%f$clog2(%l)"; }
    virtual string emitC() override { return "VL_CLOG2_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 16; }
};
class AstCountBits final : public AstNodeQuadop {
    // Number of bits set in vector
public:
    AstCountBits(FileLine* fl, AstNode* exprp, AstNode* ctrl1p)
        : ASTGEN_SUPER(fl, exprp, ctrl1p, ctrl1p->cloneTree(false), ctrl1p->cloneTree(false)) {}
    AstCountBits(FileLine* fl, AstNode* exprp, AstNode* ctrl1p, AstNode* ctrl2p)
        : ASTGEN_SUPER(fl, exprp, ctrl1p, ctrl2p, ctrl2p->cloneTree(false)) {}
    AstCountBits(FileLine* fl, AstNode* exprp, AstNode* ctrl1p, AstNode* ctrl2p, AstNode* ctrl3p)
        : ASTGEN_SUPER(fl, exprp, ctrl1p, ctrl2p, ctrl3p) {}
    ASTNODE_NODE_FUNCS(CountBits)
    virtual void numberOperate(V3Number& out, const V3Number& expr, const V3Number& ctrl1,
                               const V3Number& ctrl2, const V3Number& ctrl3) override {
        out.opCountBits(expr, ctrl1, ctrl2, ctrl3);
    }
    virtual string emitVerilog() override { return "%f$countbits(%l, %r, %f, %o)"; }
    virtual string emitC() override { return ""; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool cleanThs() const override { return true; }
    virtual bool cleanFhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool sizeMattersThs() const override { return false; }
    virtual bool sizeMattersFhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 16; }
};
class AstCountOnes final : public AstNodeUniop {
    // Number of bits set in vector
public:
    AstCountOnes(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(CountOnes)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.opCountOnes(lhs);
    }
    virtual string emitVerilog() override { return "%f$countones(%l)"; }
    virtual string emitC() override { return "VL_COUNTONES_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 16; }
};
class AstIsUnknown final : public AstNodeUniop {
    // True if any unknown bits
public:
    AstIsUnknown(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(IsUnknown)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.opIsUnknown(lhs);
    }
    virtual string emitVerilog() override { return "%f$isunknown(%l)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
};
class AstIsUnbounded final : public AstNodeUniop {
    // True if is unmbounded ($)
public:
    AstIsUnbounded(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(IsUnbounded)
    virtual void numberOperate(V3Number& out, const V3Number&) override {
        // Any constant isn't unbounded
        out.setZero();
    }
    virtual string emitVerilog() override { return "%f$isunbounded(%l)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
};
class AstOneHot final : public AstNodeUniop {
    // True if only single bit set in vector
public:
    AstOneHot(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(OneHot)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opOneHot(lhs); }
    virtual string emitVerilog() override { return "%f$onehot(%l)"; }
    virtual string emitC() override { return "VL_ONEHOT_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 4; }
};
class AstOneHot0 final : public AstNodeUniop {
    // True if only single bit, or no bits set in vector
public:
    AstOneHot0(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(OneHot0)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opOneHot0(lhs); }
    virtual string emitVerilog() override { return "%f$onehot0(%l)"; }
    virtual string emitC() override { return "VL_ONEHOT0_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 3; }
};

class AstCast final : public AstNode {
    // Cast to appropriate data type - note lhsp is value, to match AstTypedef, AstCCast, etc
public:
    AstCast(FileLine* fl, AstNode* lhsp, VFlagChildDType, AstNodeDType* dtp)
        : ASTGEN_SUPER(fl) {
        setOp1p(lhsp);
        setOp2p(dtp);
        dtypeFrom(dtp);
    }
    AstCast(FileLine* fl, AstNode* lhsp, AstNodeDType* dtp)
        : ASTGEN_SUPER(fl) {
        setOp1p(lhsp);
        dtypeFrom(dtp);
    }
    ASTNODE_NODE_FUNCS(Cast)
    virtual bool hasDType() const override { return true; }
    virtual string emitVerilog() { return "((%d)'(%l))"; }
    virtual bool cleanOut() const { V3ERROR_NA_RETURN(true); }
    virtual bool cleanLhs() const { return true; }
    virtual bool sizeMattersLhs() const { return false; }
    AstNode* lhsp() const { return op1p(); }
    AstNode* fromp() const { return lhsp(); }
    void lhsp(AstNode* nodep) { setOp1p(nodep); }
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    AstNodeDType* childDTypep() const { return VN_CAST(op2p(), NodeDType); }
    virtual AstNodeDType* subDTypep() const { return dtypep() ? dtypep() : childDTypep(); }
};

class AstCastDynamic final : public AstNodeBiop {
    // Verilog $cast used as a function
    // Task usage of $cast is converted during parse to assert($cast(...))
    // Parents: MATH
    // Children: MATH
    // lhsp() is value (we are converting FROM) to match AstCCast etc, this
    // is opposite of $cast's order, because the first access is to the
    // value reading from.  Suggest use fromp()/top() instead of lhsp/rhsp().
public:
    AstCastDynamic(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(CastDynamic)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        V3ERROR_NA;
    }
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstCastDynamic(this->fileline(), lhsp, rhsp);
    }
    virtual string emitVerilog() override { return "%f$cast(%r, %l)"; }
    virtual string emitC() override { return "VL_DYNAMIC_CAST(%r, %l)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 20; }
    virtual bool isPure() const override { return true; }
    AstNode* fromp() const { return lhsp(); }
    AstNode* top() const { return rhsp(); }
};

class AstCastParse final : public AstNode {
    // Cast to appropriate type, where we haven't determined yet what the data type is
public:
    AstCastParse(FileLine* fl, AstNode* lhsp, AstNode* dtp)
        : ASTGEN_SUPER(fl) {
        setOp1p(lhsp);
        setOp2p(dtp);
    }
    ASTNODE_NODE_FUNCS(CastParse)
    virtual string emitVerilog() { return "((%d)'(%l))"; }
    virtual string emitC() { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const { V3ERROR_NA_RETURN(true); }
    virtual bool cleanLhs() const { return true; }
    virtual bool sizeMattersLhs() const { return false; }
    AstNode* lhsp() const { return op1p(); }
    AstNode* dtp() const { return op2p(); }
};

class AstCastSize final : public AstNode {
    // Cast to specific size; signed/twostate inherited from lower element per IEEE
public:
    AstCastSize(FileLine* fl, AstNode* lhsp, AstConst* rhsp)
        : ASTGEN_SUPER(fl) {
        setOp1p(lhsp);
        setOp2p(rhsp);
    }
    ASTNODE_NODE_FUNCS(CastSize)
    // No hasDType because widthing removes this node before the hasDType check
    virtual string emitVerilog() { return "((%r)'(%l))"; }
    virtual bool cleanOut() const { V3ERROR_NA_RETURN(true); }
    virtual bool cleanLhs() const { return true; }
    virtual bool sizeMattersLhs() const { return false; }
    AstNode* lhsp() const { return op1p(); }
    AstNode* rhsp() const { return op2p(); }
};

class AstCCast final : public AstNodeUniop {
    // Cast to C-based data type
private:
    int m_size;

public:
    AstCCast(FileLine* fl, AstNode* lhsp, int setwidth, int minwidth = -1)
        : ASTGEN_SUPER(fl, lhsp) {
        m_size = setwidth;
        if (setwidth) {
            if (minwidth == -1) minwidth = setwidth;
            dtypeSetLogicUnsized(setwidth, minwidth, VSigning::UNSIGNED);
        }
    }
    AstCCast(FileLine* fl, AstNode* lhsp, AstNode* typeFromp)
        : ASTGEN_SUPER(fl, lhsp) {
        dtypeFrom(typeFromp);
        m_size = width();
    }
    ASTNODE_NODE_FUNCS(CCast)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opAssign(lhs); }
    virtual string emitVerilog() override { return "%f$_CAST(%l)"; }
    virtual string emitC() override { return "VL_CAST_%nq%lq(%nw,%lw, %P, %li)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }  // Special cased in V3Cast
    virtual V3Hash sameHash() const override { return V3Hash(size()); }
    virtual bool same(const AstNode* samep) const override {
        return size() == static_cast<const AstCCast*>(samep)->size();
    }
    virtual void dump(std::ostream& str = std::cout) const override;
    //
    int size() const { return m_size; }
};

class AstCvtPackString final : public AstNodeUniop {
    // Convert to Verilator Packed String (aka verilog "string")
public:
    AstCvtPackString(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {
        dtypeSetString();
    }
    ASTNODE_NODE_FUNCS(CvtPackString)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { V3ERROR_NA; }
    virtual string emitVerilog() override { return "%f$_CAST(%l)"; }
    virtual string emitC() override { return "VL_CVT_PACK_STR_N%lq(%lW, %li)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
};

class AstFEof final : public AstNodeUniop {
public:
    AstFEof(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(FEof)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { V3ERROR_NA; }
    virtual string emitVerilog() override { return "%f$feof(%l)"; }
    virtual string emitC() override { return "(%li ? feof(VL_CVT_I_FP(%li)) : true)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 16; }
    virtual bool isPure() const override {
        return false;
    }  // SPECIAL: $display has 'visual' ordering
    AstNode* filep() const { return lhsp(); }
};

class AstFError final : public AstNodeMath {
public:
    AstFError(FileLine* fl, AstNode* filep, AstNode* strp)
        : ASTGEN_SUPER(fl) {
        setOp1p(filep);
        setOp2p(strp);
    }
    ASTNODE_NODE_FUNCS(FError)
    virtual string emitVerilog() override { return "%f$ferror(%l, %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const { return true; }
    virtual bool sizeMattersLhs() const { return false; }
    virtual int instrCount() const override { return widthInstrs() * 64; }
    virtual bool isPure() const override {
        return false;
    }  // SPECIAL: $display has 'visual' ordering
    void filep(AstNode* nodep) { setOp1p(nodep); }
    AstNode* filep() const { return op1p(); }
    void strp(AstNode* nodep) { setOp2p(nodep); }
    AstNode* strp() const { return op2p(); }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
};

class AstFGetC final : public AstNodeUniop {
public:
    AstFGetC(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(FGetC)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { V3ERROR_NA; }
    virtual string emitVerilog() override { return "%f$fgetc(%l)"; }
    // Non-existent filehandle returns EOF
    virtual string emitC() override { return "(%li ? fgetc(VL_CVT_I_FP(%li)) : -1)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 64; }
    virtual bool isPure() const override {
        return false;
    }  // SPECIAL: $display has 'visual' ordering
    AstNode* filep() const { return lhsp(); }
};

class AstFUngetC final : public AstNodeBiop {
public:
    AstFUngetC(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(FUngetC)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        V3ERROR_NA;
    }
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstFUngetC(this->fileline(), lhsp, rhsp);
    }
    virtual string emitVerilog() override { return "%f$ungetc(%r, %l)"; }
    // Non-existent filehandle returns EOF
    virtual string emitC() override {
        return "(%li ? (ungetc(%ri, VL_CVT_I_FP(%li)) >= 0 ? 0 : -1) : -1)";
    }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 64; }
    virtual bool isPure() const override {
        return false;
    }  // SPECIAL: $display has 'visual' ordering
    AstNode* filep() const { return lhsp(); }
    AstNode* charp() const { return rhsp(); }
};

class AstNodeSystemUniop VL_NOT_FINAL : public AstNodeUniop {
public:
    AstNodeSystemUniop(AstType t, FileLine* fl, AstNode* lhsp)
        : AstNodeUniop(t, fl, lhsp) {
        dtypeSetDouble();
    }
    ASTNODE_BASE_FUNCS(NodeSystemUniop)
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual int instrCount() const override { return instrCountDoubleTrig(); }
    virtual bool doubleFlavor() const override { return true; }
};

class AstLogD final : public AstNodeSystemUniop {
public:
    AstLogD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(LogD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::log(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$ln(%l)"; }
    virtual string emitC() override { return "log(%li)"; }
};
class AstLog10D final : public AstNodeSystemUniop {
public:
    AstLog10D(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(Log10D)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::log10(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$log10(%l)"; }
    virtual string emitC() override { return "log10(%li)"; }
};

class AstExpD final : public AstNodeSystemUniop {
public:
    AstExpD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(ExpD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::exp(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$exp(%l)"; }
    virtual string emitC() override { return "exp(%li)"; }
};

class AstSqrtD final : public AstNodeSystemUniop {
public:
    AstSqrtD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(SqrtD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::sqrt(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$sqrt(%l)"; }
    virtual string emitC() override { return "sqrt(%li)"; }
};

class AstFloorD final : public AstNodeSystemUniop {
public:
    AstFloorD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(FloorD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::floor(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$floor(%l)"; }
    virtual string emitC() override { return "floor(%li)"; }
};

class AstCeilD final : public AstNodeSystemUniop {
public:
    AstCeilD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(CeilD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::ceil(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$ceil(%l)"; }
    virtual string emitC() override { return "ceil(%li)"; }
};

class AstSinD final : public AstNodeSystemUniop {
public:
    AstSinD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(SinD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::sin(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$sin(%l)"; }
    virtual string emitC() override { return "sin(%li)"; }
};

class AstCosD final : public AstNodeSystemUniop {
public:
    AstCosD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(CosD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::cos(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$cos(%l)"; }
    virtual string emitC() override { return "cos(%li)"; }
};

class AstTanD final : public AstNodeSystemUniop {
public:
    AstTanD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(TanD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::tan(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$tan(%l)"; }
    virtual string emitC() override { return "tan(%li)"; }
};

class AstAsinD final : public AstNodeSystemUniop {
public:
    AstAsinD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(AsinD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::asin(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$asin(%l)"; }
    virtual string emitC() override { return "asin(%li)"; }
};

class AstAcosD final : public AstNodeSystemUniop {
public:
    AstAcosD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(AcosD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::acos(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$acos(%l)"; }
    virtual string emitC() override { return "acos(%li)"; }
};

class AstAtanD final : public AstNodeSystemUniop {
public:
    AstAtanD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(AtanD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::atan(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$atan(%l)"; }
    virtual string emitC() override { return "atan(%li)"; }
};

class AstSinhD final : public AstNodeSystemUniop {
public:
    AstSinhD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(SinhD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::sinh(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$sinh(%l)"; }
    virtual string emitC() override { return "sinh(%li)"; }
};

class AstCoshD final : public AstNodeSystemUniop {
public:
    AstCoshD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(CoshD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::cosh(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$cosh(%l)"; }
    virtual string emitC() override { return "cosh(%li)"; }
};

class AstTanhD final : public AstNodeSystemUniop {
public:
    AstTanhD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(TanhD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::tanh(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$tanh(%l)"; }
    virtual string emitC() override { return "tanh(%li)"; }
};

class AstAsinhD final : public AstNodeSystemUniop {
public:
    AstAsinhD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(AsinhD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::asinh(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$asinh(%l)"; }
    virtual string emitC() override { return "asinh(%li)"; }
};

class AstAcoshD final : public AstNodeSystemUniop {
public:
    AstAcoshD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(AcoshD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::acosh(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$acosh(%l)"; }
    virtual string emitC() override { return "acosh(%li)"; }
};

class AstAtanhD final : public AstNodeSystemUniop {
public:
    AstAtanhD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(AtanhD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::atanh(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$atanh(%l)"; }
    virtual string emitC() override { return "atanh(%li)"; }
};
class AstToLowerN final : public AstNodeUniop {
    // string.tolower()
public:
    AstToLowerN(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {
        dtypeSetString();
    }
    ASTNODE_NODE_FUNCS(ToLowerN)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.opToLowerN(lhs);
    }
    virtual string emitVerilog() override { return "%l.tolower()"; }
    virtual string emitC() override { return "VL_TOLOWER_NN(%li)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
};
class AstToUpperN final : public AstNodeUniop {
    // string.toupper()
public:
    AstToUpperN(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {
        dtypeSetString();
    }
    ASTNODE_NODE_FUNCS(ToUpperN)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.opToUpperN(lhs);
    }
    virtual string emitVerilog() override { return "%l.toupper()"; }
    virtual string emitC() override { return "VL_TOUPPER_NN(%li)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
};
class AstTimeImport final : public AstNodeUniop {
    // Take a constant that represents a time and needs conversion based on time units
    VTimescale m_timeunit;  // Parent module time unit
public:
    AstTimeImport(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(TimeImport)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { V3ERROR_NA; }
    virtual string emitVerilog() override { return "%l"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual void dump(std::ostream& str = std::cout) const override;
    void timeunit(const VTimescale& flag) { m_timeunit = flag; }
    VTimescale timeunit() const { return m_timeunit; }
};

class AstAtoN final : public AstNodeUniop {
    // string.atoi(), atobin(), atohex(), atooct(), atoireal()
public:
    enum FmtType { ATOI = 10, ATOHEX = 16, ATOOCT = 8, ATOBIN = 2, ATOREAL = -1 };

private:
    FmtType m_fmt;  // Operation type
public:
    AstAtoN(FileLine* fl, AstNode* lhsp, FmtType fmt)
        : ASTGEN_SUPER(fl, lhsp)
        , m_fmt{fmt} {
        fmt == ATOREAL ? dtypeSetDouble() : dtypeSetSigned32();
    }
    ASTNODE_NODE_FUNCS(AtoN)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.opAtoN(lhs, m_fmt);
    }
    virtual string name() const override {
        switch (m_fmt) {
        case ATOI: return "atoi";
        case ATOHEX: return "atohex";
        case ATOOCT: return "atooct";
        case ATOBIN: return "atobin";
        case ATOREAL: return "atoreal";
        default: V3ERROR_NA;
        }
    }
    virtual string emitVerilog() override { return "%l." + name() + "()"; }
    virtual string emitC() override {
        switch (m_fmt) {
        case ATOI: return "VL_ATOI_N(%li, 10)";
        case ATOHEX: return "VL_ATOI_N(%li, 16)";
        case ATOOCT: return "VL_ATOI_N(%li, 8)";
        case ATOBIN: return "VL_ATOI_N(%li, 2)";
        case ATOREAL: return "std::atof(%li.c_str())";
        default: V3ERROR_NA;
        }
    }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool isHeavy() const override { return true; }
    FmtType format() const { return m_fmt; }
};

//======================================================================
// Binary ops

class AstLogOr final : public AstNodeBiop {
public:
    AstLogOr(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(LogOr)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstLogOr(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLogOr(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f|| %r)"; }
    virtual string emitC() override { return "VL_LOGOR_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "||"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() + instrCountBranch(); }
};
class AstLogAnd final : public AstNodeBiop {
public:
    AstLogAnd(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(LogAnd)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstLogAnd(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLogAnd(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f&& %r)"; }
    virtual string emitC() override { return "VL_LOGAND_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "&&"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() + instrCountBranch(); }
};
class AstLogEq final : public AstNodeBiCom {
public:
    AstLogEq(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(LogEq)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstLogEq(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLogEq(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f<-> %r)"; }
    virtual string emitC() override { return "VL_LOGEQ_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "<->"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() + instrCountBranch(); }
};
class AstLogIf final : public AstNodeBiop {
public:
    AstLogIf(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(LogIf)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstLogIf(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLogIf(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f-> %r)"; }
    virtual string emitC() override { return "VL_LOGIF_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "->"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() + instrCountBranch(); }
};
class AstOr final : public AstNodeBiComAsv {
public:
    AstOr(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(Or)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstOr(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opOr(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f| %r)"; }
    virtual string emitC() override { return "VL_OR_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "|"; }
    virtual bool cleanOut() const override { V3ERROR_NA_RETURN(false); }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstAnd final : public AstNodeBiComAsv {
public:
    AstAnd(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(And)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstAnd(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opAnd(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f& %r)"; }
    virtual string emitC() override { return "VL_AND_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "&"; }
    virtual bool cleanOut() const override { V3ERROR_NA_RETURN(false); }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstXor final : public AstNodeBiComAsv {
public:
    AstXor(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(Xor)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstXor(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opXor(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f^ %r)"; }
    virtual string emitC() override { return "VL_XOR_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "^"; }
    virtual bool cleanOut() const override { return false; }  // Lclean && Rclean
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstEq final : public AstNodeBiCom {
public:
    AstEq(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(Eq)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstEq(this->fileline(), lhsp, rhsp);
    }
    static AstNodeBiop* newTyped(FileLine* fl, AstNode* lhsp,
                                 AstNode* rhsp);  // Return AstEq/AstEqD
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opEq(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f== %r)"; }
    virtual string emitC() override { return "VL_EQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "=="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstEqD final : public AstNodeBiCom {
public:
    AstEqD(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(EqD)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstEqD(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opEqD(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f== %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return "=="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return instrCountDouble(); }
    virtual bool doubleFlavor() const override { return true; }
};
class AstEqN final : public AstNodeBiCom {
public:
    AstEqN(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(EqN)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstEqN(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opEqN(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f== %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return "=="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return instrCountString(); }
    virtual bool stringFlavor() const override { return true; }
};
class AstNeq final : public AstNodeBiCom {
public:
    AstNeq(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(Neq)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstNeq(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opNeq(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f!= %r)"; }
    virtual string emitC() override { return "VL_NEQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "!="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstNeqD final : public AstNodeBiCom {
public:
    AstNeqD(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(NeqD)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstNeqD(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opNeqD(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f!= %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return "!="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return instrCountDouble(); }
    virtual bool doubleFlavor() const override { return true; }
};
class AstNeqN final : public AstNodeBiCom {
public:
    AstNeqN(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(NeqN)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstNeqN(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opNeqN(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f!= %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return "!="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return instrCountString(); }
    virtual bool stringFlavor() const override { return true; }
};
class AstLt final : public AstNodeBiop {
public:
    AstLt(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(Lt)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstLt(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLt(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f< %r)"; }
    virtual string emitC() override { return "VL_LT_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "<"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstLtD final : public AstNodeBiop {
public:
    AstLtD(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(LtD)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstLtD(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLtD(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f< %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return "<"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return instrCountDouble(); }
    virtual bool doubleFlavor() const override { return true; }
};
class AstLtS final : public AstNodeBiop {
public:
    AstLtS(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(LtS)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstLtS(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLtS(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f< %r)"; }
    virtual string emitC() override { return "VL_LTS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return ""; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool signedFlavor() const override { return true; }
};
class AstLtN final : public AstNodeBiop {
public:
    AstLtN(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(LtN)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstLtN(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLtN(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f< %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return "<"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return instrCountString(); }
    virtual bool stringFlavor() const override { return true; }
};
class AstGt final : public AstNodeBiop {
public:
    AstGt(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(Gt)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstGt(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opGt(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f> %r)"; }
    virtual string emitC() override { return "VL_GT_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return ">"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstGtD final : public AstNodeBiop {
public:
    AstGtD(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(GtD)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstGtD(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opGtD(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f> %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return ">"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return instrCountDouble(); }
    virtual bool doubleFlavor() const override { return true; }
};
class AstGtS final : public AstNodeBiop {
public:
    AstGtS(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(GtS)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstGtS(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opGtS(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f> %r)"; }
    virtual string emitC() override { return "VL_GTS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return ""; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool signedFlavor() const override { return true; }
};
class AstGtN final : public AstNodeBiop {
public:
    AstGtN(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(GtN)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstGtN(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opGtN(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f> %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return ">"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return instrCountString(); }
    virtual bool stringFlavor() const override { return true; }
};
class AstGte final : public AstNodeBiop {
public:
    AstGte(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(Gte)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstGte(this->fileline(), lhsp, rhsp);
    }
    static AstNodeBiop* newTyped(FileLine* fl, AstNode* lhsp,
                                 AstNode* rhsp);  // Return AstGte/AstGteS/AstGteD
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opGte(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f>= %r)"; }
    virtual string emitC() override { return "VL_GTE_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return ">="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstGteD final : public AstNodeBiop {
public:
    AstGteD(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(GteD)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstGteD(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opGteD(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f>= %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return ">="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return instrCountDouble(); }
    virtual bool doubleFlavor() const override { return true; }
};
class AstGteS final : public AstNodeBiop {
public:
    AstGteS(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(GteS)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstGteS(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opGteS(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f>= %r)"; }
    virtual string emitC() override { return "VL_GTES_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return ""; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool signedFlavor() const override { return true; }
};
class AstGteN final : public AstNodeBiop {
public:
    AstGteN(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(GteN)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstGteN(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opGteN(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f>= %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return ">="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return instrCountString(); }
    virtual bool stringFlavor() const override { return true; }
};
class AstLte final : public AstNodeBiop {
public:
    AstLte(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(Lte)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstLte(this->fileline(), lhsp, rhsp);
    }
    static AstNodeBiop* newTyped(FileLine* fl, AstNode* lhsp,
                                 AstNode* rhsp);  // Return AstLte/AstLteS/AstLteD
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLte(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f<= %r)"; }
    virtual string emitC() override { return "VL_LTE_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "<="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstLteD final : public AstNodeBiop {
public:
    AstLteD(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(LteD)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstLteD(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLteD(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f<= %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return "<="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return instrCountDouble(); }
    virtual bool doubleFlavor() const override { return true; }
};
class AstLteS final : public AstNodeBiop {
public:
    AstLteS(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(LteS)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstLteS(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLteS(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f<= %r)"; }
    virtual string emitC() override { return "VL_LTES_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return ""; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool signedFlavor() const override { return true; }
};
class AstLteN final : public AstNodeBiop {
public:
    AstLteN(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(LteN)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstLteN(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLteN(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f<= %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return "<="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return instrCountString(); }
    virtual bool stringFlavor() const override { return true; }
};
class AstShiftL final : public AstNodeBiop {
public:
    AstShiftL(FileLine* fl, AstNode* lhsp, AstNode* rhsp, int setwidth = 0)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        if (setwidth) dtypeSetLogicSized(setwidth, VSigning::UNSIGNED);
    }
    ASTNODE_NODE_FUNCS(ShiftL)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstShiftL(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opShiftL(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f<< %r)"; }
    virtual string emitC() override { return "VL_SHIFTL_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override {
        return (rhsp()->isWide() || rhsp()->isQuad()) ? "" : "<<";
    }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstShiftR final : public AstNodeBiop {
public:
    AstShiftR(FileLine* fl, AstNode* lhsp, AstNode* rhsp, int setwidth = 0)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        if (setwidth) dtypeSetLogicSized(setwidth, VSigning::UNSIGNED);
    }
    ASTNODE_NODE_FUNCS(ShiftR)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstShiftR(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opShiftR(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f>> %r)"; }
    virtual string emitC() override { return "VL_SHIFTR_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override {
        return (rhsp()->isWide() || rhsp()->isQuad()) ? "" : ">>";
    }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    // LHS size might be > output size, so don't want to force size
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstShiftRS final : public AstNodeBiop {
    // Shift right with sign extension, >>> operator
    // Output data type's width determines which bit is used for sign extension
public:
    AstShiftRS(FileLine* fl, AstNode* lhsp, AstNode* rhsp, int setwidth = 0)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        // Important that widthMin be correct, as opExtend requires it after V3Expand
        if (setwidth) dtypeSetLogicSized(setwidth, VSigning::SIGNED);
    }
    ASTNODE_NODE_FUNCS(ShiftRS)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstShiftRS(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opShiftRS(lhs, rhs, lhsp()->widthMinV());
    }
    virtual string emitVerilog() override { return "%k(%l %f>>> %r)"; }
    virtual string emitC() override { return "VL_SHIFTRS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return ""; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool signedFlavor() const override { return true; }
};
class AstAdd final : public AstNodeBiComAsv {
public:
    AstAdd(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(Add)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstAdd(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opAdd(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f+ %r)"; }
    virtual string emitC() override { return "VL_ADD_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "+"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return true; }
};
class AstAddD final : public AstNodeBiComAsv {
public:
    AstAddD(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetDouble();
    }
    ASTNODE_NODE_FUNCS(AddD)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstAddD(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opAddD(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f+ %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return "+"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return instrCountDouble(); }
    virtual bool doubleFlavor() const override { return true; }
};
class AstSub final : public AstNodeBiop {
public:
    AstSub(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(Sub)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstSub(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opSub(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f- %r)"; }
    virtual string emitC() override { return "VL_SUB_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "-"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return true; }
};
class AstSubD final : public AstNodeBiop {
public:
    AstSubD(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetDouble();
    }
    ASTNODE_NODE_FUNCS(SubD)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstSubD(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opSubD(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f- %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return "-"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return instrCountDouble(); }
    virtual bool doubleFlavor() const override { return true; }
};
class AstMul final : public AstNodeBiComAsv {
public:
    AstMul(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(Mul)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstMul(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opMul(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f* %r)"; }
    virtual string emitC() override { return "VL_MUL_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "*"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return true; }
    virtual int instrCount() const override { return widthInstrs() * instrCountMul(); }
};
class AstMulD final : public AstNodeBiComAsv {
public:
    AstMulD(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetDouble();
    }
    ASTNODE_NODE_FUNCS(MulD)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstMulD(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opMulD(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f* %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return "*"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return true; }
    virtual int instrCount() const override { return instrCountDouble(); }
    virtual bool doubleFlavor() const override { return true; }
};
class AstMulS final : public AstNodeBiComAsv {
public:
    AstMulS(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(MulS)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstMulS(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opMulS(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f* %r)"; }
    virtual string emitC() override { return "VL_MULS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return ""; }
    virtual bool emitCheckMaxWords() override { return true; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return true; }
    virtual int instrCount() const override { return widthInstrs() * instrCountMul(); }
    virtual bool signedFlavor() const override { return true; }
};
class AstDiv final : public AstNodeBiop {
public:
    AstDiv(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(Div)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstDiv(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opDiv(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f/ %r)"; }
    virtual string emitC() override { return "VL_DIV_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return true; }
    virtual int instrCount() const override { return widthInstrs() * instrCountDiv(); }
};
class AstDivD final : public AstNodeBiop {
public:
    AstDivD(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetDouble();
    }
    ASTNODE_NODE_FUNCS(DivD)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstDivD(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opDivD(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f/ %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return "/"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return instrCountDoubleDiv(); }
    virtual bool doubleFlavor() const override { return true; }
};
class AstDivS final : public AstNodeBiop {
public:
    AstDivS(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(DivS)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstDivS(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opDivS(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f/ %r)"; }
    virtual string emitC() override { return "VL_DIVS_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return true; }
    virtual int instrCount() const override { return widthInstrs() * instrCountDiv(); }
    virtual bool signedFlavor() const override { return true; }
};
class AstModDiv final : public AstNodeBiop {
public:
    AstModDiv(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(ModDiv)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstModDiv(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opModDiv(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f%% %r)"; }
    virtual string emitC() override { return "VL_MODDIV_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return true; }
    virtual int instrCount() const override { return widthInstrs() * instrCountDiv(); }
};
class AstModDivS final : public AstNodeBiop {
public:
    AstModDivS(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(ModDivS)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstModDivS(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opModDivS(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f%% %r)"; }
    virtual string emitC() override { return "VL_MODDIVS_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return true; }
    virtual int instrCount() const override { return widthInstrs() * instrCountDiv(); }
    virtual bool signedFlavor() const override { return true; }
};
class AstPow final : public AstNodeBiop {
public:
    AstPow(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(Pow)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstPow(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opPow(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f** %r)"; }
    virtual string emitC() override { return "VL_POW_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual bool emitCheckMaxWords() override { return true; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * instrCountMul() * 10; }
};
class AstPowD final : public AstNodeBiop {
public:
    AstPowD(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetDouble();
    }
    ASTNODE_NODE_FUNCS(PowD)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstPowD(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opPowD(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f** %r)"; }
    virtual string emitC() override { return "pow(%li,%ri)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return instrCountDoubleDiv() * 5; }
    virtual bool doubleFlavor() const override { return true; }
};
class AstPowSU final : public AstNodeBiop {
public:
    AstPowSU(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(PowSU)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstPowSU(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opPowSU(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f** %r)"; }
    virtual string emitC() override {
        return "VL_POWSS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri, 1,0)";
    }
    virtual bool emitCheckMaxWords() override { return true; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * instrCountMul() * 10; }
    virtual bool signedFlavor() const override { return true; }
};
class AstPowSS final : public AstNodeBiop {
public:
    AstPowSS(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(PowSS)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstPowSS(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opPowSS(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f** %r)"; }
    virtual string emitC() override {
        return "VL_POWSS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri, 1,1)";
    }
    virtual bool emitCheckMaxWords() override { return true; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * instrCountMul() * 10; }
    virtual bool signedFlavor() const override { return true; }
};
class AstPowUS final : public AstNodeBiop {
public:
    AstPowUS(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(PowUS)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstPowUS(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opPowUS(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f** %r)"; }
    virtual string emitC() override {
        return "VL_POWSS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri, 0,1)";
    }
    virtual bool emitCheckMaxWords() override { return true; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * instrCountMul() * 10; }
    virtual bool signedFlavor() const override { return true; }
};
class AstPreAdd final : public AstNodeTriop {
    // Pre-increment/add
    // Parents:  MATH
    // Children: lhsp: AstConst (1) as currently support only ++ not +=
    // Children: rhsp: tree with AstVarRef that is value to read before operation
    // Children: thsp: tree with AstVarRef LValue that is stored after operation
public:
    AstPreAdd(FileLine* fl, AstNode* lhsp, AstNode* rhsp, AstNode* thsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp, thsp) {}
    ASTNODE_NODE_FUNCS(PreAdd)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs,
                               const V3Number& ths) override {
        V3ERROR_NA;  // Need to modify lhs
    }
    virtual string emitVerilog() override { return "%k(++%r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool cleanThs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return true; }
    virtual bool sizeMattersThs() const override { return true; }
};
class AstPreSub final : public AstNodeTriop {
    // Pre-decrement/subtract
    // Parents:  MATH
    // Children: lhsp: AstConst (1) as currently support only -- not -=
    // Children: rhsp: tree with AstVarRef that is value to read before operation
    // Children: thsp: tree with AstVarRef LValue that is stored after operation
public:
    AstPreSub(FileLine* fl, AstNode* lhsp, AstNode* rhsp, AstNode* thsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp, thsp) {}
    ASTNODE_NODE_FUNCS(PreSub)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs,
                               const V3Number& ths) override {
        V3ERROR_NA;  // Need to modify lhs
    }
    virtual string emitVerilog() override { return "%k(--%r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool cleanThs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return true; }
    virtual bool sizeMattersThs() const override { return true; }
};
class AstPostAdd final : public AstNodeTriop {
    // Post-increment/add
    // Parents:  MATH
    // Children: lhsp: AstConst (1) as currently support only ++ not +=
    // Children: rhsp: tree with AstVarRef that is value to read before operation
    // Children: thsp: tree with AstVarRef LValue that is stored after operation
public:
    AstPostAdd(FileLine* fl, AstNode* lhsp, AstNode* rhsp, AstNode* thsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp, thsp) {}
    ASTNODE_NODE_FUNCS(PostAdd)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs,
                               const V3Number& ths) override {
        V3ERROR_NA;  // Need to modify lhs
    }
    virtual string emitVerilog() override { return "%k(%r++)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool cleanThs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return true; }
    virtual bool sizeMattersThs() const override { return true; }
};
class AstPostSub final : public AstNodeTriop {
    // Post-decrement/subtract
    // Parents:  MATH
    // Children: lhsp: AstConst (1) as currently support only -- not -=
    // Children: rhsp: tree with AstVarRef that is value to read before operation
    // Children: thsp: tree with AstVarRef LValue that is stored after operation
public:
    AstPostSub(FileLine* fl, AstNode* lhsp, AstNode* rhsp, AstNode* thsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp, thsp) {}
    ASTNODE_NODE_FUNCS(PostSub)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs,
                               const V3Number& ths) override {
        V3ERROR_NA;  // Need to modify lhs
    }
    virtual string emitVerilog() override { return "%k(%r--)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool cleanThs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return true; }
    virtual bool sizeMattersThs() const override { return true; }
};
class AstEqCase final : public AstNodeBiCom {
public:
    AstEqCase(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(EqCase)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstEqCase(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opCaseEq(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f=== %r)"; }
    virtual string emitC() override { return "VL_EQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "=="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstNeqCase final : public AstNodeBiCom {
public:
    AstNeqCase(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(NeqCase)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstNeqCase(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opCaseNeq(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f!== %r)"; }
    virtual string emitC() override { return "VL_NEQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "!="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstEqWild final : public AstNodeBiop {
    // Note wildcard operator rhs differs from lhs
public:
    AstEqWild(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(EqWild)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstEqWild(this->fileline(), lhsp, rhsp);
    }
    static AstNodeBiop* newTyped(FileLine* fl, AstNode* lhsp,
                                 AstNode* rhsp);  // Return AstEqWild/AstEqD
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opWildEq(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f==? %r)"; }
    virtual string emitC() override { return "VL_EQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "=="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstNeqWild final : public AstNodeBiop {
public:
    AstNeqWild(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(NeqWild)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstNeqWild(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opWildNeq(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f!=? %r)"; }
    virtual string emitC() override { return "VL_NEQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "!="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstConcat final : public AstNodeBiop {
    // If you're looking for {#{}}, see AstReplicate
public:
    AstConcat(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        if (lhsp->dtypep() && rhsp->dtypep()) {
            dtypeSetLogicSized(lhsp->dtypep()->width() + rhsp->dtypep()->width(),
                               VSigning::UNSIGNED);
        }
    }
    ASTNODE_NODE_FUNCS(Concat)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstConcat(this->fileline(), lhsp, rhsp);
    }
    virtual string emitVerilog() override { return "%f{%l, %k%r}"; }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opConcat(lhs, rhs);
    }
    virtual string emitC() override { return "VL_CONCAT_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 2; }
};
class AstConcatN final : public AstNodeBiop {
    // String concatenate
public:
    AstConcatN(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetString();
    }
    ASTNODE_NODE_FUNCS(ConcatN)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstConcatN(this->fileline(), lhsp, rhsp);
    }
    virtual string emitVerilog() override { return "%f{%l, %k%r}"; }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opConcatN(lhs, rhs);
    }
    virtual string emitC() override { return "VL_CONCATN_NNN(%li, %ri)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return instrCountString(); }
    virtual bool stringFlavor() const override { return true; }
};
class AstReplicate final : public AstNodeBiop {
    // Also used as a "Uniop" flavor of Concat, e.g. "{a}"
    // Verilog {rhs{lhs}} - Note rhsp() is the replicate value, not the lhsp()
public:
    AstReplicate(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        if (lhsp) {
            if (const AstConst* constp = VN_CAST(rhsp, Const)) {
                dtypeSetLogicSized(lhsp->width() * constp->toUInt(), VSigning::UNSIGNED);
            }
        }
    }
    AstReplicate(FileLine* fl, AstNode* lhsp, uint32_t repCount)
        : AstReplicate(fl, lhsp, new AstConst(fl, repCount)) {}
    ASTNODE_NODE_FUNCS(Replicate)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstReplicate(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opRepl(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%f{%r{%k%l}}"; }
    virtual string emitC() override { return "VL_REPLICATE_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 2; }
};
class AstReplicateN final : public AstNodeBiop {
    // String replicate
public:
    AstReplicateN(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetString();
    }
    AstReplicateN(FileLine* fl, AstNode* lhsp, uint32_t repCount)
        : AstReplicateN(fl, lhsp, new AstConst(fl, repCount)) {}
    ASTNODE_NODE_FUNCS(ReplicateN)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstReplicateN(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opReplN(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%f{%r{%k%l}}"; }
    virtual string emitC() override { return "VL_REPLICATEN_NN%rq(0,0,%rw, %li, %ri)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 2; }
    virtual bool stringFlavor() const override { return true; }
};
class AstStreamL final : public AstNodeStream {
    // Verilog {rhs{lhs}} - Note rhsp() is the slice size, not the lhsp()
public:
    AstStreamL(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(StreamL)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstStreamL(this->fileline(), lhsp, rhsp);
    }
    virtual string emitVerilog() override { return "%f{ << %r %k{%l} }"; }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opStreamL(lhs, rhs);
    }
    virtual string emitC() override { return "VL_STREAML_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 2; }
};
class AstStreamR final : public AstNodeStream {
    // Verilog {rhs{lhs}} - Note rhsp() is the slice size, not the lhsp()
public:
    AstStreamR(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(StreamR)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstStreamR(this->fileline(), lhsp, rhsp);
    }
    virtual string emitVerilog() override { return "%f{ >> %r %k{%l} }"; }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opAssign(lhs);
    }
    virtual string emitC() override { return isWide() ? "VL_ASSIGN_W(%nw, %P, %li)" : "%li"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 2; }
};
class AstBufIf1 final : public AstNodeBiop {
    // lhs is enable, rhs is data to drive
    // Note unlike the Verilog bufif1() UDP, this allows any width; each lhsp
    // bit enables respective rhsp bit
public:
    AstBufIf1(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(BufIf1)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstBufIf1(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opBufIf1(lhs, rhs);
    }
    virtual string emitVerilog() override { return "bufif(%r,%l)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }  // Lclean || Rclean
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }  // Lclean || Rclean
    virtual bool cleanOut() const override { V3ERROR_NA_RETURN(""); }  // Lclean || Rclean
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstFGetS final : public AstNodeBiop {
public:
    AstFGetS(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(FGetS)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstFGetS(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        V3ERROR_NA;
    }
    virtual string emitVerilog() override { return "%f$fgets(%l,%r)"; }
    virtual string emitC() override {
        return strgp()->dtypep()->basicp()->isString() ? "VL_FGETS_NI(%li, %ri)"
                                                       : "VL_FGETS_%nqX%rq(%lw, %P, &(%li), %ri)";
    }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 64; }
    AstNode* strgp() const { return lhsp(); }
    AstNode* filep() const { return rhsp(); }
};

class AstNodeSystemBiop VL_NOT_FINAL : public AstNodeBiop {
public:
    AstNodeSystemBiop(AstType t, FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : AstNodeBiop(t, fl, lhsp, rhsp) {
        dtypeSetDouble();
    }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return instrCountDoubleTrig(); }
    virtual bool doubleFlavor() const override { return true; }
};

class AstAtan2D final : public AstNodeSystemBiop {
public:
    AstAtan2D(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(Atan2D)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstAtan2D(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.setDouble(std::atan2(lhs.toDouble(), rhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$atan2(%l,%r)"; }
    virtual string emitC() override { return "atan2(%li,%ri)"; }
};

class AstHypotD final : public AstNodeSystemBiop {
public:
    AstHypotD(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(HypotD)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstHypotD(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.setDouble(std::hypot(lhs.toDouble(), rhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$hypot(%l,%r)"; }
    virtual string emitC() override { return "hypot(%li,%ri)"; }
};

class AstPutcN final : public AstNodeTriop {
    // Verilog string.putc()
public:
    AstPutcN(FileLine* fl, AstNode* lhsp, AstNode* rhsp, AstNode* ths)
        : ASTGEN_SUPER(fl, lhsp, rhsp, ths) {
        dtypeSetString();
    }
    ASTNODE_NODE_FUNCS(PutcN)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs,
                               const V3Number& ths) override {
        out.opPutcN(lhs, rhs, ths);
    }
    virtual string name() const override { return "putc"; }
    virtual string emitVerilog() override { return "%k(%l.putc(%r,%t))"; }
    virtual string emitC() override { return "VL_PUTC_N(%li,%ri,%ti)"; }
    virtual string emitSimpleOperator() override { return ""; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool cleanThs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool sizeMattersThs() const override { return false; }
    virtual bool isHeavy() const override { return true; }
};

class AstGetcN final : public AstNodeBiop {
    // Verilog string.getc()
public:
    AstGetcN(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBitSized(8, VSigning::UNSIGNED);
    }
    ASTNODE_NODE_FUNCS(GetcN)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstGetcN(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opGetcN(lhs, rhs);
    }
    virtual string name() const override { return "getc"; }
    virtual string emitVerilog() override { return "%k(%l.getc(%r))"; }
    virtual string emitC() override { return "VL_GETC_N(%li,%ri)"; }
    virtual string emitSimpleOperator() override { return ""; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool isHeavy() const override { return true; }
};

class AstGetcRefN final : public AstNodeBiop {
    // Verilog string[#] on the left-hand-side of assignment
    // Spec says is of type byte (not string of single character)
public:
    AstGetcRefN(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER(fl, lhsp, rhsp) {
        dtypeSetBitSized(8, VSigning::UNSIGNED);
    }
    ASTNODE_NODE_FUNCS(GetcRefN)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstGetcRefN(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        V3ERROR_NA;
    }
    virtual string emitVerilog() override { return "%k%l[%r]"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return ""; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool isHeavy() const override { return true; }
};

class AstSubstrN final : public AstNodeTriop {
    // Verilog string.substr()
public:
    AstSubstrN(FileLine* fl, AstNode* lhsp, AstNode* rhsp, AstNode* ths)
        : ASTGEN_SUPER(fl, lhsp, rhsp, ths) {
        dtypeSetString();
    }
    ASTNODE_NODE_FUNCS(SubstrN)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs,
                               const V3Number& ths) override {
        out.opSubstrN(lhs, rhs, ths);
    }
    virtual string name() const override { return "substr"; }
    virtual string emitVerilog() override { return "%k(%l.substr(%r,%t))"; }
    virtual string emitC() override { return "VL_SUBSTR_N(%li,%ri,%ti)"; }
    virtual string emitSimpleOperator() override { return ""; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool cleanThs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool sizeMattersThs() const override { return false; }
    virtual bool isHeavy() const override { return true; }
};

class AstCompareNN final : public AstNodeBiop {
    // Verilog str.compare() and str.icompare()
private:
    bool m_ignoreCase;  // True for str.icompare()
public:
    AstCompareNN(FileLine* fl, AstNode* lhsp, AstNode* rhsp, bool ignoreCase)
        : ASTGEN_SUPER(fl, lhsp, rhsp)
        , m_ignoreCase{ignoreCase} {
        dtypeSetUInt32();
    }
    ASTNODE_NODE_FUNCS(CompareNN)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstCompareNN(this->fileline(), lhsp, rhsp, m_ignoreCase);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opCompareNN(lhs, rhs, m_ignoreCase);
    }
    virtual string name() const override { return m_ignoreCase ? "icompare" : "compare"; }
    virtual string emitVerilog() override {
        return m_ignoreCase ? "%k(%l.icompare(%r))" : "%k(%l.compare(%r))";
    }
    virtual string emitC() override {
        return m_ignoreCase ? "VL_CMP_NN(%li,%ri,true)" : "VL_CMP_NN(%li,%ri,false)";
    }
    virtual string emitSimpleOperator() override { return ""; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool isHeavy() const override { return true; }
};

class AstFell final : public AstNodeMath {
    // Verilog $fell
    // Parents: math
    // Children: expression
public:
    AstFell(FileLine* fl, AstNode* exprp)
        : ASTGEN_SUPER(fl) {
        addOp1p(exprp);
    }
    ASTNODE_NODE_FUNCS(Fell)
    virtual string emitVerilog() override { return "$fell(%l)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { V3ERROR_NA_RETURN(""); }
    virtual int instrCount() const override { return widthInstrs(); }
    AstNode* exprp() const { return op1p(); }  // op1 = expression
    AstSenTree* sentreep() const { return VN_CAST(op2p(), SenTree); }  // op2 = clock domain
    void sentreep(AstSenTree* sentreep) { addOp2p(sentreep); }  // op2 = clock domain
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
};

class AstPast final : public AstNodeMath {
    // Verilog $past
    // Parents: math
    // Children: expression
public:
    AstPast(FileLine* fl, AstNode* exprp, AstNode* ticksp)
        : ASTGEN_SUPER(fl) {
        addOp1p(exprp);
        addNOp2p(ticksp);
    }
    ASTNODE_NODE_FUNCS(Past)
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { V3ERROR_NA_RETURN(""); }
    virtual int instrCount() const override { return widthInstrs(); }
    AstNode* exprp() const { return op1p(); }  // op1 = expression
    AstNode* ticksp() const { return op2p(); }  // op2 = ticks or nullptr means 1
    AstSenTree* sentreep() const { return VN_CAST(op4p(), SenTree); }  // op4 = clock domain
    void sentreep(AstSenTree* sentreep) { addOp4p(sentreep); }  // op4 = clock domain
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
};

class AstRose final : public AstNodeMath {
    // Verilog $rose
    // Parents: math
    // Children: expression
public:
    AstRose(FileLine* fl, AstNode* exprp)
        : ASTGEN_SUPER(fl) {
        addOp1p(exprp);
    }
    ASTNODE_NODE_FUNCS(Rose)
    virtual string emitVerilog() override { return "$rose(%l)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { V3ERROR_NA_RETURN(""); }
    virtual int instrCount() const override { return widthInstrs(); }
    AstNode* exprp() const { return op1p(); }  // op1 = expression
    AstSenTree* sentreep() const { return VN_CAST(op2p(), SenTree); }  // op2 = clock domain
    void sentreep(AstSenTree* sentreep) { addOp2p(sentreep); }  // op2 = clock domain
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
};

class AstSampled final : public AstNodeMath {
    // Verilog $sampled
    // Parents: math
    // Children: expression
public:
    AstSampled(FileLine* fl, AstNode* exprp)
        : ASTGEN_SUPER(fl) {
        addOp1p(exprp);
    }
    ASTNODE_NODE_FUNCS(Sampled)
    virtual string emitVerilog() override { return "$sampled(%l)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { V3ERROR_NA_RETURN(""); }
    virtual int instrCount() const override { return 0; }
    AstNode* exprp() const { return op1p(); }  // op1 = expression
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
};

class AstStable final : public AstNodeMath {
    // Verilog $stable
    // Parents: math
    // Children: expression
public:
    AstStable(FileLine* fl, AstNode* exprp)
        : ASTGEN_SUPER(fl) {
        addOp1p(exprp);
    }
    ASTNODE_NODE_FUNCS(Stable)
    virtual string emitVerilog() override { return "$stable(%l)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { V3ERROR_NA_RETURN(""); }
    virtual int instrCount() const override { return widthInstrs(); }
    AstNode* exprp() const { return op1p(); }  // op1 = expression
    AstSenTree* sentreep() const { return VN_CAST(op2p(), SenTree); }  // op2 = clock domain
    void sentreep(AstSenTree* sentreep) { addOp2p(sentreep); }  // op2 = clock domain
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
};

class AstPattern final : public AstNodeMath {
    // Verilog '{a,b,c,d...}
    // Parents: AstNodeAssign, AstPattern, ...
    // Children: expression, AstPattern, AstPatReplicate
public:
    AstPattern(FileLine* fl, AstNode* itemsp)
        : ASTGEN_SUPER(fl) {
        addNOp2p(itemsp);
    }
    ASTNODE_NODE_FUNCS(Pattern)
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { V3ERROR_NA_RETURN(""); }
    virtual int instrCount() const override { return widthInstrs(); }
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    virtual AstNodeDType* subDTypep() const { return dtypep() ? dtypep() : childDTypep(); }
    // op1 = Type assigning to
    AstNodeDType* childDTypep() const { return VN_CAST(op1p(), NodeDType); }
    void childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    AstNode* itemsp() const { return op2p(); }  // op2 = AstPatReplicate, AstPatMember, etc
};
class AstPatMember final : public AstNodeMath {
    // Verilog '{a} or '{a{b}}
    // Parents: AstPattern
    // Children: expression, AstPattern, replication count
private:
    bool m_default = false;

public:
    AstPatMember(FileLine* fl, AstNode* lhsp, AstNode* keyp, AstNode* repp)
        : ASTGEN_SUPER(fl) {
        addOp1p(lhsp), setNOp2p(keyp), setNOp3p(repp);
    }
    ASTNODE_NODE_FUNCS(PatMember)
    virtual string emitVerilog() override { return lhssp() ? "%f{%r{%k%l}}" : "%l"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { V3ERROR_NA_RETURN(""); }
    virtual int instrCount() const override { return widthInstrs() * 2; }
    virtual void dump(std::ostream& str = std::cout) const override;
    // op1 = expression to assign or another AstPattern (list if replicated)
    AstNode* lhssp() const { return op1p(); }
    AstNode* keyp() const { return op2p(); }  // op2 = assignment key (Const, id Text)
    AstNode* repp() const { return op3p(); }  // op3 = replication count, or nullptr for count 1
    bool isDefault() const { return m_default; }
    void isDefault(bool flag) { m_default = flag; }
};

class AstImplication final : public AstNodeMath {
    // Verilog |-> |=>
    // Parents: math
    // Children: expression
public:
    AstImplication(FileLine* fl, AstNode* lhs, AstNode* rhs)
        : ASTGEN_SUPER(fl) {
        setOp1p(lhs);
        setOp2p(rhs);
    }
    ASTNODE_NODE_FUNCS(Implication)
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { V3ERROR_NA_RETURN(""); }
    virtual int instrCount() const override { return widthInstrs(); }
    AstNode* lhsp() const { return op1p(); }
    AstNode* rhsp() const { return op2p(); }
    void lhsp(AstNode* nodep) { return setOp1p(nodep); }
    void rhsp(AstNode* nodep) { return setOp2p(nodep); }
    AstSenTree* sentreep() const { return VN_CAST(op4p(), SenTree); }  // op4 = clock domain
    void sentreep(AstSenTree* sentreep) { addOp4p(sentreep); }  // op4 = clock domain
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
};

//======================================================================
// Assertions

class AstClocking final : public AstNode {
    // Set default clock region
    // Parents:  MODULE
    // Children: Assertions
public:
    AstClocking(FileLine* fl, AstSenItem* sensesp, AstNode* bodysp)
        : ASTGEN_SUPER(fl) {
        addOp1p(sensesp);
        addNOp2p(bodysp);
    }
    ASTNODE_NODE_FUNCS(Clocking)
    // op1 = Sensitivity list
    AstSenItem* sensesp() const { return VN_CAST(op1p(), SenItem); }
    AstNode* bodysp() const { return op2p(); }  // op2 = Body
};

//======================================================================
// PSL

class AstPropClocked final : public AstNode {
    // A clocked property
    // Parents:  ASSERT|COVER (property)
    // Children: SENITEM, Properties
public:
    AstPropClocked(FileLine* fl, AstSenItem* sensesp, AstNode* disablep, AstNode* propp)
        : ASTGEN_SUPER(fl) {
        addNOp1p(sensesp);
        addNOp2p(disablep);
        addOp3p(propp);
    }
    ASTNODE_NODE_FUNCS(PropClocked)
    virtual bool hasDType() const override {
        return true;
    }  // Used under Cover, which expects a bool child
    AstSenItem* sensesp() const { return VN_CAST(op1p(), SenItem); }  // op1 = Sensitivity list
    AstNode* disablep() const { return op2p(); }  // op2 = disable
    AstNode* propp() const { return op3p(); }  // op3 = property
};

class AstNodeCoverOrAssert VL_NOT_FINAL : public AstNodeStmt {
    // Cover or Assert
    // Parents:  {statement list}
    // Children: expression, report string
private:
    bool m_immediate;  // Immediate assertion/cover
    string m_name;  // Name to report
public:
    AstNodeCoverOrAssert(AstType t, FileLine* fl, AstNode* propp, AstNode* passsp, bool immediate,
                         const string& name = "")
        : AstNodeStmt(t, fl)
        , m_immediate(immediate)
        , m_name(name) {
        addOp1p(propp);
        addNOp4p(passsp);
    }
    ASTNODE_BASE_FUNCS(NodeCoverOrAssert)
    virtual string name() const override { return m_name; }  // * = Var name
    virtual V3Hash sameHash() const override { return V3Hash(name()); }
    virtual bool same(const AstNode* samep) const override { return samep->name() == name(); }
    virtual void name(const string& name) override { m_name = name; }
    virtual void dump(std::ostream& str = std::cout) const override;
    AstNode* propp() const { return op1p(); }  // op1 = property
    AstSenTree* sentreep() const { return VN_CAST(op2p(), SenTree); }  // op2 = clock domain
    void sentreep(AstSenTree* sentreep) { addOp2p(sentreep); }  // op2 = clock domain
    AstNode* passsp() const { return op4p(); }  // op4 = statements (assert/cover passes)
    bool immediate() const { return m_immediate; }
};

class AstAssert final : public AstNodeCoverOrAssert {
public:
    ASTNODE_NODE_FUNCS(Assert)
    AstAssert(FileLine* fl, AstNode* propp, AstNode* passsp, AstNode* failsp, bool immediate,
              const string& name = "")
        : ASTGEN_SUPER(fl, propp, passsp, immediate, name) {
        addNOp3p(failsp);
    }
    AstNode* failsp() const { return op3p(); }  // op3 = if assertion fails
};

class AstAssertIntrinsic final : public AstNodeCoverOrAssert {
    // A $cast or other compiler inserted assert, that must run even without --assert option
public:
    ASTNODE_NODE_FUNCS(AssertIntrinsic)
    AstAssertIntrinsic(FileLine* fl, AstNode* propp, AstNode* passsp, AstNode* failsp,
                       bool immediate, const string& name = "")
        : ASTGEN_SUPER(fl, propp, passsp, immediate, name) {
        addNOp3p(failsp);
    }
    AstNode* failsp() const { return op3p(); }  // op3 = if assertion fails
};

class AstCover final : public AstNodeCoverOrAssert {
public:
    ASTNODE_NODE_FUNCS(Cover)
    AstCover(FileLine* fl, AstNode* propp, AstNode* stmtsp, bool immediate,
             const string& name = "")
        : ASTGEN_SUPER(fl, propp, stmtsp, immediate, name) {}
    AstNode* coverincp() const { return op3p(); }  // op3 = coverage node
    void coverincp(AstCoverInc* nodep) { addOp3p(nodep); }  // op3 = coverage node
    virtual bool immediate() const { return false; }
};

class AstRestrict final : public AstNodeCoverOrAssert {
public:
    ASTNODE_NODE_FUNCS(Restrict)
    AstRestrict(FileLine* fl, AstNode* propp)
        : ASTGEN_SUPER(fl, propp, nullptr, false, "") {}
};

//======================================================================
// Text based nodes

class AstNodeSimpleText VL_NOT_FINAL : public AstNodeText {
private:
    bool m_tracking;  // When emit, it's ok to parse the string to do indentation
public:
    AstNodeSimpleText(AstType t, FileLine* fl, const string& textp, bool tracking = false)
        : AstNodeText(t, fl, textp)
        , m_tracking(tracking) {}
    ASTNODE_BASE_FUNCS(NodeSimpleText)
    void tracking(bool flag) { m_tracking = flag; }
    bool tracking() const { return m_tracking; }
};

class AstText final : public AstNodeSimpleText {
public:
    AstText(FileLine* fl, const string& textp, bool tracking = false)
        : ASTGEN_SUPER(fl, textp, tracking) {}
    ASTNODE_NODE_FUNCS(Text)
};

class AstTextBlock final : public AstNodeSimpleText {
private:
    bool m_commas;  // Comma separate emitted children
public:
    explicit AstTextBlock(FileLine* fl, const string& textp = "", bool tracking = false,
                          bool commas = false)
        : ASTGEN_SUPER(fl, textp, tracking)
        , m_commas(commas) {}
    ASTNODE_NODE_FUNCS(TextBlock)
    void commas(bool flag) { m_commas = flag; }
    bool commas() const { return m_commas; }
    AstNode* nodesp() const { return op1p(); }
    void addNodep(AstNode* nodep) { addOp1p(nodep); }
    void addText(FileLine* fl, const string& textp, bool tracking = false) {
        addNodep(new AstText(fl, textp, tracking));
    }
};

class AstScCtor final : public AstNodeText {
public:
    AstScCtor(FileLine* fl, const string& textp)
        : ASTGEN_SUPER(fl, textp) {}
    ASTNODE_NODE_FUNCS(ScCtor)
    virtual bool isPure() const override { return false; }  // SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const override { return true; }
};

class AstScDtor final : public AstNodeText {
public:
    AstScDtor(FileLine* fl, const string& textp)
        : ASTGEN_SUPER(fl, textp) {}
    ASTNODE_NODE_FUNCS(ScDtor)
    virtual bool isPure() const override { return false; }  // SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const override { return true; }
};

class AstScHdr final : public AstNodeText {
public:
    AstScHdr(FileLine* fl, const string& textp)
        : ASTGEN_SUPER(fl, textp) {}
    ASTNODE_NODE_FUNCS(ScHdr)
    virtual bool isPure() const override { return false; }  // SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const override { return true; }
};

class AstScImp final : public AstNodeText {
public:
    AstScImp(FileLine* fl, const string& textp)
        : ASTGEN_SUPER(fl, textp) {}
    ASTNODE_NODE_FUNCS(ScImp)
    virtual bool isPure() const override { return false; }  // SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const override { return true; }
};

class AstScImpHdr final : public AstNodeText {
public:
    AstScImpHdr(FileLine* fl, const string& textp)
        : ASTGEN_SUPER(fl, textp) {}
    ASTNODE_NODE_FUNCS(ScImpHdr)
    virtual bool isPure() const override { return false; }  // SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const override { return true; }
};

class AstScInt final : public AstNodeText {
public:
    AstScInt(FileLine* fl, const string& textp)
        : ASTGEN_SUPER(fl, textp) {}
    ASTNODE_NODE_FUNCS(ScInt)
    virtual bool isPure() const override { return false; }  // SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const override { return true; }
};

class AstUCStmt final : public AstNodeStmt {
    // User $c statement
public:
    AstUCStmt(FileLine* fl, AstNode* exprsp)
        : ASTGEN_SUPER(fl) {
        addNOp1p(exprsp);
    }
    ASTNODE_NODE_FUNCS(UCStmt)
    AstNode* bodysp() const { return op1p(); }  // op1 = expressions to print
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
};

//======================================================================
// Emitted file nodes

class AstNodeFile VL_NOT_FINAL : public AstNode {
    // Emitted Otput file
    // Parents:  NETLIST
    // Children: AstTextBlock
private:
    string m_name;  ///< Filename
public:
    AstNodeFile(AstType t, FileLine* fl, const string& name)
        : AstNode(t, fl) {
        m_name = name;
    }
    ASTNODE_BASE_FUNCS(NodeFile)
    virtual void dump(std::ostream& str) const override;
    virtual string name() const override { return m_name; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    void tblockp(AstTextBlock* tblockp) { setOp1p(tblockp); }
    AstTextBlock* tblockp() { return VN_CAST(op1p(), TextBlock); }
};

//======================================================================
// Emit V nodes

class AstVFile final : public AstNodeFile {
    // Verilog output file
    // Parents:  NETLIST
public:
    AstVFile(FileLine* fl, const string& name)
        : ASTGEN_SUPER(fl, name) {}
    ASTNODE_NODE_FUNCS(VFile)
    virtual void dump(std::ostream& str = std::cout) const override;
};

//======================================================================
// Emit C nodes

class AstCFile final : public AstNodeFile {
    // C++ output file
    // Parents:  NETLIST
private:
    bool m_slow : 1;  ///< Compile w/o optimization
    bool m_source : 1;  ///< Source file (vs header file)
    bool m_support : 1;  ///< Support file (non systemc)
public:
    AstCFile(FileLine* fl, const string& name)
        : ASTGEN_SUPER(fl, name)
        , m_slow{false}
        , m_source{false}
        , m_support{false} {}
    ASTNODE_NODE_FUNCS(CFile)
    virtual void dump(std::ostream& str = std::cout) const override;
    bool slow() const { return m_slow; }
    void slow(bool flag) { m_slow = flag; }
    bool source() const { return m_source; }
    void source(bool flag) { m_source = flag; }
    bool support() const { return m_support; }
    void support(bool flag) { m_support = flag; }
};

class AstCFunc final : public AstNode {
    // C++ function
    // Parents:  MODULE/SCOPE
    // Children: VAR/statements
private:
    AstCFuncType m_funcType;
    AstScope* m_scopep;
    string m_name;
    string m_cname;  // C name, for dpiExports
    string m_rtnType;  // void, bool, or other return type
    string m_argTypes;  // Argument types
    string m_ctorInits;  // Constructor sub-class inits
    string m_ifdef;  // #ifdef symbol around this function
    VBoolOrUnknown m_isConst;  // Function is declared const (*this not changed)
    VBoolOrUnknown m_isStatic;  // Function is declared static (no this)
    bool m_dontCombine : 1;  // V3Combine shouldn't compare this func tree, it's special
    bool m_skipDecl : 1;  // Don't declare it
    bool m_declPrivate : 1;  // Declare it private
    bool m_formCallTree : 1;  // Make a global function to call entire tree of functions
    bool m_slow : 1;  // Slow routine, called once or just at init time
    bool m_funcPublic : 1;  // From user public task/function
    bool m_isConstructor : 1;  // Is C class constructor
    bool m_isDestructor : 1;  // Is C class destructor
    bool m_isMethod : 1;  // Is inside a class definition
    bool m_isInline : 1;  // Inline function
    bool m_isVirtual : 1;  // Virtual function
    bool m_symProlog : 1;  // Setup symbol table for later instructions
    bool m_entryPoint : 1;  // User may call into this top level function
    bool m_pure : 1;  // Pure function
    bool m_dpiExport : 1;  // From dpi export
    bool m_dpiExportWrapper : 1;  // From dpi export; static function with dispatch table
    bool m_dpiImport : 1;  // From dpi import
    bool m_dpiImportWrapper : 1;  // Wrapper from dpi import
public:
    AstCFunc(FileLine* fl, const string& name, AstScope* scopep, const string& rtnType = "")
        : ASTGEN_SUPER(fl) {
        m_funcType = AstCFuncType::FT_NORMAL;
        m_isConst = VBoolOrUnknown::BU_UNKNOWN;  // Unknown until analyzed
        m_isStatic = VBoolOrUnknown::BU_UNKNOWN;  // Unknown until see where thisp needed
        m_scopep = scopep;
        m_name = name;
        m_rtnType = rtnType;
        m_dontCombine = false;
        m_skipDecl = false;
        m_declPrivate = false;
        m_formCallTree = false;
        m_slow = false;
        m_funcPublic = false;
        m_isConstructor = false;
        m_isDestructor = false;
        m_isMethod = true;
        m_isInline = false;
        m_isVirtual = false;
        m_symProlog = false;
        m_entryPoint = false;
        m_pure = false;
        m_dpiExport = false;
        m_dpiExportWrapper = false;
        m_dpiImport = false;
        m_dpiImportWrapper = false;
    }
    ASTNODE_NODE_FUNCS(CFunc)
    virtual string name() const override { return m_name; }
    virtual const char* broken() const override {
        BROKEN_RTN((m_scopep && !m_scopep->brokeExists()));
        return nullptr;
    }
    virtual bool maybePointedTo() const override { return true; }
    virtual void dump(std::ostream& str = std::cout) const override;
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override {
        const AstCFunc* asamep = static_cast<const AstCFunc*>(samep);
        return ((funcType() == asamep->funcType()) && (rtnTypeVoid() == asamep->rtnTypeVoid())
                && (argTypes() == asamep->argTypes()) && (ctorInits() == asamep->ctorInits())
                && (!(dpiImport() || dpiExport()) || name() == asamep->name()));
    }
    //
    virtual void name(const string& name) override { m_name = name; }
    virtual int instrCount() const override { return dpiImport() ? instrCountDpi() : 0; }
    VBoolOrUnknown isConst() const { return m_isConst; }
    void isConst(bool flag) { m_isConst.setTrueOrFalse(flag); }
    void isConst(VBoolOrUnknown flag) { m_isConst = flag; }
    VBoolOrUnknown isStatic() const { return m_isStatic; }
    void isStatic(bool flag) { m_isStatic.setTrueOrFalse(flag); }
    void isStatic(VBoolOrUnknown flag) { m_isStatic = flag; }
    void cname(const string& name) { m_cname = name; }
    string cname() const { return m_cname; }
    AstScope* scopep() const { return m_scopep; }
    void scopep(AstScope* nodep) { m_scopep = nodep; }
    string rtnTypeVoid() const { return ((m_rtnType == "") ? "void" : m_rtnType); }
    bool dontCombine() const { return m_dontCombine || funcType() != AstCFuncType::FT_NORMAL; }
    void dontCombine(bool flag) { m_dontCombine = flag; }
    bool dontInline() const { return dontCombine() || slow() || skipDecl() || funcPublic(); }
    bool skipDecl() const { return m_skipDecl; }
    void skipDecl(bool flag) { m_skipDecl = flag; }
    bool declPrivate() const { return m_declPrivate; }
    void declPrivate(bool flag) { m_declPrivate = flag; }
    bool formCallTree() const { return m_formCallTree; }
    void formCallTree(bool flag) { m_formCallTree = flag; }
    bool slow() const { return m_slow; }
    void slow(bool flag) { m_slow = flag; }
    bool funcPublic() const { return m_funcPublic; }
    void funcPublic(bool flag) { m_funcPublic = flag; }
    void argTypes(const string& str) { m_argTypes = str; }
    string argTypes() const { return m_argTypes; }
    void ctorInits(const string& str) { m_ctorInits = str; }
    string ctorInits() const { return m_ctorInits; }
    void ifdef(const string& str) { m_ifdef = str; }
    string ifdef() const { return m_ifdef; }
    void funcType(AstCFuncType flag) { m_funcType = flag; }
    AstCFuncType funcType() const { return m_funcType; }
    bool isConstructor() const { return m_isConstructor; }
    void isConstructor(bool flag) { m_isConstructor = flag; }
    bool isDestructor() const { return m_isDestructor; }
    void isDestructor(bool flag) { m_isDestructor = flag; }
    bool isMethod() const { return m_isMethod; }
    void isMethod(bool flag) { m_isMethod = flag; }
    bool isInline() const { return m_isInline; }
    void isInline(bool flag) { m_isInline = flag; }
    bool isVirtual() const { return m_isVirtual; }
    void isVirtual(bool flag) { m_isVirtual = flag; }
    bool symProlog() const { return m_symProlog; }
    void symProlog(bool flag) { m_symProlog = flag; }
    bool entryPoint() const { return m_entryPoint; }
    void entryPoint(bool flag) { m_entryPoint = flag; }
    bool pure() const { return m_pure; }
    void pure(bool flag) { m_pure = flag; }
    bool dpiExport() const { return m_dpiExport; }
    void dpiExport(bool flag) { m_dpiExport = flag; }
    bool dpiExportWrapper() const { return m_dpiExportWrapper; }
    void dpiExportWrapper(bool flag) { m_dpiExportWrapper = flag; }
    bool dpiImport() const { return m_dpiImport; }
    void dpiImport(bool flag) { m_dpiImport = flag; }
    bool dpiImportWrapper() const { return m_dpiImportWrapper; }
    void dpiImportWrapper(bool flag) { m_dpiImportWrapper = flag; }
    //
    // If adding node accessors, see below emptyBody
    AstNode* argsp() const { return op1p(); }
    void addArgsp(AstNode* nodep) { addOp1p(nodep); }
    AstNode* initsp() const { return op2p(); }
    void addInitsp(AstNode* nodep) { addOp2p(nodep); }
    AstNode* stmtsp() const { return op3p(); }
    void addStmtsp(AstNode* nodep) { addOp3p(nodep); }
    AstNode* finalsp() const { return op4p(); }
    void addFinalsp(AstNode* nodep) { addOp4p(nodep); }
    // Special methods
    bool emptyBody() const {
        return argsp() == nullptr && initsp() == nullptr && stmtsp() == nullptr
               && finalsp() == nullptr;
    }
};

class AstCCall final : public AstNodeCCall {
    // C++ function call
    // Parents:  Anything above a statement
    // Children: Args to the function
public:
    AstCCall(FileLine* fl, AstCFunc* funcp, AstNode* argsp = nullptr)
        : ASTGEN_SUPER(fl, funcp, argsp) {}
    // Replacement form for V3Combine
    // Note this removes old attachments from the oldp
    AstCCall(AstCCall* oldp, AstCFunc* funcp)
        : ASTGEN_SUPER(oldp, funcp) {}
    ASTNODE_NODE_FUNCS(CCall)
};

class AstCMethodCall final : public AstNodeCCall {
    // C++ method call
    // Parents:  Anything above a statement
    // Children: Args to the function
public:
    AstCMethodCall(FileLine* fl, AstNode* fromp, AstCFunc* funcp, AstNode* argsp = nullptr)
        : ASTGEN_SUPER(fl, funcp, argsp) {
        setOp1p(fromp);
    }
    ASTNODE_NODE_FUNCS(CMethodCall)
    virtual const char* broken() const override {
        BROKEN_BASE_RTN(AstNodeCCall::broken());
        BROKEN_RTN(!fromp());
        return nullptr;
    }
    AstNode* fromp() const {
        return op1p();
    }  // op1 = Extracting what (nullptr=TBD during parsing)
    void fromp(AstNode* nodep) { setOp1p(nodep); }
};

class AstCNew final : public AstNodeCCall {
    // C++ new() call
    // Parents:  Anything above an expression
    // Children: Args to the function
public:
    AstCNew(FileLine* fl, AstCFunc* funcp, AstNode* argsp = nullptr)
        : ASTGEN_SUPER(fl, funcp, argsp) {
        statement(false);
    }
    // Replacement form for V3Combine
    // Note this removes old attachments from the oldp
    AstCNew(AstCCall* oldp, AstCFunc* funcp)
        : ASTGEN_SUPER(oldp, funcp) {}
    virtual bool hasDType() const override { return true; }
    ASTNODE_NODE_FUNCS(CNew)
};

class AstCReturn final : public AstNodeStmt {
    // C++ return from a function
    // Parents:  CFUNC/statement
    // Children: Math
public:
    AstCReturn(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER(fl) {
        setOp1p(lhsp);
    }
    ASTNODE_NODE_FUNCS(CReturn)
    virtual int instrCount() const override { return widthInstrs(); }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    //
    AstNode* lhsp() const { return op1p(); }
};

class AstCMath final : public AstNodeMath {
private:
    bool m_cleanOut;
    bool m_pure;  // Pure optimizable
public:
    // Emit C textual math function (like AstUCFunc)
    AstCMath(FileLine* fl, AstNode* exprsp)
        : ASTGEN_SUPER(fl)
        , m_cleanOut{true}
        , m_pure{false} {
        addOp1p(exprsp);
        dtypeFrom(exprsp);
    }
    AstCMath(FileLine* fl, const string& textStmt, int setwidth, bool cleanOut = true)
        : ASTGEN_SUPER(fl)
        , m_cleanOut{cleanOut}
        , m_pure{true} {
        addNOp1p(new AstText(fl, textStmt, true));
        if (setwidth) dtypeSetLogicSized(setwidth, VSigning::UNSIGNED);
    }
    ASTNODE_NODE_FUNCS(CMath)
    virtual bool isGateOptimizable() const override { return m_pure; }
    virtual bool isPredictOptimizable() const override { return m_pure; }
    virtual bool cleanOut() const override { return m_cleanOut; }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    void addBodysp(AstNode* nodep) { addNOp1p(nodep); }
    AstNode* bodysp() const { return op1p(); }  // op1 = expressions to print
    bool pure() const { return m_pure; }
    void pure(bool flag) { m_pure = flag; }
};

class AstCReset final : public AstNodeStmt {
    // Reset variable at startup
public:
    AstCReset(FileLine* fl, AstNode* exprsp)
        : ASTGEN_SUPER(fl) {
        addNOp1p(exprsp);
    }
    ASTNODE_NODE_FUNCS(CReset)
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    AstVarRef* varrefp() const { return VN_CAST(op1p(), VarRef); }  // op1 = varref to reset
};

class AstCStmt final : public AstNodeStmt {
    // Emit C statement
public:
    AstCStmt(FileLine* fl, AstNode* exprsp)
        : ASTGEN_SUPER(fl) {
        addNOp1p(exprsp);
    }
    AstCStmt(FileLine* fl, const string& textStmt)
        : ASTGEN_SUPER(fl) {
        addNOp1p(new AstText(fl, textStmt, true));
    }
    ASTNODE_NODE_FUNCS(CStmt)
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual V3Hash sameHash() const override { return V3Hash(); }
    virtual bool same(const AstNode* samep) const override { return true; }
    void addBodysp(AstNode* nodep) { addNOp1p(nodep); }
    AstNode* bodysp() const { return op1p(); }  // op1 = expressions to print
};

class AstCUse final : public AstNode {
    // C++ use of a class or #include; indicates need of forward declaration
    // Parents:  NODEMODULE
private:
    VUseType m_useType;  // What sort of use this is
    string m_name;

public:
    AstCUse(FileLine* fl, VUseType useType, const string& name)
        : ASTGEN_SUPER(fl)
        , m_useType{useType}
        , m_name{name} {}
    ASTNODE_NODE_FUNCS(CUse)
    virtual string name() const override { return m_name; }
    virtual void dump(std::ostream& str = std::cout) const override;
    VUseType useType() const { return m_useType; }
    void useType(VUseType useType) { m_useType = useType; }
};

class AstMTaskBody final : public AstNode {
    // Hold statements for each MTask
private:
    ExecMTask* m_execMTaskp = nullptr;

public:
    explicit AstMTaskBody(FileLine* fl)
        : ASTGEN_SUPER(fl) {}
    ASTNODE_NODE_FUNCS(MTaskBody);
    virtual const char* broken() const override {
        BROKEN_RTN(!m_execMTaskp);
        return nullptr;
    }
    AstNode* stmtsp() const { return op1p(); }
    void addStmtsp(AstNode* nodep) { addOp1p(nodep); }
    ExecMTask* execMTaskp() const { return m_execMTaskp; }
    void execMTaskp(ExecMTask* execMTaskp) { m_execMTaskp = execMTaskp; }
    virtual void dump(std::ostream& str = std::cout) const override;
};

class AstExecGraph final : public AstNode {
    // For parallel execution, this node contains a dependency graph.  Each
    // node in the graph is an ExecMTask, which contains a body for the
    // mtask, which contains a set of AstActive's, each of which calls a
    // leaf AstCFunc. whew!
    //
    // The mtask bodies are also children of this node, so we can visit
    // them without traversing the graph (it's not always needed to
    // traverse the graph.)
private:
    V3Graph* m_depGraphp;  // contains ExecMTask's
public:
    explicit AstExecGraph(FileLine* fl);
    ASTNODE_NODE_FUNCS_NO_DTOR(ExecGraph)
    virtual ~AstExecGraph() override;
    virtual const char* broken() const override {
        BROKEN_RTN(!m_depGraphp);
        return nullptr;
    }
    const V3Graph* depGraphp() const { return m_depGraphp; }
    V3Graph* mutableDepGraphp() { return m_depGraphp; }
    void addMTaskBody(AstMTaskBody* bodyp) { addOp1p(bodyp); }
};

class AstSplitPlaceholder final : public AstNode {
public:
    // Dummy node used within V3Split; never exists outside of V3Split.
    explicit AstSplitPlaceholder(FileLine* fl)
        : ASTGEN_SUPER(fl) {}
    ASTNODE_NODE_FUNCS(SplitPlaceholder)
};

//######################################################################
// Right below top

class AstTypeTable final : public AstNode {
    // Container for hash of standard data types
    // Children:  NODEDTYPEs
    AstVoidDType* m_voidp = nullptr;
    AstQueueDType* m_queueIndexp = nullptr;
    AstBasicDType* m_basicps[AstBasicDTypeKwd::_ENUM_MAX];
    //
    using DetailedMap = std::map<VBasicTypeKey, AstBasicDType*>;
    DetailedMap m_detailedMap;

public:
    explicit AstTypeTable(FileLine* fl)
        : ASTGEN_SUPER(fl) {
        for (int i = 0; i < AstBasicDTypeKwd::_ENUM_MAX; ++i) m_basicps[i] = nullptr;
    }
    ASTNODE_NODE_FUNCS(TypeTable)
    AstNodeDType* typesp() const { return VN_CAST(op1p(), NodeDType); }  // op1 = List of dtypes
    void addTypesp(AstNodeDType* nodep) { addOp1p(nodep); }
    AstVoidDType* findVoidDType(FileLine* fl);
    AstQueueDType* findQueueIndexDType(FileLine* fl);
    AstBasicDType* findBasicDType(FileLine* fl, AstBasicDTypeKwd kwd);
    AstBasicDType* findLogicBitDType(FileLine* fl, AstBasicDTypeKwd kwd, int width, int widthMin,
                                     VSigning numeric);
    AstBasicDType* findLogicBitDType(FileLine* fl, AstBasicDTypeKwd kwd, const VNumRange& range,
                                     int widthMin, VSigning numeric);
    AstBasicDType* findInsertSameDType(AstBasicDType* nodep);
    void clearCache();
    void repairCache();
    virtual void dump(std::ostream& str = std::cout) const override;
};

//######################################################################
// Top

class AstNetlist final : public AstNode {
    // All modules are under this single top node.
    // Parents:   none
    // Children:  MODULEs & CFILEs
private:
    AstTypeTable* m_typeTablep = nullptr;  // Reference to top type table, for faster lookup
    AstPackage* m_dollarUnitPkgp = nullptr;  // $unit
    AstCFunc* m_evalp = nullptr;  // The '_eval' function
    AstExecGraph* m_execGraphp = nullptr;  // Execution MTask graph for threads>1 mode
    VTimescale m_timeunit;  // Global time unit
    VTimescale m_timeprecision;  // Global time precision
    bool m_timescaleSpecified = false;  // Input HDL specified timescale
public:
    AstNetlist()
        : ASTGEN_SUPER(new FileLine(FileLine::builtInFilename())) {}
    ASTNODE_NODE_FUNCS(Netlist)
    virtual const char* broken() const override {
        BROKEN_RTN(m_dollarUnitPkgp && !m_dollarUnitPkgp->brokeExists());
        BROKEN_RTN(m_evalp && !m_evalp->brokeExists());
        return nullptr;
    }
    virtual string name() const override { return "$root"; }
    virtual void dump(std::ostream& str) const override;
    AstNodeModule* modulesp() const {  // op1 = List of modules
        return VN_CAST(op1p(), NodeModule);
    }
    AstNodeModule* topModulep() const {  // * = Top module in hierarchy (first one added, for now)
        return VN_CAST(op1p(), NodeModule);
    }
    void addModulep(AstNodeModule* modulep) { addOp1p(modulep); }
    AstNodeFile* filesp() const { return VN_CAST(op2p(), NodeFile); }  // op2 = List of files
    void addFilesp(AstNodeFile* filep) { addOp2p(filep); }
    AstNode* miscsp() const { return op3p(); }  // op3 = List of dtypes etc
    void addMiscsp(AstNode* nodep) { addOp3p(nodep); }
    AstTypeTable* typeTablep() { return m_typeTablep; }
    void addTypeTablep(AstTypeTable* nodep) {
        m_typeTablep = nodep;
        addMiscsp(nodep);
    }
    AstPackage* dollarUnitPkgp() const { return m_dollarUnitPkgp; }
    AstPackage* dollarUnitPkgAddp() {
        if (!m_dollarUnitPkgp) {
            m_dollarUnitPkgp = new AstPackage(fileline(), AstPackage::dollarUnitName());
            // packages are always libraries; don't want to make them a "top"
            m_dollarUnitPkgp->inLibrary(true);
            m_dollarUnitPkgp->modTrace(false);  // may reconsider later
            m_dollarUnitPkgp->internal(true);
            addModulep(m_dollarUnitPkgp);
        }
        return m_dollarUnitPkgp;
    }
    AstCFunc* evalp() const { return m_evalp; }
    void evalp(AstCFunc* evalp) { m_evalp = evalp; }
    AstExecGraph* execGraphp() const { return m_execGraphp; }
    void execGraphp(AstExecGraph* graphp) { m_execGraphp = graphp; }
    VTimescale timeunit() const { return m_timeunit; }
    void timeunit(const VTimescale& value) { m_timeunit = value; }
    VTimescale timeprecision() const { return m_timeprecision; }
    void timeInit() {
        m_timeunit = v3Global.opt.timeDefaultUnit();
        m_timeprecision = v3Global.opt.timeDefaultPrec();
    }
    void timeprecisionMerge(FileLine*, const VTimescale& value);
    void timescaleSpecified(bool specified) { m_timescaleSpecified = specified; }
    bool timescaleSpecified() const { return m_timescaleSpecified; }
};

//######################################################################

#undef ASTGEN_SUPER

#endif  // Guard
