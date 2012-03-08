// -*- C++ -*-
//*************************************************************************
// DESCRIPTION: Verilator: Ast node structure
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2012 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#ifndef _V3ASTNODES_H_
#define _V3ASTNODES_H_ 1

#ifndef _V3AST_H_
#error "Use V3Ast.h as the include"
#endif

//######################################################################
// Standard defines for all AstNode final classes

#define ASTNODE_NODE_FUNCS(name,ucname)	\
    virtual ~Ast ##name() {} \
    virtual AstType type() const { return AstType::at ##ucname; } \
    virtual AstNode* clone() { return new Ast ##name (*this); } \
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); } \
    Ast ##name * cloneTree(bool cloneNext) { return AstNode::cloneTree(cloneNext)->cast ##name(); }

//######################################################################
//=== Ast* : Specific types
// Netlist interconnect

struct AstConst : public AstNodeMath {
    // A constant
private:
    V3Number	m_num;		// Constant value
public:
    AstConst(FileLine* fl, const V3Number& num)
	:AstNodeMath(fl)
	,m_num(num) {
	if (m_num.isDouble()) {
	    dtypeChgDouble();
	} else {
	    width(m_num.width(), m_num.sized()?0:m_num.widthMin());
	    numeric(m_num.isSigned() ? AstNumeric::SIGNED
		    : AstNumeric::UNSIGNED);
	}
    }
    AstConst(FileLine* fl, uint32_t num)
	:AstNodeMath(fl)
	,m_num(V3Number(fl,32,num)) { width(m_num.width(), m_num.sized()?0:m_num.widthMin()); }
    class Unsized32 {};		// for creator type-overload selection
    AstConst(FileLine* fl, Unsized32, uint32_t num)  // Unsized 32-bit integer of specified value
	:AstNodeMath(fl)
	,m_num(V3Number(fl,32,num)) { m_num.width(32,false); width(32,m_num.widthMin()); }
    class RealDouble {};		// for creator type-overload selection
    AstConst(FileLine* fl, RealDouble, double num)
	:AstNodeMath(fl)
	,m_num(V3Number(fl,64)) { m_num.setDouble(num); dtypeChgDouble(); }
    class LogicFalse {};
    AstConst(FileLine* fl, LogicFalse) // Shorthand const 0, know the dtype should be a logic of size 1
	:AstNodeMath(fl)
	,m_num(V3Number(fl,1,0)) { dtypeChgLogicBool(); }
    class LogicTrue {};
    AstConst(FileLine* fl, LogicTrue) // Shorthand const 1, know the dtype should be a logic of size 1
	:AstNodeMath(fl)
	,m_num(V3Number(fl,1,1)) { dtypeChgLogicBool(); }

    ASTNODE_NODE_FUNCS(Const, CONST)
    virtual string name()	const { return num().ascii(); }		// * = Value
    virtual const V3Number& num()	const { return m_num; }		// * = Value
    uint32_t toUInt()  const { return num().toUInt(); }
    vlsint32_t toSInt()  const { return num().toSInt(); }
    vluint64_t toUQuad() const { return num().toUQuad(); }
    virtual string emitVerilog() { V3ERROR_NA; return ""; }  // Implemented specially
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool cleanOut() { return true; }
    virtual V3Hash sameHash() const { return V3Hash(num().toHash()); }
    virtual bool same(AstNode* samep) const {
	return num().isCaseEq(samep->castConst()->num()); }
    virtual int instrCount() const { return widthInstrs(); }
    bool isEqAllOnes() const { return num().isEqAllOnes(width()); }
    bool isEqAllOnesV() const { return num().isEqAllOnes(widthMin()); }
};

struct AstConstString : public AstNodeMath {
    // A constant string
private:
    string	m_name;
public:
    AstConstString(FileLine* fl, const string& name)
	: AstNodeMath(fl), m_name(name) {
	rewidth();
    }
    void rewidth() {
	if (m_name.length()==0) {
	    width(1,1);  // 0 width isn't allowed due to historic special cases
	} else {
	    width(((int)m_name.length())*8, ((int)m_name.length())*8);
	}
    }
    ASTNODE_NODE_FUNCS(ConstString, CONSTSTRING)
    virtual string emitVerilog() { V3ERROR_NA; return ""; }  // Implemented specially
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool cleanOut() { return true; }
    virtual V3Hash sameHash() const { return V3Hash(name()); }
    virtual bool same(AstNode* samep) const {
	return name()==samep->castConstString()->name(); }
    virtual int instrCount() const { return 2; }  // C just loads a pointer
    virtual string name() const { return m_name; }
    void name(const string& flag) { m_name = flag; rewidth(); }
};

struct AstRange : public AstNode {
    // Range specification, for use under variables and cells
private:
    bool	m_littleEndian:1;	// Bit vector is little endian
public:
    AstRange(FileLine* fl, AstNode* msbp, AstNode* lsbp)
	:AstNode(fl) {
	m_littleEndian = false;
	setOp2p(msbp); setOp3p(lsbp); }
    AstRange(FileLine* fl, int msb, int lsb)
	:AstNode(fl) {
	m_littleEndian = false;
	setOp2p(new AstConst(fl,msb)); setOp3p(new AstConst(fl,lsb));
    }
    ASTNODE_NODE_FUNCS(Range, RANGE)
    AstNode* msbp() const { return op2p()->castNode(); }	// op2 = Msb expression
    AstNode* lsbp() const { return op3p()->castNode(); }	// op3 = Lsb expression
    AstNode* msbEndianedp() const { return littleEndian()?lsbp():msbp(); }  // How to show a declaration
    AstNode* lsbEndianedp() const { return littleEndian()?msbp():lsbp(); }
    int	     msbConst()	const { AstConst* constp=msbp()->castConst(); return (constp?constp->toSInt():0); }
    int	     lsbConst()	const { AstConst* constp=lsbp()->castConst(); return (constp?constp->toSInt():0); }
    int	     elementsConst() const { return (msbConst()>lsbConst()) ? msbConst()-lsbConst()+1 : lsbConst()-msbConst()+1; }
    bool     littleEndian() const { return m_littleEndian; }
    void     littleEndian(bool flag) { m_littleEndian=flag; }
    virtual void dump(ostream& str);
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
};

//######################################################################
//==== Data Types

struct AstTypedef : public AstNode {
private:
    string	m_name;
public:
    AstTypedef(FileLine* fl, const string& name, AstNodeDType* dtp)
	: AstNode(fl), m_name(name) {
	setOp1p(dtp);
	widthSignedFrom(dtp);
    }
    ASTNODE_NODE_FUNCS(Typedef, TYPEDEF)
    AstNodeDType* dtypep() const { return op1p()->castNodeDType(); } // op1 = Range of variable
    void	dtypep(AstNodeDType* nodep) { setOp1p(nodep); }
    // METHODS
    virtual string name() const { return m_name; }
    virtual bool maybePointedTo() const { return true; }
    void name(const string& flag) { m_name = flag; }
};

struct AstTypedefFwd : public AstNode {
    // Forward declaration of a type; stripped after netlist parsing is complete
private:
    string	m_name;
public:
    AstTypedefFwd(FileLine* fl, const string& name)
	: AstNode(fl), m_name(name) {}
    ASTNODE_NODE_FUNCS(TypedefFwd, TYPEDEFFWD)
    // METHODS
    virtual string name() const { return m_name; }
};

struct AstDefImplicitDType : public AstNodeDType {
    // For parsing enum/struct/unions that are declared with a variable rather than typedef
    // This allows "var enum {...} a,b" to share the enum definition for both variables
    // After link, these become typedefs
private:
    string	m_name;
    void*	m_containerp;	// In what scope is the name unique, so we can know what are duplicate definitions (arbitrary value)
public:
    AstDefImplicitDType(FileLine* fl, const string& name, AstNode* containerp, AstNodeDType* dtp)
	: AstNodeDType(fl), m_name(name), m_containerp(containerp) {
	setOp1p(dtp);
	widthSignedFrom(dtp);
    }
    ASTNODE_NODE_FUNCS(DefImplicitDType, DEFIMPLICITDTYPE)
    AstNodeDType* dtypep() const { return op1p()->castNodeDType(); } // op1 = Range of variable
    AstNodeDType* dtypeSkipRefp() const { return dtypep()->skipRefp(); }	// op1 = Range of variable
    void	dtypep(AstNodeDType* nodep) { setOp1p(nodep); }
    void*	containerp() const { return m_containerp; }
    // METHODS
    virtual AstBasicDType* basicp() const { return dtypep()->basicp(); }  // (Slow) recurse down to find basic data type
    virtual AstNodeDType* skipRefp() const { return (AstNodeDType*)this; }
    virtual int widthAlignBytes() const { return dtypep()->widthAlignBytes(); }
    virtual int widthTotalBytes() const { return dtypep()->widthTotalBytes(); }
    virtual string name() const { return m_name; }
    void name(const string& flag) { m_name = flag; }
};

struct AstArrayDType : public AstNodeDType {
    // Array data type, ie "some_dtype var_name [2:0]"
private:
    bool		m_packed;
public:
    AstArrayDType(FileLine* fl, AstNodeDType* dtp, AstRange* rangep, bool isPacked=false)
	: AstNodeDType(fl), m_packed(isPacked) {
	setOp1p(dtp);
	setOp2p(rangep);
	widthSignedFrom(dtp);
    }
    ASTNODE_NODE_FUNCS(ArrayDType, ARRAYDTYPE)
    virtual void dump(ostream& str);
    AstNodeDType* dtypep() const { return op1p()->castNodeDType(); } // op1 = Range of variable
    AstNodeDType* dtypeSkipRefp() const { return dtypep()->skipRefp(); }	// op1 = Range of variable
    void	dtypep(AstNodeDType* nodep) { setOp1p(nodep); }
    AstRange*	arrayp() const { return op2p()->castRange(); }	// op2 = Array(s) of variable
    void	arrayp(AstRange* nodep) { setOp2p(nodep); }
    // METHODS
    virtual AstBasicDType* basicp() const { return dtypep()->basicp(); }  // (Slow) recurse down to find basic data type
    virtual AstNodeDType* skipRefp() const { return (AstNodeDType*)this; }
    virtual int widthAlignBytes() const { return dtypep()->widthAlignBytes(); }
    virtual int widthTotalBytes() const { return elementsConst() * dtypep()->widthTotalBytes(); }
    int		msb() const { return arrayp()->msbConst(); }
    int		lsb() const { return arrayp()->lsbConst(); }
    int		elementsConst() const { return arrayp()->elementsConst(); }
    int		msbMaxSelect() const { return (lsb()<0 ? msb()-lsb() : msb()); } // Maximum value a [] select may index
    bool	isPacked() const { return m_packed; }
};

struct AstBasicDType : public AstNodeDType {
    // Builtin atomic/vectored data type
    // Children: RANGE (converted to constant in V3Width)
private:
    AstBasicDTypeKwd	m_keyword;	// What keyword created it
    bool		m_implicit;	// Implicitly declared
    bool		m_nosigned;	// Implicit without sign
    int			m_msb;		// MSB when no range attached
public:
    AstBasicDType(FileLine* fl, AstBasicDTypeKwd kwd, AstSignedState signst=signedst_NOSIGNED)
	: AstNodeDType(fl) {
	init(kwd, signst, 0, NULL);
    }
    AstBasicDType(FileLine* fl, AstLogicPacked, int wantwidth)
	: AstNodeDType(fl) {
	init(AstBasicDTypeKwd::LOGIC, signedst_NOSIGNED, wantwidth, NULL);
    }
    AstBasicDType(FileLine* fl, AstBitPacked, int wantwidth)
	: AstNodeDType(fl) {
	init(AstBasicDTypeKwd::BIT, signedst_NOSIGNED, wantwidth, NULL);
    }
    // See also addRange in verilog.y
private:
    void init(AstBasicDTypeKwd kwd, AstSignedState signst, int wantwidth, AstRange* rangep) {
	m_keyword = kwd;
	m_msb = 0;
	// Implicitness: // "parameter X" is implicit and sized from initial value, "parameter reg x" not
	m_implicit = false;
	m_nosigned = false;
	if (keyword()==AstBasicDTypeKwd::LOGIC_IMPLICIT) {
	    if (!rangep && !wantwidth) m_implicit = true;  // Also cleared if range added later
	    m_keyword = AstBasicDTypeKwd::LOGIC;
	}
	if (signst == signedst_NOSIGNED) {
	    if (keyword().isSigned()) signst = signedst_SIGNED;
	    else m_nosigned = true;
	}
	if (keyword().isDouble()) dtypeChgDouble();
	else setSignedState(signst);
	if (!rangep && wantwidth) { // Constant width
	    m_msb = wantwidth - 1;
	    width(wantwidth, wantwidth);
	} else if (!rangep) {  // Set based on keyword properties
	    // V3Width will pull from this width
	    if (keyword().width() > 1 && !isOpaque()) rangep = new AstRange(fileline(), keyword().width()-1, 0);
	    width(keyword().width(), keyword().width());
	} else {
	    width(rangep->elementsConst(), rangep->elementsConst());  // Maybe unknown if parameters underneath it
	}
	setNOp1p(rangep);
    }
public:
    ASTNODE_NODE_FUNCS(BasicDType, BASICDTYPE)
    virtual void dump(ostream& str);
    virtual V3Hash sameHash() const { return V3Hash(keyword()); }
    virtual bool same(AstNode* samep) const {
	return samep->castBasicDType()->keyword() == keyword(); }
    virtual string name()	const { return m_keyword.ascii(); }
    AstRange*	rangep() 	const { return op1p()->castRange(); }	// op1 = Range of variable
    void	rangep(AstRange* nodep) { setNOp1p(nodep); }
    void	setSignedState(AstSignedState signst) {
	if (signst==signedst_UNSIGNED) numeric(AstNumeric::UNSIGNED);
	else if (signst==signedst_SIGNED) numeric(AstNumeric::SIGNED);
    }
    // METHODS
    virtual AstBasicDType* basicp() const { return (AstBasicDType*)this; }  // (Slow) recurse down to find basic data type
    virtual AstNodeDType* skipRefp() const { return (AstNodeDType*)this; }
    virtual int widthAlignBytes() const; // (Slow) recurses - Structure alignment 1,2,4 or 8 bytes (arrays affect this)
    virtual int widthTotalBytes() const; // (Slow) recurses - Width in bytes rounding up 1,2,4,8,12,...
    AstBasicDTypeKwd keyword() const { return m_keyword; }  // Avoid using - use isSomething accessors instead
    bool	isBitLogic() const { return keyword().isBitLogic(); }
    bool	isDouble() const { return keyword().isDouble(); }
    bool	isOpaque() const { return keyword().isOpaque(); }
    bool	isSloppy() const { return keyword().isSloppy(); }
    bool	isZeroInit() const { return keyword().isZeroInit(); }
    bool	isRanged() const { return rangep() || m_msb; }
    int		msb() const { if (!rangep()) return m_msb; return rangep()->msbConst(); }
    int		lsb() const { if (!rangep()) return 0; return rangep()->lsbConst(); }
    int		msbEndianed() const { if (!rangep()) return m_msb; return littleEndian()?rangep()->lsbConst():rangep()->msbConst(); }
    int		lsbEndianed() const { if (!rangep()) return 0; return littleEndian()?rangep()->msbConst():rangep()->lsbConst(); }
    int		msbMaxSelect() const { return (lsb()<0 ? msb()-lsb() : msb()); } // Maximum value a [] select may index
    bool	littleEndian() const { return (rangep() && rangep()->littleEndian()); }
    bool	implicit() const { return m_implicit; }
    void	implicit(bool flag) { m_implicit = flag; }
    bool	nosigned() const { return m_nosigned; }
    void	cvtRangeConst() {}  // Convert to smaller represenation - disabled
};

struct AstConstDType : public AstNodeDType {
    // const data type, ie "const some_dtype var_name [2:0]"
    // ConstDType are removed in V3LinkLValue and become AstVar::isConst.
    // When more generic types are supported AstConstDType will be propagated further.
    AstConstDType(FileLine* fl, AstNodeDType* dtp)
	: AstNodeDType(fl) {
	setOp1p(dtp);
	widthSignedFrom(dtp);
    }
    ASTNODE_NODE_FUNCS(ConstDType, CONSTDTYPE)
    AstNodeDType* dtypep() const { return op1p()->castNodeDType(); } // op1 = Range of variable
    void	dtypep(AstNodeDType* nodep) { setOp1p(nodep); }
    // METHODS
    virtual AstBasicDType* basicp() const { return dtypep()->basicp(); }  // (Slow) recurse down to find basic data type
    virtual AstNodeDType* skipRefp() const { return (AstNodeDType*)this; }
    virtual int widthAlignBytes() const { return dtypep()->widthAlignBytes(); }
    virtual int widthTotalBytes() const { return dtypep()->widthTotalBytes(); }
};

struct AstRefDType : public AstNodeDType {
private:
    AstNodeDType* m_defp;	// data type pointed to, BELOW the AstTypedef
    string	m_name;		// Name of an AstTypedef
    AstPackage*	m_packagep;	// Package hierarchy
public:
    AstRefDType(FileLine* fl, const string& name)
	: AstNodeDType(fl), m_defp(NULL), m_name(name), m_packagep(NULL) {}
    AstRefDType(FileLine* fl, AstNodeDType* defp)
	: AstNodeDType(fl), m_defp(defp), m_packagep(NULL) {
	widthSignedFrom(defp);
    }
    ASTNODE_NODE_FUNCS(RefDType, REFDTYPE)
    // METHODS
    virtual bool broken() const { return m_defp && !m_defp->brokeExists(); }
    virtual void cloneRelink() { if (m_defp && m_defp->clonep()) {
	m_defp = m_defp->clonep()->castNodeDType();
    }}
    virtual V3Hash sameHash() const { return V3Hash(skipRefp()); }
    virtual bool same(AstNode* samep) const {
	return skipRefp()->sameTree(samep->castRefDType()->skipRefp()); }
    virtual void dump(ostream& str=cout);
    virtual string name() const { return m_name; }
    virtual AstBasicDType* basicp() const { return defp() ? defp()->basicp() : NULL; }
    virtual AstNodeDType* skipRefp() const {
	// Skip past both the Ref and the Typedef
	if (defp()) return defp()->skipRefp();
	else { v3fatalSrc("Typedef not linked"); return NULL; }
    }
    virtual int widthAlignBytes() const { return dtypeSkipRefp()->widthAlignBytes(); }
    virtual int widthTotalBytes() const { return dtypeSkipRefp()->widthTotalBytes(); }
    void name(const string& flag) { m_name = flag; }
    AstNodeDType* dtypep() const {
	if (defp()) return defp();
	else { v3fatalSrc("Typedef not linked"); return NULL; }
    }
    AstNodeDType* dtypeSkipRefp() const { return defp()->skipRefp(); }	// op1 = Range of variable
    AstNodeDType* defp() const { return m_defp; }
    void defp(AstNodeDType* nodep) { m_defp=nodep; }
    AstPackage* packagep() const { return m_packagep; }
    void packagep(AstPackage* nodep) { m_packagep=nodep; }
};

struct AstEnumItem : public AstNode {
private:
    string	m_name;
public:
    // Parents: ENUM
    AstEnumItem(FileLine* fl, const string& name, AstNode* rangep, AstNode* initp)
	: AstNode(fl), m_name(name)
	{ addNOp1p(rangep); addNOp2p(initp); }
    ASTNODE_NODE_FUNCS(EnumItem, ENUMITEM)
    virtual string name() const { return m_name; }
    virtual bool maybePointedTo() const { return true; }
    void name(const string& flag) { m_name = flag; }
    AstRange* rangep() const { return op1p()->castRange(); } // op1 = Range for name appending
    void rangep(AstNode* nodep) { addOp1p(nodep); }
    AstNode* valuep() const { return op2p(); } // op2 = Value
    void valuep(AstNode* nodep) { addOp2p(nodep); }
};

struct AstEnumItemRef : public AstNodeMath {
private:
    AstEnumItem* m_itemp;	// [AfterLink] Pointer to item
    AstPackage*	m_packagep;	// Package hierarchy
public:
    AstEnumItemRef(FileLine* fl, AstEnumItem* itemp, AstPackage* packagep)
	: AstNodeMath(fl), m_itemp(itemp), m_packagep(packagep) {
	if (m_itemp) widthSignedFrom(m_itemp);
    }
    ASTNODE_NODE_FUNCS(EnumItemRef, ENUMITEMREF)
    virtual void dump(ostream& str);
    virtual string name() const { return itemp()->name(); }
    virtual bool broken() const { return !itemp(); }
    virtual int instrCount() const { return 0; }
    virtual void cloneRelink() { if (m_itemp->clonep()) m_itemp = m_itemp->clonep()->castEnumItem(); }
    virtual bool same(AstNode* samep) const {
	return itemp()==samep->castEnumItemRef()->itemp(); }
    AstEnumItem* itemp() const { return m_itemp; }
    virtual string emitVerilog() { V3ERROR_NA; return ""; }  // Implemented specially
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool cleanOut() { return true; }
    AstPackage* packagep() const { return m_packagep; }
    void packagep(AstPackage* nodep) { m_packagep=nodep; }
};

struct AstEnumDType : public AstNodeDType {
    // Parents: TYPEDEF/MODULE
    // Children: ENUMVALUEs
    AstEnumDType(FileLine* fl, AstNodeDType* dtp, AstNode* itemsp)
	: AstNodeDType(fl)
	{ setOp1p(dtp); addNOp2p(itemsp); }
    ASTNODE_NODE_FUNCS(EnumDType, ENUMDTYPE)
    AstNodeDType* dtypep() const { return op1p()->castNodeDType(); } // op1 = Data type
    void dtypep(AstNodeDType* nodep) { setOp1p(nodep); }
    AstEnumItem* itemsp() const { return op2p()->castEnumItem(); } // op2 = AstEnumItem's
    void addValuesp(AstNode* nodep) { addOp2p(nodep); }
    // METHODS
    virtual AstBasicDType* basicp() const { return dtypep()->basicp(); }  // (Slow) recurse down to find basic data type
    virtual AstNodeDType* skipRefp() const { return dtypep()->skipRefp(); }
    virtual int widthAlignBytes() const { return dtypep()->widthAlignBytes(); }
    virtual int widthTotalBytes() const { return dtypep()->widthTotalBytes(); }
};

//######################################################################

struct AstArraySel : public AstNodeSel {
    // Parents: math|stmt
    // Children: varref|arraysel, math
private:
    unsigned m_start;
    unsigned m_length;
    void init(AstNode* fromp) {
	if (fromp) widthSignedFrom(fromp);
    }
public:
    AstArraySel(FileLine* fl, AstNode* fromp, AstNode* bitp)
	:AstNodeSel(fl, fromp, bitp), m_start(0), m_length(1) {
	init(fromp);
    }
    AstArraySel(FileLine* fl, AstNode* fromp, int bit)
	:AstNodeSel(fl, fromp, new AstConst(fl,bit)), m_start(0), m_length(1) {
	init(fromp);
    }
    ASTNODE_NODE_FUNCS(ArraySel, ARRAYSEL)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) {
	V3ERROR_NA; /* How can from be a const? */ }
    virtual string emitVerilog() { return "%k(%l%f[%r])"; }
    virtual string emitC() { return "%li%k[%ri]"; }
    virtual bool cleanOut() { return true; }
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
    virtual int instrCount() const { return widthInstrs(); }
    unsigned length() const { return m_length; }
    void     length(unsigned length) { m_length = length; }
    void     start(unsigned start) { m_start = start; }
    unsigned start() const { return m_start; }
    // Special operators
    static int dimension(AstNode* nodep); ///< How many dimensions is this reference from the base variable?
    static AstNode* baseFromp(AstNode* nodep);	///< What is the base variable (or const) this dereferences?
    virtual void dump(ostream& str);
};

struct AstWordSel : public AstNodeSel {
    // Select a single word from a multi-word wide value
    AstWordSel(FileLine* fl, AstNode* fromp, AstNode* bitp)
	:AstNodeSel(fl, fromp, bitp) {
	dtypeChgUInt32(); // Always used on IData arrays so returns word entities
    }
    ASTNODE_NODE_FUNCS(WordSel, WORDSEL)
    virtual void numberOperate(V3Number& out, const V3Number& from, const V3Number& bit) { V3ERROR_NA; }
    virtual string emitVerilog() { return "%k(%l%f[%r])"; }
    virtual string emitC() { return "%li[%ri]"; } // Not %k, as usually it's a small constant rhsp
    virtual bool cleanOut() { return true; }
    virtual bool cleanLhs() { return true; } virtual bool cleanRhs() { return true; }
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
};

struct AstSelExtract : public AstNodePreSel {
    // Range extraction, gets replaced with AstSel
    AstSelExtract(FileLine* fl, AstNode* fromp, AstNode* msbp, AstNode* lsbp)
	: AstNodePreSel(fl, fromp, msbp, lsbp) {}
    ASTNODE_NODE_FUNCS(SelExtract, SELEXTRACT)
    AstNode*	msbp() const { return rhsp(); }
    AstNode*	lsbp() const { return thsp(); }
};

struct AstSelBit : public AstNodePreSel {
    // Single bit range extraction, perhaps with non-constant selection or array selection
    // Gets replaced during link with AstArraySel or AstSel
    AstSelBit(FileLine* fl, AstNode* fromp, AstNode* bitp)
	:AstNodePreSel(fl, fromp, bitp, NULL) {
	if (v3Global.assertDTypesResolved()) { v3fatalSrc("not coded to create after dtypes resolved"); }
    }
    ASTNODE_NODE_FUNCS(SelBit, SELBIT)
    AstNode*	bitp() const { return rhsp(); }
};

struct AstSelPlus : public AstNodePreSel {
    // +: range extraction, perhaps with non-constant selection
    // Gets replaced during link with AstSel
    AstSelPlus(FileLine* fl, AstNode* fromp, AstNode* bitp, AstNode* widthp)
	:AstNodePreSel(fl, fromp, bitp, widthp) {}
    ASTNODE_NODE_FUNCS(SelPlus, SELPLUS)
    AstNode*	bitp() const { return rhsp(); }
    AstNode*	widthp() const { return thsp(); }
};

struct AstSelMinus : public AstNodePreSel {
    // -: range extraction, perhaps with non-constant selection
    // Gets replaced during link with AstSel
    AstSelMinus(FileLine* fl, AstNode* fromp, AstNode* bitp, AstNode* widthp)
	:AstNodePreSel(fl, fromp, bitp, widthp) {}
    ASTNODE_NODE_FUNCS(SelMinus, SELMINUS)
    AstNode*	bitp() const { return rhsp(); }
    AstNode*	widthp() const { return thsp(); }
};

struct AstSel : public AstNodeTriop {
    // Multiple bit range extraction
    // Parents: math|stmt
    // Children: varref|arraysel, math, constant math
    AstSel(FileLine* fl, AstNode* fromp, AstNode* lsbp, AstNode* widthp)
	:AstNodeTriop(fl, fromp, lsbp, widthp) {
	if (widthp->castConst()) {
	    width(widthp->castConst()->toUInt(), widthp->castConst()->toUInt());
	}
    }
    AstSel(FileLine* fl, AstNode* fromp, int lsb, int bitwidth)
	:AstNodeTriop(fl, fromp,
		      new AstConst(fl,lsb), new AstConst(fl,bitwidth)) {
	width(bitwidth,bitwidth);
    }
    ASTNODE_NODE_FUNCS(Sel, SEL)
    virtual void numberOperate(V3Number& out, const V3Number& from, const V3Number& bit, const V3Number& width) {
	out.opSel(from, bit.toUInt()+width.toUInt()-1, bit.toUInt()); }
    virtual string emitVerilog() { V3ERROR_NA; return ""; }  // Implemented specially
    virtual string emitC() {
	return this->widthp()->isOne()
	    ? "VL_BITSEL_%nq%lq%rq%tq(%nw,%lw,%rw,%tw, %P, %li, %ri)"
	    : "VL_SEL_%nq%lq%rq%tq(%nw,%lw,%rw,%tw, %P, %li, %ri, %ti)"; }
    virtual bool cleanOut() { return false; }
    virtual bool cleanLhs() { return true;} virtual bool cleanRhs() {return true;}
    virtual bool cleanThs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual bool sizeMattersThs() {return false;}
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode*) const { return true; }
    virtual int instrCount() const { return widthInstrs()*(lsbp()->castConst()?3:10); }
    AstNode* fromp()		const { return op1p()->castNode(); }	// op1 = Extracting what (NULL=TBD during parsing)
    AstNode* lsbp()		const { return op2p()->castNode(); }	// op2 = Msb selection expression
    AstNode* widthp()		const { return op3p()->castNode(); }	// op3 = Width
    int		widthConst() const { return widthp()->castConst()->toSInt(); }
    int		lsbConst()   const { return lsbp()->castConst()->toSInt(); }
    int		msbConst()   const { return lsbConst()+widthConst()-1; }
};

struct AstVar : public AstNode {
    // A variable (in/out/wire/reg/param) inside a module
private:
    string	m_name;		// Name of variable
    AstVarType	m_varType;	// Type of variable
    bool	m_input:1;	// Input or inout
    bool	m_output:1;	// Output or inout
    bool	m_tristate:1;	// Inout or triwire or trireg
    bool	m_primaryIO:1;	// In/out to top level (or directly assigned from same)
    bool	m_sc:1;		// SystemC variable
    bool	m_scClocked:1;	// SystemC sc_clk<> needed
    bool	m_scSensitive:1;// SystemC sensitive() needed
    bool	m_sigPublic:1;	// User C code accesses this signal or is top signal
    bool	m_sigModPublic:1;// User C code accesses this signal and module
    bool	m_sigUserRdPublic:1; // User C code accesses this signal, read only
    bool	m_sigUserRWPublic:1; // User C code accesses this signal, read-write
    bool	m_usedClock:1;	// Signal used as a clock
    bool	m_usedParam:1;	// Parameter is referenced (on link; later signals not setup)
    bool	m_usedLoopIdx:1; // Variable subject of for unrolling
    bool	m_funcLocal:1;	// Local variable for a function
    bool	m_funcReturn:1;	// Return variable for a function
    bool	m_attrClockEn:1;// User clock enable attribute
    bool	m_attrScBv:1; // User force bit vector attribute
    bool	m_attrIsolateAssign:1;// User isolate_assignments attribute
    bool	m_attrSFormat:1;// User sformat attribute
    bool	m_fileDescr:1;	// File descriptor
    bool	m_isConst:1;	// Table contains constant data
    bool	m_isStatic:1;	// Static variable
    bool	m_trace:1;	// Trace this variable

    void	init() {
	m_input=false; m_output=false; m_tristate=false;
	m_primaryIO=false;
	m_sc=false; m_scClocked=false; m_scSensitive=false;
	m_usedClock=false; m_usedParam=false; m_usedLoopIdx=false;
	m_sigPublic=false; m_sigModPublic=false; m_sigUserRdPublic=false; m_sigUserRWPublic=false;
	m_funcLocal=false; m_funcReturn=false;
	m_attrClockEn=false; m_attrScBv=false; m_attrIsolateAssign=false; m_attrSFormat=false;
	m_fileDescr=false; m_isConst=false; m_isStatic=false;
	m_trace=false;
    }
public:
    AstVar(FileLine* fl, AstVarType type, const string& name, AstNodeDType* dtp)
	:AstNode(fl)
	, m_name(name) {
	init();
	combineType(type); setOp1p(dtp);
	if (dtp && dtp->basicp()) {
	    numericFrom(dtp);
	    width(dtp->basicp()->width(), 0);
	} else width(1, 0);
    }
    AstVar(FileLine* fl, AstVarType type, const string& name, AstLogicPacked, int wantwidth)
	:AstNode(fl)
	, m_name(name) {
	init();
	combineType(type);
	setOp1p(new AstBasicDType(fl, AstLogicPacked(), wantwidth));
	width(wantwidth,0);
    }
    AstVar(FileLine* fl, AstVarType type, const string& name, AstBitPacked, int wantwidth)
	:AstNode(fl)
	, m_name(name) {
	init();
	combineType(type);
	setOp1p(new AstBasicDType(fl, AstBitPacked(), wantwidth));
	width(wantwidth,0);
    }
    AstVar(FileLine* fl, AstVarType type, const string& name, AstVar* examplep)
	:AstNode(fl)
	, m_name(name) {
	init();
	combineType(type);
	if (examplep->dtypep()) {
	    setOp1p(examplep->dtypep()->cloneTree(true));
	}
	numericFrom(examplep);
	width(examplep->width(), examplep->widthMin());
    }
    ASTNODE_NODE_FUNCS(Var, VAR)
    virtual void dump(ostream& str);
    virtual string name()	const { return m_name; }		// * = Var name
    virtual bool maybePointedTo() const { return true; }
    virtual bool broken() const { return !dtypep(); }
    AstVarType	varType()	const { return m_varType; }		// * = Type of variable
    void varType2Out() { m_tristate=0; m_input=0; m_output=1; }
    void varType2In() {  m_tristate=0; m_input=1; m_output=0; }
    string	scType() const;	  // Return SysC type: bool, uint32_t, uint64_t, sc_bv
    string	cPubArgType(bool named, bool forReturn) const;  // Return C /*public*/ type for argument: bool, uint32_t, uint64_t, etc.
    string	dpiArgType(bool named, bool forReturn) const;  // Return DPI-C type for argument
    string	vlArgType(bool named, bool forReturn) const;  // Return Verilator internal type for argument: CData, SData, IData, WData
    string	vlEnumType() const;  // Return VerilatorVarType: VLVT_UINT32, etc
    string	vlEnumDir() const;  // Return VerilatorVarDir: VLVD_INOUT, etc
    void	combineType(AstVarType type);
    AstNodeDType* dtypep() 	const { return op1p()->castNodeDType(); }	// op1 = Range of variable
    AstNodeDType* dtypeSkipRefp() const { return dtypep()->skipRefp(); }	// op1 = Range of variable (Note don't need virtual - AstVar isn't a NodeDType)
    AstBasicDType* basicp() const { return dtypep()->basicp(); }  // (Slow) recurse down to find basic data type (Note don't need virtual - AstVar isn't a NodeDType)
    AstNode* 	valuep() const { return op3p()->castNode(); } // op3 = Initial value that never changes (static const)
    void	valuep(AstNode* nodep) { setOp3p(nodep); }    // It's valuep, not constp, as may be more complicated than an AstConst
    void	addAttrsp(AstNode* nodep) { addNOp4p(nodep); }
    AstNode*	attrsp()	const { return op4p()->castNode(); }	// op4 = Attributes during early parse
    bool	hasSimpleInit()	const { return (op3p() && !op3p()->castInitArray()); }
    void	dtypep(AstNodeDType* nodep) { setOp1p(nodep); }
    void	attrClockEn(bool flag) { m_attrClockEn = flag; }
    void	attrFileDescr(bool flag) { m_fileDescr = flag; }
    void	attrScClocked(bool flag) { m_scClocked = flag; }
    void	attrScBv(bool flag) { m_attrScBv = flag; }
    void	attrIsolateAssign(bool flag) { m_attrIsolateAssign = flag; }
    void	attrSFormat(bool flag) { m_attrSFormat = flag; }
    void	usedClock(bool flag) { m_usedClock = flag; }
    void	usedParam(bool flag) { m_usedParam = flag; }
    void	usedLoopIdx(bool flag) { m_usedLoopIdx = flag; }
    void	sigPublic(bool flag) { m_sigPublic = flag; }
    void	sigModPublic(bool flag) { m_sigModPublic = flag; }
    void	sigUserRdPublic(bool flag) { m_sigUserRdPublic = flag; if (flag) sigPublic(true); }
    void	sigUserRWPublic(bool flag) { m_sigUserRWPublic = flag; if (flag) sigUserRdPublic(true); }
    void	sc(bool flag) { m_sc = flag; }
    void	scSensitive(bool flag) { m_scSensitive = flag; }
    void	primaryIO(bool flag) { m_primaryIO = flag; }
    void	isConst(bool flag) { m_isConst = flag; }
    void	isStatic(bool flag) { m_isStatic = flag; }
    void	funcLocal(bool flag) { m_funcLocal = flag; }
    void	funcReturn(bool flag) { m_funcReturn = flag; }
    void	trace(bool flag) { m_trace=flag; }
    // METHODS
    virtual void name(const string& name) { m_name = name; }
    bool	isInput() const { return m_input; }
    bool	isOutput() const { return m_output; }
    bool	isInOnly() const { return m_input && !m_output; }
    bool	isOutOnly() const { return m_output && !m_input; }
    bool	isInout() const { return m_input && m_output; }
    bool	isTristate() const  { return m_tristate; }
    bool	isPrimaryIO() const { return m_primaryIO; }
    bool	isPrimaryIn() const { return isPrimaryIO() && isInput(); }
    bool	isIO() const  { return (m_input||m_output); }
    bool	isSignal() const  { return (varType()==AstVarType::WIRE || varType()==AstVarType::IMPLICITWIRE
					    || varType()==AstVarType::VAR); }
    bool	isTemp() const { return (varType()==AstVarType::BLOCKTEMP || varType()==AstVarType::MODULETEMP
					 || varType()==AstVarType::STMTTEMP || varType()==AstVarType::XTEMP); }
    bool	isToggleCoverable() const  { return ((isIO() || isSignal())
						     && (isIO() || isBitLogic())
						     // Wrapper would otherwise duplicate wrapped module's coverage
						     && !isSc() && !isPrimaryIO() && !isConst()); }
    bool	isStatementTemp() const { return (varType()==AstVarType::STMTTEMP); }
    bool	isMovableToBlock() const { return (varType()==AstVarType::BLOCKTEMP || isFuncLocal()); }
    bool	isXTemp() const { return (varType()==AstVarType::XTEMP); }
    bool	isParam() const { return (varType()==AstVarType::LPARAM || varType()==AstVarType::GPARAM); }
    bool	isGParam() const { return (varType()==AstVarType::GPARAM); }
    bool	isGenVar() const { return (varType()==AstVarType::GENVAR); }
    bool	isBitLogic() const { AstBasicDType* bdtypep = basicp(); return bdtypep && bdtypep->isBitLogic(); }
    bool	isUsedClock() const { return m_usedClock; }
    bool	isUsedParam() const { return m_usedParam; }
    bool	isUsedLoopIdx() const { return m_usedLoopIdx; }
    bool	isSc() const { return m_sc; }
    bool	isScQuad() const;
    bool	isScBv() const;
    bool	isScSensitive() const { return m_scSensitive; }
    bool	isSigPublic()  const;
    bool	isSigModPublic() const { return m_sigModPublic; }
    bool	isSigUserRdPublic() const { return m_sigUserRdPublic; }
    bool	isSigUserRWPublic() const { return m_sigUserRWPublic; }
    bool	isTrace() const { return m_trace; }
    bool	isConst() const { return m_isConst; }
    bool	isStatic() const { return m_isStatic; }
    bool	isFuncLocal() const { return m_funcLocal; }
    bool	isFuncReturn() const { return m_funcReturn; }
    bool	attrClockEn() const { return m_attrClockEn; }
    bool	attrScBv() const { return m_attrScBv; }
    bool	attrFileDescr() const { return m_fileDescr; }
    bool	attrScClocked() const { return m_scClocked; }
    bool	attrSFormat() const { return m_attrSFormat; }
    bool	attrIsolateAssign() const { return m_attrIsolateAssign; }
    virtual string verilogKwd() const;
    void	propagateAttrFrom(AstVar* fromp) {
	// This is getting connected to fromp; keep attributes
	// Note the method below too
	if (fromp->attrClockEn()) attrClockEn(true);
	if (fromp->attrFileDescr()) attrFileDescr(true);
	if (fromp->attrIsolateAssign()) attrIsolateAssign(true);
    }
    bool	gateMultiInputOptimizable() const {
	// Ok to gate optimize; must return false if propagateAttrFrom would do anything
	return (!attrClockEn() && !isUsedClock());
    }
    void	combineType(AstVar* typevarp) {
	// This is same as typevarp (for combining input & reg decls)
	propagateAttrFrom(typevarp);
	combineType(typevarp->varType());
	if (typevarp->isSigPublic()) sigPublic(true);
	if (typevarp->isSigModPublic()) sigModPublic(true);
	if (typevarp->isSigUserRdPublic()) sigUserRdPublic(true);
	if (typevarp->isSigUserRWPublic()) sigUserRWPublic(true);
	if (typevarp->attrScClocked()) attrScClocked(true);
    }
    void	inlineAttrReset(const string& name) {
	m_input=m_output=false; m_name = name;
	if (varType()==AstVarType::INOUT) m_varType = AstVarType::TRIWIRE;
	if (varType()==AstVarType::INPUT || varType()==AstVarType::OUTPUT) m_varType = AstVarType::WIRE;
    }
};

struct AstDefParam : public AstNode {
    // A defparam assignment
    // Parents: MODULE
    // Children: math
private:
    string	m_name;		// Name of variable getting set
    string	m_path;		// Dotted cellname to set parameter of
public:
    AstDefParam(FileLine* fl, const string& path, const string& name, AstNode* rhsp)
	: AstNode(fl) {
	setOp1p(rhsp);
	m_name = name;
	m_path = path;
    }
    virtual string name()	const { return m_name; }		// * = Scope name
    ASTNODE_NODE_FUNCS(DefParam, DEFPARAM)
    virtual bool cleanRhs() { return true; }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode*) const { return true; }
    AstNode* rhsp()		const { return op1p()->castNode(); }	// op1 = Assign from
    string   path()		const { return m_path; }
};

struct AstImplicit : public AstNode {
    // Create implicit wires and do nothing else, for gates that are ignored
    // Parents: MODULE
    AstImplicit(FileLine* fl, AstNode* exprsp)
	: AstNode(fl) {
	addNOp1p(exprsp);
    }
    ASTNODE_NODE_FUNCS(Implicit, IMPLICIT)
    AstNode* exprsp() const { return op1p()->castNode(); }	// op1 = Assign from
};

struct AstScope : public AstNode {
    // A particular usage of a cell
    // Parents: MODULE
    // Children: NODEBLOCK
private:
    // An AstScope->name() is special: . indicates an uninlined scope, __DOT__ an inlined scope
    string	m_name;		// Name
    AstScope*	m_aboveScopep;	// Scope above this one in the hierarchy (NULL if top)
    AstCell*	m_aboveCellp;	// Cell above this in the hierarchy (NULL if top)
    AstNodeModule*	m_modp;		// Module scope corresponds to
public:
    AstScope(FileLine* fl, AstNodeModule* modp, const string& name,
	     AstScope* aboveScopep, AstCell* aboveCellp)
	:AstNode(fl)
	,m_name(name) ,m_aboveScopep(aboveScopep) ,m_aboveCellp(aboveCellp), m_modp(modp) {}
    ASTNODE_NODE_FUNCS(Scope, SCOPE)
    virtual void cloneRelink();
    virtual bool broken() const;
    virtual bool maybePointedTo() const { return true; }
    virtual string name()	const { return m_name; }		// * = Scope name
    virtual void name(const string& name) { m_name = name; }
    string nameDotless() const;
    string nameVlSym() const { return (((string)"vlSymsp->") + nameDotless()); }
    AstNodeModule* modp()		const { return m_modp; }
    void addVarp(AstNode* nodep) { addOp1p(nodep); }
    AstNode* varsp()		const { return op1p()->castNode(); }	// op1 = AstVarScope's
    void addActivep(AstNode* nodep) { addOp2p(nodep); }
    AstNode* blocksp()		const { return op2p()->castNode(); }	// op2 = Block names
    void addFinalClkp(AstNode* nodep) { addOp3p(nodep); }
    AstNode* finalClksp()		const { return op3p()->castNode(); }	// op3 = Final assigns for clock correction
    AstScope* aboveScopep() const { return m_aboveScopep; }
    AstCell* aboveCellp() const { return m_aboveCellp; }
    bool isTop() const { return aboveScopep()==NULL; }  // At top of hierarchy
};

struct AstTopScope : public AstNode {
    // In the top level netlist, a complete scope tree
    // There may be two of these, when we support "rare" and "usual" splitting
    // Parents: topMODULE
    // Children: SCOPEs
    AstTopScope(FileLine* fl, AstScope* ascopep)
	:AstNode(fl)
	{addNOp2p(ascopep);}
    ASTNODE_NODE_FUNCS(TopScope, TOPSCOPE)
    AstNode*	stmtsp() 	const { return op1p()->castNode(); }
    void addStmtsp(AstNode* nodep) { addOp1p(nodep); }
    AstScope* scopep()		const { return op2p()->castScope(); }	// op1 = AstVarScope's
};

struct AstVarScope : public AstNode {
    // A particular scoped usage of a variable
    // That is, as a module is used under multiple cells, we get a different varscope for each var in the module
    // Parents: MODULE
    // Children: none
private:
    AstScope*	m_scopep;	// Scope variable is underneath
    AstVar*	m_varp;		// [AfterLink] Pointer to variable itself
    bool	m_circular:1;	// Used in circular ordering dependency, need change detect
public:
    AstVarScope(FileLine* fl, AstScope* scopep, AstVar* varp)
	:AstNode(fl)
	, m_scopep(scopep), m_varp(varp) {
	m_circular = false;
	widthSignedFrom(varp);
    }
    ASTNODE_NODE_FUNCS(VarScope, VARSCOPE)
    virtual void cloneRelink() { if (m_varp && m_varp->clonep()) {
	m_varp = m_varp->clonep()->castVar();
	UASSERT(m_scopep->clonep(), "No clone cross link: "<<this);
	m_scopep = m_scopep->clonep()->castScope();
    }}
    virtual bool broken() const { return ( (m_varp && !m_varp->brokeExists())
					   || (m_scopep && !m_scopep->brokeExists())); }
    virtual bool maybePointedTo() const { return true; }
    virtual string name() const {return scopep()->name()+"->"+varp()->name();}	// * = Var name
    virtual void dump(ostream& str);
    AstVar*	varp() const { return m_varp; }			// [After Link] Pointer to variable
    AstScope*	scopep() const { return m_scopep; }		// Pointer to scope it's under
    AstNode*	valuep()	const { return op1p(); }	// op1 = Calculation of value of variable, NULL=complicated
    void	valuep(AstNode* valuep) { addOp1p(valuep); }
    bool	isCircular() const { return m_circular; }
    void	circular(bool flag) { m_circular = flag; }
};

struct AstVarRef : public AstNodeVarRef {
    // A reference to a variable (lvalue or rvalue)
    AstVarRef(FileLine* fl, const string& name, bool lvalue)
	:AstNodeVarRef(fl, name, NULL, lvalue) {}
    AstVarRef(FileLine* fl, AstVar* varp, bool lvalue)  // This form only allowed post-link
	:AstNodeVarRef(fl, varp->name(), varp, lvalue) {}		// because output/wire compression may lead to deletion of AstVar's
    AstVarRef(FileLine* fl, AstVarScope* varscp, bool lvalue)  // This form only allowed post-link
	:AstNodeVarRef(fl, varscp->varp()->name(), varscp->varp(), lvalue) {	// because output/wire compression may lead to deletion of AstVar's
	varScopep(varscp);
    }
    ASTNODE_NODE_FUNCS(VarRef, VARREF)
    virtual void dump(ostream& str);
    virtual V3Hash sameHash() const { return V3Hash(V3Hash(varp()->name()),V3Hash(hiername())); }
    virtual bool same(AstNode* samep) const {
	if (varScopep()) return varScopep()==samep->castVarRef()->varScopep();
	else return (hiername()==samep->castVarRef()->hiername()
		     && varp()->name()==samep->castVarRef()->varp()->name()); }
    virtual int instrCount() const { return widthInstrs()*(lvalue()?1:instrCountLd()); }
    virtual string emitVerilog() { V3ERROR_NA; return ""; }  // Implemented specially
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool cleanOut() { return true; }
};

struct AstVarXRef : public AstNodeVarRef {
    // A VarRef to something in another module before AstScope.
    // Includes pin on a cell, as part of a ASSIGN statement to connect I/Os until AstScope
private:
    string	m_dotted;	// Scope name to connected to
    string	m_inlinedDots;	// Dotted hierarchy flattened out
public:
    AstVarXRef(FileLine* fl, const string& name, const string& dotted, bool lvalue)
	:AstNodeVarRef(fl, name, NULL, lvalue)
	, m_dotted(dotted) { }
    AstVarXRef(FileLine* fl, AstVar* varp, const string& dotted, bool lvalue)
	:AstNodeVarRef(fl, varp->name(), varp, lvalue)
	, m_dotted(dotted) {
    }
    ASTNODE_NODE_FUNCS(VarXRef, VARXREF)
    virtual void dump(ostream& str);
    string	dotted() const { return m_dotted; }
    string	prettyDotted() const { return prettyName(dotted()); }
    string	inlinedDots() const { return m_inlinedDots; }
    void	inlinedDots(const string& flag) { m_inlinedDots = flag; }
    virtual string emitVerilog() { V3ERROR_NA; return ""; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool cleanOut() { return true; }
    virtual int instrCount() const { return widthInstrs(); }
    virtual V3Hash sameHash() const { return V3Hash(V3Hash(varp()),V3Hash(dotted())); }
    virtual bool same(AstNode* samep) const {
	return (hiername()==samep->castVarXRef()->hiername()
		&& varp()==samep->castVarXRef()->varp()
	        && name()==samep->castVarXRef()->name()
		&& dotted()==samep->castVarXRef()->dotted()); }
};

struct AstPin : public AstNode {
    // A pin on a cell
private:
    int		m_pinNum;	// Pin number
    string	m_name;		// Pin name, or "" for number based interconnect
    AstVar*	m_modVarp;	// Input/output this pin connects to on submodule.
    bool	m_svImplicit;	// Pin is SystemVerilog .name'ed
public:
    AstPin(FileLine* fl, int pinNum, const string& name, AstNode* exprp)
	:AstNode(fl)
	,m_name(name), m_svImplicit(false) {
	m_pinNum = pinNum;
	m_modVarp = NULL;
	setNOp1p(exprp);
	if (exprp) widthSignedFrom(exprp);
    }
    AstPin(FileLine* fl, int pinNum, AstVarRef* varname, AstNode* exprp)
	:AstNode(fl), m_svImplicit(false) {
	m_name = varname->name();
	m_pinNum = pinNum;
	m_modVarp = NULL;
	setNOp1p(exprp);
	if (exprp) widthSignedFrom(exprp);
    }
    ASTNODE_NODE_FUNCS(Pin, PIN)
    virtual void dump(ostream& str);
    virtual bool broken() const { return (m_modVarp && !m_modVarp->brokeExists()); }
    virtual string name()	const { return m_name; }		// * = Pin name, ""=go by number
    virtual void name(const string& name) { m_name = name; }
    bool	dotStar()	const { return name() == ".*"; }	// Special fake name for .* connections until linked
    int		pinNum()	const { return m_pinNum; }
    void	exprp(AstNode* nodep) { addOp1p(nodep); }
    AstNode*	exprp()		const { return op1p()->castNode(); }	// op1 = Expression connected to pin, NULL if unconnected
    AstVar*	modVarp()	const { return m_modVarp; }		// [After Link] Pointer to variable
    void  	modVarp(AstVar* varp) { m_modVarp=varp; }
    bool	svImplicit()	const { return m_svImplicit; }
    void        svImplicit(bool flag) { m_svImplicit=flag; }
};

struct AstModule : public AstNodeModule {
    // A module declaration
    AstModule(FileLine* fl, const string& name)
	: AstNodeModule (fl,name) {}
    ASTNODE_NODE_FUNCS(Module, MODULE)
    virtual string verilogKwd() const { return "module"; }
};

struct AstNotFoundModule : public AstNodeModule {
    // A missing module declaration
    AstNotFoundModule(FileLine* fl, const string& name)
	: AstNodeModule (fl,name) {}
    ASTNODE_NODE_FUNCS(NotFoundModule, NOTFOUNDMODULE)
    virtual string verilogKwd() const { return "/*not-found-*/ module"; }
};

struct AstPackage : public AstNodeModule {
    // A package declaration
    AstPackage(FileLine* fl, const string& name)
	: AstNodeModule (fl,name) {}
    ASTNODE_NODE_FUNCS(Package, PACKAGE)
    virtual string verilogKwd() const { return "package"; }
    static string dollarUnitName() { return AstNode::encodeName("$unit"); }
    bool isDollarUnit() const { return name() == dollarUnitName(); }
};

struct AstPrimitive : public AstNodeModule {
    // A primitive declaration
    AstPrimitive(FileLine* fl, const string& name)
	: AstNodeModule (fl,name) {}
    ASTNODE_NODE_FUNCS(Primitive, PRIMITIVE)
    virtual string verilogKwd() const { return "primitive"; }
};

struct AstPackageImport : public AstNode {
private:
    // A package import declaration
    string	m_name;
    AstPackage*	m_packagep;	// Package hierarchy
public:
    AstPackageImport(FileLine* fl, AstPackage* packagep, const string& name)
	: AstNode (fl), m_name(name), m_packagep(packagep) {}
    ASTNODE_NODE_FUNCS(PackageImport, PACKAGEIMPORT)
    virtual bool broken() const { return (!m_packagep || !m_packagep->brokeExists()); }
    virtual void cloneRelink() { if (m_packagep && m_packagep->clonep()) m_packagep = m_packagep->clonep()->castPackage(); }
    virtual void dump(ostream& str);
    virtual string name() const { return m_name; }
    AstPackage* packagep() const { return m_packagep; }
    void packagep(AstPackage* nodep) { m_packagep=nodep; }
};

struct AstCell : public AstNode {
    // A instantiation cell or interface call (don't know which until link)
private:
    string	m_name;		// Cell name
    string	m_origName;	// Original name before dot addition
    string	m_modName;	// Module the cell instances
    AstNodeModule*	m_modp;		// [AfterLink] Pointer to module instanced
public:
    AstCell(FileLine* fl, const string& instName, const string& modName,
	    AstPin* pinsp, AstPin* paramsp, AstRange* rangep)
	: AstNode(fl)
	, m_name(instName), m_origName(instName), m_modName(modName)
	, m_modp(NULL) {
	addNOp1p(pinsp); addNOp2p(paramsp); setNOp3p(rangep); }
    ASTNODE_NODE_FUNCS(Cell, CELL)
    // No cloneRelink, we presume cloneee's want the same module linkages
    virtual void dump(ostream& str);
    virtual bool broken() const { return (m_modp && !m_modp->brokeExists()); }
    virtual bool maybePointedTo() const { return true; }
    // ACCESSORS
    virtual string name()	const { return m_name; }		// * = Cell name
    virtual void name(const string& name) { m_name = name; }
    string origName()		const { return m_origName; }		// * = Original name
    void origName(const string& name) 	{ m_origName = name; }
    string modName()		const { return m_modName; }		// * = Instance name
    void modName(const string& name)	{ m_modName = name; }
    AstPin* pinsp()		const { return op1p()->castPin(); }	// op1 = List of cell ports
    AstPin* paramsp()		const { return op2p()->castPin(); }	// op2 = List of parameter #(##) values
    AstRange* rangep()		const { return op3p()->castRange(); }	// op3 = Range of arrayed instants (NULL=not ranged)
    AstNodeModule* modp()		const { return m_modp; }		// [AfterLink] = Pointer to module instantiated
    void addPinsp(AstPin* nodep) { addOp1p(nodep); }
    void addParamsp(AstPin* nodep) { addOp2p(nodep); }
    void modp(AstNodeModule* nodep)	{ m_modp = nodep; }
};

struct AstCellInline : public AstNode {
    // A instantiation cell that was removed by inlining
    // For communication between V3Inline and V3LinkDot only
    // Children: When 2 levels inlined, other CellInline under this
private:
    string	m_name;		// Cell name, possibly {a}__DOT__{b}...
    string	m_origModName;	// Original name of the module, ignoring name() changes, for dot lookup
public:
    AstCellInline(FileLine* fl, const string& name, const string& origModName)
	: AstNode(fl)
	, m_name(name), m_origModName(origModName) {}
    ASTNODE_NODE_FUNCS(CellInline, CELLINLINE)
    virtual void dump(ostream& str);
    // ACCESSORS
    virtual string name()	const { return m_name; }		// * = Cell name
    string origModName()	const { return m_origModName; }		// * = modp()->origName() before inlining
    virtual void name(const string& name) { m_name = name; }
};

struct AstPort : public AstNode {
    // A port (in/out/inout) on a module
private:
    int		m_pinNum;	// Pin number
    string	m_name;		// Name of pin
public:
    AstPort(FileLine* fl, int pinnum, const string& name)
	:AstNode(fl)
	,m_pinNum(pinnum) ,m_name(name) {}
    ASTNODE_NODE_FUNCS(Port, PORT)
    virtual string name()	const { return m_name; }		// * = Port name
    int pinNum()		const { return m_pinNum; }		// * = Pin number, for order based instantiation
    AstNode* exprp()		const { return op1p()->castNode(); }	// op1 = Expression connected to port
};

//######################################################################

struct AstBegin : public AstNode {
    // A Begin/end named block, only exists shortly after parsing until linking
    // Parents: statement
    // Children: statements
private:
    string	m_name;		// Name of block
    bool	m_unnamed;	// Originally unnamed
    bool	m_hidden;	// Inserted by verilator, not user
public:
    // Node that simply puts name into the output stream
    AstBegin(FileLine* fileline, const string& name, AstNode* stmtsp)
	: AstNode(fileline)
	, m_name(name) {
	addNOp1p(stmtsp);
	m_unnamed = (name=="");
	m_hidden = false;
    }
    ASTNODE_NODE_FUNCS(Begin, BEGIN)
    virtual void dump(ostream& str);
    virtual string name()	const { return m_name; }		// * = Block name
    virtual void name(const string& name) { m_name = name; }
    // op1 = Statements
    AstNode*	stmtsp() 	const { return op1p()->castNode(); }	// op1 = List of statements
    void addStmtsp(AstNode* nodep) { addNOp1p(nodep); }
    AstNode*	flatsp() 	const { return op2p()->castNode(); }	// op2 = Statements that don't appear under new scope
    void addFlatsp(AstNode* nodep) { addNOp2p(nodep); }
    bool unnamed() const { return m_unnamed; }
    void hidden(bool flag) { m_hidden = flag; }
    bool hidden() const { return m_hidden; }
};

struct AstGenerate : public AstNode {
    // A Generate/end block
    // Parents: MODULE
    // Children: modItems
    AstGenerate(FileLine* fileline, AstNode* stmtsp)
	: AstNode(fileline) {
	addNOp1p(stmtsp);
    }
    ASTNODE_NODE_FUNCS(Generate, GENERATE)
    // op1 = Statements
    AstNode*	stmtsp() 	const { return op1p()->castNode(); }	// op1 = List of statements
    void addStmtp(AstNode* nodep) { addOp1p(nodep); }
};

struct AstParseRef : public AstNode {
    // A reference to a variable, function or task
    // We don't know which at parse time due to bison constraints
    // The link stages will replace this with AstVarRef, or AstTaskRef, etc.
    // Parents: math|stmt
    // Children: TEXT|DOT|SEL* (or expression under sel)
private:
    AstParseRefExp	m_expect;		// Type we think it should resolve to
public:
    AstParseRef(FileLine* fl, AstParseRefExp expect, AstNode* lhsp)
	:AstNode(fl), m_expect(expect) { setOp1p(lhsp); }
    ASTNODE_NODE_FUNCS(ParseRef, PARSEREF)
    virtual void dump(ostream& str);
    virtual V3Hash sameHash() const { return V3Hash(m_expect); }
    virtual bool same(AstNode* samep) const { return expect() == samep->castParseRef()->expect(); }
    virtual string emitVerilog() { V3ERROR_NA; return ""; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    AstParseRefExp expect() const { return m_expect; }
    // op1 = Components
    AstNode*	lhsp() 		const { return op1p(); }	// op1 = List of statements
};

struct AstDot : public AstNode {
    // A dot separating paths in an AstXRef, AstFuncRef or AstTaskRef
    // These are elimiated in the link stage
    AstDot(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
	:AstNode(fl) { setOp1p(lhsp); setOp2p(rhsp); }
    ASTNODE_NODE_FUNCS(Dot, DOT)
    virtual string emitVerilog() { V3ERROR_NA; return ""; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    AstNode* lhsp() const { return op1p(); }
    AstNode* rhsp() const { return op2p(); }
};

//######################################################################

struct AstTask : public AstNodeFTask {
    // A task inside a module
    AstTask(FileLine* fl, const string& name, AstNode* stmtp)
	:AstNodeFTask(fl, name, stmtp) {}
    ASTNODE_NODE_FUNCS(Task, TASK)
};

struct AstFunc : public AstNodeFTask {
    // A function inside a module
    AstFunc(FileLine* fl, const string& name, AstNode* stmtp, AstNode* fvarsp)
	:AstNodeFTask(fl, name, stmtp) {
	addNOp1p(fvarsp);
    }
    ASTNODE_NODE_FUNCS(Func, FUNC)
};

struct AstTaskRef : public AstNodeFTaskRef {
    // A reference to a task
    AstTaskRef(FileLine* fl, AstParseRef* namep, AstNode* pinsp)
	:AstNodeFTaskRef(fl, namep, pinsp) {}
    AstTaskRef(FileLine* fl, const string& name, AstNode* pinsp)
	:AstNodeFTaskRef(fl, name, pinsp) {}
    ASTNODE_NODE_FUNCS(TaskRef, TASKREF)
};

struct AstFuncRef : public AstNodeFTaskRef {
    // A reference to a function
    AstFuncRef(FileLine* fl, AstParseRef* namep, AstNode* pinsp)
	:AstNodeFTaskRef(fl, namep, pinsp) {}
    AstFuncRef(FileLine* fl, const string& name, AstNode* pinsp)
	:AstNodeFTaskRef(fl, name, pinsp) {}
    ASTNODE_NODE_FUNCS(FuncRef, FUNCREF)
};

struct AstDpiExport : public AstNode {
    // We could put an AstNodeFTaskRef instead of the verilog function name,
    // however we're not *calling* it, so that seems somehow wrong.
    // (Probably AstNodeFTaskRef should be renamed AstNodeFTaskCall and have-a AstNodeFTaskRef)
private:
    string	m_name;		// Name of function
    string	m_cname;	// Name of function on c side
public:
    AstDpiExport(FileLine* fl, const string& vname, const string& cname)
	:AstNode(fl), m_name(vname), m_cname(cname) { }
    ASTNODE_NODE_FUNCS(DpiExport, DPIEXPORT)
    virtual string name() const { return m_name; }
    virtual void name(const string& name) { m_name = name; }
    string cname() const { return m_cname; }
    void cname(const string& cname) { m_cname = cname; }
};

//######################################################################

struct AstSenItem : public AstNodeSenItem {
    // Parents:  SENTREE
    // Children: (optional) VARREF SENGATE
private:
    AstEdgeType	m_edgeType;		// Edge type
public:
    class Combo {};		// for creator type-overload selection
    class Initial {};		// for creator type-overload selection
    class Settle {};		// for creator type-overload selection
    class Never {};		// for creator type-overload selection
    AstSenItem(FileLine* fl, AstEdgeType edgeType, AstNodeVarRef* varrefp)
	: AstNodeSenItem(fl), m_edgeType(edgeType) {
	setOp1p(varrefp);
    }
    AstSenItem(FileLine* fl, AstEdgeType edgeType, AstParseRef* varrefp)
	: AstNodeSenItem(fl), m_edgeType(edgeType) {
	setOp1p(varrefp);
    }
    AstSenItem(FileLine* fl, Combo)
	: AstNodeSenItem(fl) {
	m_edgeType = AstEdgeType::ET_COMBO;
    }
    AstSenItem(FileLine* fl, Initial)
	: AstNodeSenItem(fl) {
	m_edgeType = AstEdgeType::ET_INITIAL;
    }
    AstSenItem(FileLine* fl, Settle)
	: AstNodeSenItem(fl) {
	m_edgeType = AstEdgeType::ET_SETTLE;
    }
    AstSenItem(FileLine* fl, Never)
	: AstNodeSenItem(fl) {
	m_edgeType = AstEdgeType::ET_NEVER;
    }
    ASTNODE_NODE_FUNCS(SenItem, SENITEM)
    virtual void dump(ostream& str);
    virtual V3Hash sameHash() const { return V3Hash(V3Hash(edgeType())); }
    virtual bool same(AstNode* samep) const {
	return edgeType()==samep->castSenItem()->edgeType(); }
    AstEdgeType edgeType()	const { return m_edgeType; }		// * = Posedge/negedge
    void edgeType(AstEdgeType type)  { m_edgeType=type; editCountInc(); }// * = Posedge/negedge
    AstNode*	sensp()		const { return op1p(); }		// op1 = Signal sensitized
    AstNodeVarRef* varrefp()	const { return op1p()->castNodeVarRef(); }	// op1 = Signal sensitized
    //
    virtual bool isClocked() const { return edgeType().clockedStmt(); }
    virtual bool isCombo() const { return edgeType()==AstEdgeType::ET_COMBO; }
    virtual bool isInitial() const { return edgeType()==AstEdgeType::ET_INITIAL; }
    virtual bool isSettle() const { return edgeType()==AstEdgeType::ET_SETTLE; }
    virtual bool isNever() const { return edgeType()==AstEdgeType::ET_NEVER; }
    bool hasVar() const { return !(isCombo()||isInitial()||isSettle()||isNever()); }
};

struct AstSenGate : public AstNodeSenItem {
    // Parents:  SENTREE
    // Children: SENITEM expr
    // AND as applied to a sensitivity list and a gating expression
    // Performing this gating is optional; it may be removed by later optimizations
    AstSenGate(FileLine* fl, AstSenItem* sensesp, AstNode* rhsp) : AstNodeSenItem(fl) {
	dtypeChgLogicBool(); addOp1p(sensesp); setOp2p(rhsp);
    }
    ASTNODE_NODE_FUNCS(SenGate, SENGATE)
    virtual string emitVerilog() { return "(%l) %f&& (%r)"; }
    AstSenItem*	sensesp() const { return op1p()->castSenItem(); }
    AstNode*	rhsp() 	const { return op2p()->castNode(); }
    void	sensesp(AstSenItem* nodep)  { addOp1p(nodep); }
    void	rhsp(AstNode* nodep)  { setOp2p(nodep); }
    //
    virtual bool isClocked() const { return true; }
    virtual bool isCombo() const { return false; }
    virtual bool isInitial() const { return false; }
    virtual bool isSettle() const { return false; }
    virtual bool isNever() const { return false; }
};

struct AstSenTree : public AstNode {
    // A list of senitems
    // Parents:  MODULE | SBLOCK
    // Children: SENITEM list
private:
    bool	m_multi;	// Created from combo logic by ORing multiple clock domains
public:
    AstSenTree(FileLine* fl, AstNodeSenItem* sensesp)
	: AstNode(fl), m_multi(false) {
	addNOp1p(sensesp);
    }
    ASTNODE_NODE_FUNCS(SenTree, SENTREE)
    virtual void dump(ostream& str);
    virtual bool maybePointedTo() const { return true; }
    bool isMulti() const { return m_multi; }
    AstNodeSenItem* sensesp() 	const { return op1p()->castNodeSenItem(); }	// op1 = Sensitivity list
    void addSensesp(AstNodeSenItem* nodep) { addOp1p(nodep); }
    void multi(bool flag) { m_multi = true; }
    // METHODS
    bool hasClocked();	// Includes a clocked statement
    bool hasSettle();	// Includes a SETTLE SenItem
    bool hasInitial();	// Includes a INITIAL SenItem
    bool hasCombo();	// Includes a COMBO SenItem
};

struct AstAlways : public AstNode {
    AstAlways(FileLine* fl, AstSenTree* sensesp, AstNode* bodysp)
	: AstNode(fl) {
	addNOp1p(sensesp); addNOp2p(bodysp);
    }
    ASTNODE_NODE_FUNCS(Always, ALWAYS)
    //
    AstSenTree*	sensesp() 	const { return op1p()->castSenTree(); }	// op1 = Sensitivity list
    AstNode*	bodysp() 	const { return op2p()->castNode(); }	// op2 = Statements to evaluate
    void addStmtp(AstNode* nodep) { addOp2p(nodep); }
    // Special accessors
    bool isJustOneBodyStmt() const { return bodysp() && !bodysp()->nextp(); }
};

struct AstAlwaysPublic : public AstNodeStmt {
    // "Fake" sensitivity created by /*verilator public_flat_rw @(edgelist)*/
    // Body statements are just AstVarRefs to the public signals
    AstAlwaysPublic(FileLine* fl, AstSenTree* sensesp, AstNode* bodysp)
	: AstNodeStmt(fl) {
	addNOp1p(sensesp); addNOp2p(bodysp);
    }
    ASTNODE_NODE_FUNCS(AlwaysPublic, ALWAYSPUBLIC)
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
    //
    AstSenTree*	sensesp() 	const { return op1p()->castSenTree(); }	// op1 = Sensitivity list
    AstNode*	bodysp() 	const { return op2p()->castNode(); }	// op2 = Statements to evaluate
    void addStmtp(AstNode* nodep) { addOp2p(nodep); }
    // Special accessors
    bool isJustOneBodyStmt() const { return bodysp() && !bodysp()->nextp(); }
};

struct AstAlwaysPost : public AstNode {
    // Like always but post assignments for memory assignment IFs
    AstAlwaysPost(FileLine* fl, AstSenTree* sensesp, AstNode* bodysp)
	: AstNode(fl) {
	addNOp1p(sensesp); addNOp2p(bodysp);
    }
    ASTNODE_NODE_FUNCS(AlwaysPost, ALWAYSPOST)
    //
    AstNode*	bodysp() 	const { return op2p()->castNode(); }	// op2 = Statements to evaluate
    void	addBodysp(AstNode* newp)	{ addOp2p(newp); }
};

struct AstAssign : public AstNodeAssign {
    AstAssign(FileLine* fileline, AstNode* lhsp, AstNode* rhsp)
	: AstNodeAssign(fileline, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(Assign, ASSIGN)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) { return new AstAssign(this->fileline(), lhsp, rhsp); }
};

struct AstAssignAlias : public AstNodeAssign {
    // Like AstAssignW, but a true bidirect interconnection alias
    // If both sides are wires, there's no LHS vs RHS,
    AstAssignAlias(FileLine* fileline, AstVarRef* lhsp, AstVarRef* rhsp)
	: AstNodeAssign(fileline, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(AssignAlias, ASSIGNALIAS)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) { V3ERROR_NA; return NULL; }
};

struct AstAssignDly : public AstNodeAssign {
    AstAssignDly(FileLine* fileline, AstNode* lhsp, AstNode* rhsp)
	: AstNodeAssign(fileline, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(AssignDly, ASSIGNDLY)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) { return new AstAssignDly(this->fileline(), lhsp, rhsp); }
    virtual bool isGateOptimizable() const { return false; }
    virtual string verilogKwd() const { return "<="; }
};

struct AstAssignW : public AstNodeAssign {
    // Like assign, but wire/assign's in verilog, the only setting of the specified variable
    AstAssignW(FileLine* fileline, AstNode* lhsp, AstNode* rhsp)
	: AstNodeAssign(fileline, lhsp, rhsp) { }
    ASTNODE_NODE_FUNCS(AssignW, ASSIGNW)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) { return new AstAssignW(this->fileline(), lhsp, rhsp); }
    AstAlways* convertToAlways() {
	AstNode* lhs1p = lhsp()->unlinkFrBack();
	AstNode* rhs1p = rhsp()->unlinkFrBack();
	AstAlways* newp = new AstAlways (fileline(), NULL,
					 new AstAssign (fileline(), lhs1p, rhs1p));
	replaceWith(newp); // User expected to then deleteTree();
	return newp;
    }
};

struct AstPull : public AstNode {
private:
    bool m_direction;
public:
    AstPull(FileLine* fileline, AstNode* lhsp, bool direction) 
	: AstNode(fileline) {
	setOp1p(lhsp);
	m_direction = direction;
    }
    ASTNODE_NODE_FUNCS(Pull, PULL)
    virtual bool same(AstNode* samep) const {
	return direction()==samep->castPull()->direction(); }
    void lhsp(AstNode* np) { setOp1p(np); }
    AstNode* lhsp() const { return op1p()->castNode(); }	// op1 = Assign to
    uint32_t direction() const { return (uint32_t) m_direction; }
};

struct AstAssignPre : public AstNodeAssign {
    // Like Assign, but predelayed assignment requiring special order handling
    AstAssignPre(FileLine* fileline, AstNode* lhsp, AstNode* rhsp)
	: AstNodeAssign(fileline, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(AssignPre, ASSIGNPRE)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) { return new AstAssignPre(this->fileline(), lhsp, rhsp); }
};

struct AstAssignPost : public AstNodeAssign {
    // Like Assign, but predelayed assignment requiring special order handling
    AstAssignPost(FileLine* fileline, AstNode* lhsp, AstNode* rhsp)
	: AstNodeAssign(fileline, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(AssignPost, ASSIGNPOST)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) { return new AstAssignPost(this->fileline(), lhsp, rhsp); }
};

struct AstComment : public AstNodeStmt {
    // Some comment to put into the output stream
    // Parents:  {statement list}
    // Children: none
private:
    string	m_name;		// Name of variable
public:
    AstComment(FileLine* fl, const string& name)
	: AstNodeStmt(fl)
	, m_name(name) {}
    ASTNODE_NODE_FUNCS(Comment, COMMENT)
    virtual string name()	const { return m_name; }		// * = Var name
    virtual V3Hash sameHash() const { return V3Hash(); }  // Ignore name in comments
    virtual bool same(AstNode* samep) const { return true; }  // Ignore name in comments
};

struct AstCond : public AstNodeCond {
    // Conditional ?: statement
    // Parents:  MATH
    // Children: MATH
    AstCond(FileLine* fl, AstNode* condp, AstNode* expr1p, AstNode* expr2p)
	: AstNodeCond(fl, condp, expr1p, expr2p) {}
    ASTNODE_NODE_FUNCS(Cond, COND)
};

struct AstCondBound : public AstNodeCond {
    // Conditional ?: statement, specially made for saftey checking of array bounds
    // Parents:  MATH
    // Children: MATH
    AstCondBound(FileLine* fl, AstNode* condp, AstNode* expr1p, AstNode* expr2p)
	: AstNodeCond(fl, condp, expr1p, expr2p) {}
    ASTNODE_NODE_FUNCS(CondBound, CONDBOUND)
};

struct AstCoverDecl : public AstNodeStmt {
    // Coverage analysis point declaration
    // Parents:  {statement list}
    // Children: none
private:
    AstCoverDecl* m_dataDeclp;	// [After V3CoverageJoin] Pointer to duplicate declaration to get data from instead
    string	m_page;
    string	m_text;
    string	m_hier;
    int		m_column;
    int		m_binNum;	// Set by V3EmitCSyms to tell final V3Emit what to increment
public:
    AstCoverDecl(FileLine* fl, int column, const string& page, const string& comment)
	: AstNodeStmt(fl) {
	m_text = comment; m_page = page; m_column = column;
	m_binNum = 0;
	m_dataDeclp = NULL;
    }
    ASTNODE_NODE_FUNCS(CoverDecl, COVERDECL)
    virtual bool broken() const {
	if (m_dataDeclp && !m_dataDeclp->brokeExists()) return true;
	if (m_dataDeclp && m_dataDeclp->m_dataDeclp) v3fatalSrc("dataDeclp should point to real data, not be a list");  // Avoid O(n^2) accessing
        return false; }
    virtual void cloneRelink() { if (m_dataDeclp && m_dataDeclp->clonep()) m_dataDeclp = m_dataDeclp->clonep()->castCoverDecl(); }
    virtual void dump(ostream& str);
    virtual int instrCount()	const { return 1+2*instrCountLd(); }
    virtual bool maybePointedTo() const { return true; }
    int		column() 	const { return m_column; }
    void	binNum(int flag) { m_binNum = flag; }
    int		binNum() 	const { return m_binNum; }
    const string& comment() const { return m_text; }			// text to insert in code
    const string& page() const { return m_page; }
    const string& hier() const { return m_hier; }
    void hier(const string& flag) { m_hier=flag; }
    void comment(const string& flag) { m_text=flag; }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const {
	return (fileline() == samep->castCoverDecl()->fileline()
		&& hier()==samep->castCoverDecl()->hier()
		&& comment()==samep->castCoverDecl()->comment()
		&& column()==samep->castCoverDecl()->column()); }
    virtual bool isPredictOptimizable() const { return false; }
    void		dataDeclp(AstCoverDecl* nodep) { m_dataDeclp=nodep; }
    // dataDecl NULL means "use this one", but often you want "this" to indicate to get data from here
    AstCoverDecl*	dataDeclNullp() const { return m_dataDeclp; }
    AstCoverDecl*	dataDeclThisp() { return dataDeclNullp()?dataDeclNullp():this; }
};

struct AstCoverInc : public AstNodeStmt {
    // Coverage analysis point; increment coverage count
    // Parents:  {statement list}
    // Children: none
private:
    AstCoverDecl*	m_declp;	// [After V3Coverage] Pointer to declaration
public:
    AstCoverInc(FileLine* fl, AstCoverDecl* declp)
	: AstNodeStmt(fl) {
	m_declp = declp;
    }
    ASTNODE_NODE_FUNCS(CoverInc, COVERINC)
    virtual bool broken() const { return !declp()->brokeExists(); }
    virtual void cloneRelink() { if (m_declp->clonep()) m_declp = m_declp->clonep()->castCoverDecl(); }
    virtual void dump(ostream& str);
    virtual int instrCount()	const { return 1+2*instrCountLd(); }
    virtual V3Hash sameHash() const { return V3Hash(declp()); }
    virtual bool same(AstNode* samep) const {
	return declp()==samep->castCoverInc()->declp(); }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool isOutputter() const { return true; }
    // but isPure()  true
    AstCoverDecl*	declp() const { return m_declp; }	// Where defined
};

struct AstCoverToggle : public AstNodeStmt {
    // Toggle analysis of given signal
    // Parents:  MODULE
    // Children: AstCoverInc, orig var, change det var
    AstCoverToggle(FileLine* fl, AstCoverInc* incp, AstNode* origp, AstNode* changep)
	: AstNodeStmt(fl) {
	setOp1p(incp);
	setOp2p(origp);
	setOp3p(changep);
    }
    ASTNODE_NODE_FUNCS(CoverToggle, COVERTOGGLE)
    virtual int instrCount()	const { return 3+instrCountBranch()+instrCountLd(); }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode*) const { return true; }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return true; }
    virtual bool isOutputter() const { return false; }   // Though the AstCoverInc under this is an outputter
    // but isPure()  true
    AstCoverInc* incp() const { return op1p()->castCoverInc(); }
    void 	incp(AstCoverInc* nodep) { setOp1p(nodep); }
    AstNode* origp() const { return op2p(); }
    AstNode* changep() const { return op3p(); }
};

struct AstGenCase : public AstNodeCase {
    // Generate Case statement
    // Parents:  {statement list}
    // exprp Children:  MATHs
    // casesp Children: CASEITEMs
    AstGenCase(FileLine* fileline, AstNode* exprp, AstNode* casesp)
	: AstNodeCase(fileline, exprp, casesp) {
    }
    ASTNODE_NODE_FUNCS(GenCase, GENCASE)
};

struct AstCase : public AstNodeCase {
    // Case statement
    // Parents:  {statement list}
    // exprp Children:  MATHs
    // casesp Children: CASEITEMs
private:
    AstCaseType	m_casex;		// 0=case, 1=casex, 2=casez
    bool	m_fullPragma;		// Synthesis full_case
    bool	m_parallelPragma;	// Synthesis parallel_case
    bool	m_uniquePragma;		// unique case
    bool	m_unique0Pragma;	// unique0 case
    bool	m_priorityPragma;	// priority case
public:
    AstCase(FileLine* fileline, AstCaseType casex, AstNode* exprp, AstNode* casesp)
	: AstNodeCase(fileline, exprp, casesp) {
	m_casex=casex;
	m_fullPragma=false; m_parallelPragma=false;
	m_uniquePragma=false; m_unique0Pragma=false; m_priorityPragma=false;
    }
    ASTNODE_NODE_FUNCS(Case, CASE)
    virtual string  verilogKwd() const { return casez()?"casez":casex()?"casex":"case"; }
    virtual bool same(AstNode* samep) const {
	return m_casex==samep->castCase()->m_casex; }
    bool	casex()	const { return m_casex==AstCaseType::CT_CASEX; }
    bool	casez()	const { return m_casex==AstCaseType::CT_CASEZ; }
    bool	fullPragma()	const { return m_fullPragma; }
    void	fullPragma(bool flag)	{ m_fullPragma=flag; }
    bool	parallelPragma()	const { return m_parallelPragma; }
    void	parallelPragma(bool flag) { m_parallelPragma=flag; }
    bool	uniquePragma() const { return m_uniquePragma; }
    void	uniquePragma(bool flag) { m_uniquePragma=flag; }
    bool	unique0Pragma()	const { return m_unique0Pragma; }
    void	unique0Pragma(bool flag) { m_unique0Pragma=flag; }
    bool	priorityPragma() const { return m_priorityPragma; }
    void	priorityPragma(bool flag) { m_priorityPragma=flag; }
};

struct AstCaseItem : public AstNode {
    // Single item of a case statement
    // Parents:  CASE
    // condsp Children: MATH  (Null condition used for default block)
    // bodysp Children: Statements
private:
    bool	m_ignoreOverlap;	// Default created by assertions; ignore overlaps
public:
    AstCaseItem(FileLine* fileline, AstNode* condsp, AstNode* bodysp)
	: AstNode(fileline) {
	addNOp1p(condsp); addNOp2p(bodysp);
	m_ignoreOverlap = false;
    }
    ASTNODE_NODE_FUNCS(CaseItem, CASEITEM)
    virtual int instrCount()	const { return widthInstrs()+instrCountBranch(); }
    AstNode*	condsp()		const { return op1p()->castNode(); }	// op1= list of possible matching expressions
    AstNode*	bodysp()	const { return op2p()->castNode(); }	// op2= what to do
    void	condsp(AstNode* nodep) { setOp1p(nodep); }
    void	addBodysp(AstNode* newp)	{ addOp2p(newp); }
    bool	isDefault() const { return condsp()==NULL; }
    bool	ignoreOverlap() const { return m_ignoreOverlap; }
    void	ignoreOverlap(bool flag) { m_ignoreOverlap = flag; }
};

struct AstSFormatF : public AstNode {
    // Convert format to string, generally under an AstDisplay or AstSFormat
    // Also used as "real" function for /*verilator sformat*/ functions
    string	m_text;
    bool	m_hidden;	// Under display, etc
public:
    AstSFormatF(FileLine* fl, const string& text, bool hidden, AstNode* exprsp)
	: AstNode(fl), m_text(text), m_hidden(hidden) {
	addNOp1p(exprsp); addNOp2p(NULL); }
    ASTNODE_NODE_FUNCS(SFormatF, SFORMATF)
    virtual string name() const { return m_text; }
    virtual int instrCount() const { return instrCountPli(); }
    virtual V3Hash sameHash() const { return V3Hash(text()); }
    virtual bool same(AstNode* samep) const { return text()==samep->castSFormatF()->text(); }
    virtual string verilogKwd() const { return "$sformatf"; }
    void exprsp(AstNode* nodep)	{ addOp1p(nodep); }	// op1 = Expressions to output
    AstNode* exprsp() const { return op1p()->castNode(); }	// op1 = Expressions to output
    string text() const { return m_text; }		// * = Text to display
    void text(const string& text) { m_text=text; }
    AstScopeName* scopeNamep() const { return op2p()->castScopeName(); }
    void scopeNamep(AstNode* nodep) { setNOp2p(nodep); }
    bool formatScopeTracking() const {  // Track scopeNamep();  Ok if false positive
	return (name().find("%m") != string::npos || name().find("%M") != string::npos); }
    bool hidden() const { return m_hidden; }
};

struct AstDisplay : public AstNode {
    // Parents: stmtlist
    // Children: file which must be a varref
    // Children: SFORMATF to generate print string
private:
    AstDisplayType	m_displayType;
public:
    AstDisplay(FileLine* fileline, AstDisplayType dispType, const string& text, AstNode* filep, AstNode* exprsp)
	: AstNode (fileline) {
	setOp1p(new AstSFormatF(fileline,text,true,exprsp));
	setNOp3p(filep);
	m_displayType = dispType;
    }
    ASTNODE_NODE_FUNCS(Display, DISPLAY)
    virtual void dump(ostream& str);
    virtual bool broken() const { return !fmtp(); }
    virtual string verilogKwd() const { return (filep() ? (string)"$f"+(string)displayType().ascii()
						: (string)"$"+(string)displayType().ascii()); }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool isPure() const { return false; }	// SPECIAL: $display has 'visual' ordering
    virtual bool isOutputter() const { return true; }	// SPECIAL: $display makes output
    virtual bool isUnlikely() const { return true; }
    virtual V3Hash sameHash() const { return V3Hash(displayType()); }
    virtual bool same(AstNode* samep) const { return displayType()==samep->castDisplay()->displayType(); }
    virtual int instrCount()	const { return instrCountPli(); }
    AstDisplayType	displayType()	const { return m_displayType; }
    void	displayType(AstDisplayType type) { m_displayType = type; }
    bool	addNewline() const { return displayType().addNewline(); }  // * = Add a newline for $display
    void	fmtp(AstSFormatF* nodep) { addOp1p(nodep); }	// op1 = To-String formatter
    AstSFormatF* fmtp() const { return op1p()->castSFormatF(); }
    AstNode*	filep() const { return op3p(); }
    void 	filep(AstNodeVarRef* nodep) { setNOp3p(nodep); }
};

struct AstSFormat : public AstNode {
    // Parents: statement container
    // Children: string to load
    // Children: SFORMATF to generate print string
    AstSFormat(FileLine* fileline, AstNode* lhsp, const string& text, AstNode* exprsp)
	: AstNode (fileline) {
	setOp1p(new AstSFormatF(fileline,text,true,exprsp));
	setOp3p(lhsp);
    }
    ASTNODE_NODE_FUNCS(SFormat, SFORMAT)
    virtual bool broken() const { return !fmtp(); }
    virtual string verilogKwd() const { return "$sformat"; }
    virtual string emitVerilog() { V3ERROR_NA; return ""; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return true; }
    virtual bool isPure() const { return true; }
    virtual bool isOutputter() const { return false; }
    virtual bool cleanOut() { return false; }
    virtual int instrCount()	const { return instrCountPli(); }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
    void	fmtp(AstSFormatF* nodep) { addOp1p(nodep); }	// op1 = To-String formatter
    AstSFormatF* fmtp() const { return op1p()->castSFormatF(); }
    AstNode*	lhsp() const { return op3p(); }
    void 	lhsp(AstNode* nodep) { setOp3p(nodep); }
};

struct AstSysIgnore : public AstNode {
    // Parents: stmtlist
    // Children: varrefs or exprs
    AstSysIgnore(FileLine* fileline, AstNode* exprsp)
	: AstNode (fileline) { addNOp1p(exprsp); }
    ASTNODE_NODE_FUNCS(SysIgnore, SYSIGNORE)
    virtual string verilogKwd() const { return "$ignored"; }
    virtual bool isGateOptimizable() const { return false; }  // Though deleted before opt
    virtual bool isPredictOptimizable() const { return false; }  // Though deleted before opt
    virtual bool isPure() const { return false; }  // Though deleted before opt
    virtual bool isOutputter() const { return true; }  // Though deleted before opt
    virtual int instrCount()	const { return instrCountPli(); }
    AstNode*	exprsp()	const { return op1p()->castNode(); }	// op1 = Expressions to output
    void 	exprsp(AstNode* nodep)	{ addOp1p(nodep); }	// op1 = Expressions to output
};

struct AstFClose : public AstNodeStmt {
    // Parents: stmtlist
    // Children: file which must be a varref
    AstFClose(FileLine* fileline, AstNode* filep)
	: AstNodeStmt (fileline) {
	setNOp2p(filep);
    }
    ASTNODE_NODE_FUNCS(FClose, FCLOSE)
    virtual string verilogKwd() const { return "$fclose"; }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool isPure() const { return false; }
    virtual bool isOutputter() const { return true; }
    virtual bool isUnlikely() const { return true; }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
    AstNode*	filep() const { return op2p(); }
    void filep(AstNodeVarRef* nodep) { setNOp2p(nodep); }
};

struct AstFOpen : public AstNodeStmt {
    AstFOpen(FileLine* fileline, AstNode* filep, AstNode* filenamep, AstNode* modep)
	: AstNodeStmt (fileline) {
	setOp1p(filep);
	setOp2p(filenamep);
	setOp3p(modep);
    }
    ASTNODE_NODE_FUNCS(FOpen, FOPEN)
    virtual string verilogKwd() const { return "$fopen"; }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool isPure() const { return false; }
    virtual bool isOutputter() const { return true; }
    virtual bool isUnlikely() const { return true; }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
    AstNode*	filep() const { return op1p(); }
    AstNode*	filenamep() const { return op2p(); }
    AstNode*	modep() const { return op3p(); }
};

struct AstFFlush : public AstNodeStmt {
    // Parents: stmtlist
    // Children: file which must be a varref
    AstFFlush(FileLine* fileline, AstNode* filep)
	: AstNodeStmt (fileline) {
	setNOp2p(filep);
    }
    ASTNODE_NODE_FUNCS(FFlush, FFLUSH)
    virtual string verilogKwd() const { return "$fflush"; }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool isPure() const { return false; }
    virtual bool isOutputter() const { return true; }
    virtual bool isUnlikely() const { return true; }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
    AstNode*	filep() const { return op2p(); }
    void filep(AstNodeVarRef* nodep) { setNOp2p(nodep); }
};

struct AstFScanF : public AstNodeMath {
    // Parents: expr
    // Children: file which must be a varref
    // Children: varrefs to load
private:
    string	m_text;
public:
    AstFScanF(FileLine* fileline, const string& text, AstNode* filep, AstNode* exprsp)
	: AstNodeMath (fileline), m_text(text) {
	addNOp1p(exprsp);
	setNOp2p(filep);
    }
    ASTNODE_NODE_FUNCS(FScanF, FSCANF)
    virtual string name()	const { return m_text; }
    virtual string verilogKwd() const { return "$fscanf"; }
    virtual string emitVerilog() { V3ERROR_NA; return ""; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool isPure() const { return false; }	// SPECIAL: has 'visual' ordering
    virtual bool isOutputter() const { return true; }	// SPECIAL: makes output
    virtual bool cleanOut() { return false; }
    virtual V3Hash sameHash() const { return V3Hash(text()); }
    virtual bool same(AstNode* samep) const {
	return text()==samep->castFScanF()->text(); }
    AstNode*	exprsp()	const { return op1p()->castNode(); }	// op1 = Expressions to output
    void 	exprsp(AstNode* nodep)	{ addOp1p(nodep); }	// op1 = Expressions to output
    string 	text()		const { return m_text; }		// * = Text to display
    void 	text(const string& text) { m_text=text; }
    AstNode*	filep() const { return op2p(); }
    void 	filep(AstNodeVarRef* nodep) { setNOp2p(nodep); }
};

struct AstSScanF : public AstNodeMath {
    // Parents: expr
    // Children: file which must be a varref
    // Children: varrefs to load
private:
    string	m_text;
public:
    AstSScanF(FileLine* fileline, const string& text, AstNode* fromp, AstNode* exprsp)
	: AstNodeMath (fileline), m_text(text) {
	addNOp1p(exprsp);
	setOp2p(fromp);
    }
    ASTNODE_NODE_FUNCS(SScanF, SSCANF)
    virtual string name()	const { return m_text; }
    virtual string verilogKwd() const { return "$sscanf"; }
    virtual string emitVerilog() { V3ERROR_NA; return ""; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool isPure() const { return false; }	// SPECIAL: has 'visual' ordering
    virtual bool isOutputter() const { return true; }	// SPECIAL: makes output
    virtual bool cleanOut() { return false; }
    virtual V3Hash sameHash() const { return V3Hash(text()); }
    virtual bool same(AstNode* samep) const {
	return text()==samep->castSScanF()->text(); }
    AstNode*	exprsp()	const { return op1p()->castNode(); }	// op1 = Expressions to output
    void	exprsp(AstNode* nodep)	{ addOp1p(nodep); }	// op1 = Expressions to output
    string 	text()		const { return m_text; }		// * = Text to display
    void 	text(const string& text) { m_text=text; }
    AstNode*	fromp() const { return op2p(); }
    void 	fromp(AstNode* nodep) { setOp2p(nodep); }
};

struct AstReadMem : public AstNodeStmt {
private:
    bool	m_isHex;	// readmemh, not readmemb
public:
    AstReadMem(FileLine* fileline, bool hex,
	       AstNode* filenamep, AstNode* memp, AstNode* lsbp, AstNode* msbp)
	: AstNodeStmt (fileline), m_isHex(hex) {
	setOp1p(filenamep); setOp2p(memp); setNOp3p(lsbp); setNOp4p(msbp);
    }
    ASTNODE_NODE_FUNCS(ReadMem, READMEM)
    virtual string verilogKwd() const { return (isHex()?"$readmemh":"$readmemb"); }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool isPure() const { return false; }
    virtual bool isOutputter() const { return true; }
    virtual bool isUnlikely() const { return true; }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return isHex()==samep->castReadMem()->isHex(); }
    bool	isHex() const { return m_isHex; }
    AstNode*	filenamep() const { return op1p()->castNode(); }
    AstNode*	memp() const { return op2p()->castNode(); }
    AstNode*	lsbp() const { return op3p()->castNode(); }
    AstNode*	msbp() const { return op4p()->castNode(); }
};

struct AstSystemT : public AstNodeStmt {
    // $system used as task
    AstSystemT(FileLine* fileline, AstNode* lhsp)
	: AstNodeStmt (fileline) {
	setOp1p(lhsp);
    }
    ASTNODE_NODE_FUNCS(SystemT, SYSTEMT)
    virtual string verilogKwd() const { return "$system"; }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool isPure() const { return false; }
    virtual bool isOutputter() const { return true; }
    virtual bool isUnlikely() const { return true; }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
    AstNode*	lhsp() const { return op1p(); }
};

struct AstSystemF : public AstNodeMath {
    // $system used as function
    AstSystemF(FileLine* fileline, AstNode* lhsp)
	: AstNodeMath (fileline) {
	setOp1p(lhsp);
    }
    ASTNODE_NODE_FUNCS(SystemF, SYSTEMF)
    virtual string verilogKwd() const { return "$system"; }
    virtual string emitVerilog() { return verilogKwd(); }
    virtual string emitC() { return "VL_SYSTEM_%nq(%lw, %P)"; }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool isPure() const { return false; }
    virtual bool isOutputter() const { return true; }
    virtual bool isUnlikely() const { return true; }
    virtual bool cleanOut() { return true; }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
    AstNode*	lhsp() const { return op1p(); }
};

struct AstValuePlusArgs : public AstNodeMath {
    // Parents: expr
    // Child: variable to set.  If NULL then this is a $test$plusargs instead of $value$plusargs
private:
    string	m_text;
public:
    AstValuePlusArgs(FileLine* fileline, const string& text, AstNode* exprsp)
	: AstNodeMath (fileline), m_text(text) {
	setOp1p(exprsp);
    }
    ASTNODE_NODE_FUNCS(ValuePlusArgs, VALUEPLUSARGS)
    virtual string name()	const { return m_text; }
    virtual string verilogKwd() const { return "$value$plusargs"; }
    virtual string emitVerilog() { return verilogKwd(); }
    virtual string emitC() { return "VL_VALUEPLUSARGS_%nq(%lw, %P, NULL)"; }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool cleanOut() { return true; }
    virtual V3Hash sameHash() const { return V3Hash(text()); }
    virtual bool same(AstNode* samep) const {
	return text()==samep->castValuePlusArgs()->text(); }
    AstNode*	exprsp()	const { return op1p()->castNode(); }	// op1 = Expressions to output
    void 	exprsp(AstNode* nodep)	{ setOp1p(nodep); }	// op1 = Expressions to output
    string 	text()		const { return m_text; }	// * = Text to display
    void 	text(const string& text) { m_text=text; }
};

struct AstTestPlusArgs : public AstNodeMath {
    // Parents: expr
    // Child: variable to set.  If NULL then this is a $test$plusargs instead of $value$plusargs
private:
    string	m_text;
public:
    AstTestPlusArgs(FileLine* fileline, const string& text)
	: AstNodeMath (fileline), m_text(text) { }
    ASTNODE_NODE_FUNCS(TestPlusArgs, TESTPLUSARGS)
    virtual string name()	const { return m_text; }
    virtual string verilogKwd() const { return "$test$plusargs"; }
    virtual string emitVerilog() { return verilogKwd(); }
    virtual string emitC() { return "VL_VALUEPLUSARGS_%nq(%lw, %P, NULL)"; }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool cleanOut() { return true; }
    virtual V3Hash sameHash() const { return V3Hash(text()); }
    virtual bool same(AstNode* samep) const {
	return text()==samep->castTestPlusArgs()->text(); }
    string 	text()		const { return m_text; }	// * = Text to display
    void 	text(const string& text) { m_text=text; }
};

struct AstGenFor : public AstNodeFor {
    AstGenFor(FileLine* fileline, AstNode* initsp, AstNode* condp,
	   AstNode* incsp, AstNode* bodysp)
	: AstNodeFor(fileline, initsp, condp, incsp, bodysp) {
    }
    ASTNODE_NODE_FUNCS(GenFor, GENFOR)
};

struct AstRepeat : public AstNodeStmt {
    AstRepeat(FileLine* fileline, AstNode* countp, AstNode* bodysp)
	: AstNodeStmt(fileline) {
	setOp2p(countp); addNOp3p(bodysp);
    }
    ASTNODE_NODE_FUNCS(Repeat, REPEAT)
    AstNode*	countp()	const { return op2p()->castNode(); }	// op2= condition to continue
    AstNode*	bodysp()	const { return op3p()->castNode(); }	// op3= body of loop
    virtual bool isGateOptimizable() const { return false; }  // Not releavant - converted to FOR
    virtual int instrCount()	const { return instrCountBranch(); }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
};

struct AstWhile : public AstNodeStmt {
    AstWhile(FileLine* fileline, AstNode* condp, AstNode* bodysp, AstNode* incsp=NULL)
	: AstNodeStmt(fileline) {
	setOp2p(condp); addNOp3p(bodysp); addNOp4p(incsp);
    }
    ASTNODE_NODE_FUNCS(While, WHILE)
    AstNode*	precondsp()	const { return op1p()->castNode(); }	// op1= prepare statements for condition (exec every loop)
    AstNode*	condp()		const { return op2p()->castNode(); }	// op2= condition to continue
    AstNode*	bodysp()	const { return op3p()->castNode(); }	// op3= body of loop
    AstNode*	incsp()		const { return op4p()->castNode(); }	// op4= increment (if from a FOR loop)
    void	addPrecondsp(AstNode* newp)	{ addOp1p(newp); }
    void	addBodysp(AstNode* newp)	{ addOp3p(newp); }
    void	addIncsp(AstNode* newp)		{ addOp4p(newp); }
    virtual bool isGateOptimizable() const { return false; }
    virtual int instrCount()	const { return instrCountBranch(); }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
    virtual void addBeforeStmt(AstNode* newp, AstNode* belowp);  // Stop statement searchback here 
    virtual void addNextStmt(AstNode* newp, AstNode* belowp);  // Stop statement searchback here 
};

struct AstBreak : public AstNodeStmt {
    AstBreak(FileLine* fileline)
	: AstNodeStmt (fileline) {}
    ASTNODE_NODE_FUNCS(Break, BREAK)
    virtual string verilogKwd() const { return "break"; };
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool isBrancher() const { return true; }	// SPECIAL: We don't process code after breaks
};

struct AstContinue : public AstNodeStmt {
    AstContinue(FileLine* fileline)
	: AstNodeStmt (fileline) {}
    ASTNODE_NODE_FUNCS(Continue, CONTINUE)
    virtual string verilogKwd() const { return "continue"; };
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool isBrancher() const { return true; }	// SPECIAL: We don't process code after breaks
};

struct AstDisable : public AstNodeStmt {
private:
    string	m_name;		// Name of block
public:
    AstDisable(FileLine* fileline, const string& name)
	: AstNodeStmt(fileline), m_name(name) {}
    ASTNODE_NODE_FUNCS(Disable, DISABLE)
    virtual string name()	const { return m_name; }		// * = Block name
    void name(const string& flag) { m_name=flag; }
    virtual bool isBrancher() const { return true; }	// SPECIAL: We don't process code after breaks
};

struct AstReturn : public AstNodeStmt {
    AstReturn(FileLine* fileline, AstNode* lhsp=NULL)
	: AstNodeStmt (fileline) {
	setNOp1p(lhsp);
    }
    ASTNODE_NODE_FUNCS(Return, RETURN)
    virtual string verilogKwd() const { return "return"; };
    virtual V3Hash sameHash() const { return V3Hash(); }
    AstNode*	lhsp() const { return op1p(); }
    virtual bool isBrancher() const { return true; }	// SPECIAL: We don't process code after breaks
};

struct AstGenIf : public AstNodeIf {
    AstGenIf(FileLine* fileline, AstNode* condp, AstNode* ifsp, AstNode* elsesp)
	: AstNodeIf(fileline, condp, ifsp, elsesp) {
    }
    ASTNODE_NODE_FUNCS(GenIf, GENIF)
};

struct AstIf : public AstNodeIf {
private:
    bool	m_uniquePragma;		// unique case
    bool	m_unique0Pragma;	// unique0 case
    bool	m_priorityPragma;	// priority case
public:
    AstIf(FileLine* fileline, AstNode* condp, AstNode* ifsp, AstNode* elsesp)
	: AstNodeIf(fileline, condp, ifsp, elsesp) {
	m_uniquePragma=false; m_unique0Pragma=false; m_priorityPragma=false;
    }
    ASTNODE_NODE_FUNCS(If, IF)
    bool	uniquePragma() const { return m_uniquePragma; }
    void	uniquePragma(bool flag) { m_uniquePragma=flag; }
    bool	unique0Pragma()	const { return m_unique0Pragma; }
    void	unique0Pragma(bool flag) { m_unique0Pragma=flag; }
    bool	priorityPragma() const { return m_priorityPragma; }
    void	priorityPragma(bool flag) { m_priorityPragma=flag; }
};

struct AstJumpLabel : public AstNodeStmt {
    // Jump point declaration
    // Separate from AstJumpGo; as a declaration can't be deleted
    // Parents:  {statement list}
    // Children: {statement list, with JumpGo below}
private:
    int		m_labelNum;	// Set by V3EmitCSyms to tell final V3Emit what to increment
public:
    AstJumpLabel(FileLine* fl, AstNode* stmtsp)
	: AstNodeStmt(fl) ,m_labelNum(0) {
	addNOp1p(stmtsp);
    }
    virtual int instrCount()	const { return 0; }
    ASTNODE_NODE_FUNCS(JumpLabel, JUMPLABEL)
    virtual bool maybePointedTo() const { return true; }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
    // op1 = Statements
    AstNode*	stmtsp() 	const { return op1p()->castNode(); }	// op1 = List of statements
    void addStmtsp(AstNode* nodep) { addNOp1p(nodep); }
    int labelNum() const { return m_labelNum; }
    void labelNum(int flag) { m_labelNum=flag; }
};

struct AstJumpGo : public AstNodeStmt {
    // Jump point; branch up to the JumpLabel
    // Parents:  {statement list}
private:
    AstJumpLabel*	m_labelp;	// [After V3Jump] Pointer to declaration
public:
    AstJumpGo(FileLine* fl, AstJumpLabel* labelp)
	: AstNodeStmt(fl) {
	m_labelp = labelp;
    }
    ASTNODE_NODE_FUNCS(JumpGo, JUMPGO)
    virtual bool broken() const { return !labelp()->brokeExistsAbove(); }
    virtual void cloneRelink() { if (m_labelp->clonep()) m_labelp = m_labelp->clonep()->castJumpLabel(); }
    virtual void dump(ostream& str);
    virtual int instrCount()	const { return instrCountBranch(); }
    virtual V3Hash sameHash() const { return V3Hash(labelp()); }
    virtual bool same(AstNode* samep) const {  // Also same if identical tree structure all the way down, but hard to detect
	return labelp()==samep->castJumpGo()->labelp(); }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isBrancher() const { return true; }	// SPECIAL: We don't process code after breaks
    AstJumpLabel* labelp() const { return m_labelp; }
};

struct AstUntilStable : public AstNodeStmt {
    // Quasi-while loop until given signals are stable
    // Parents: CFUNC (generally)
    // Children: VARREF, statements
    AstUntilStable(FileLine* fileline, AstVarRef* stablesp, AstNode* bodysp)
	: AstNodeStmt(fileline) {
	addNOp2p(stablesp); addNOp3p(bodysp);
    }
    ASTNODE_NODE_FUNCS(UntilStable, UNTILSTABLE)
    AstVarRef* stablesp()	const { return op2p()->castVarRef(); } // op2= list of variables that must become stable
    AstNode*	bodysp()	const { return op3p()->castNode(); }	// op3= body of loop
    void	addStablesp(AstVarRef* newp)	{ addOp2p(newp); }
    void	addBodysp(AstNode* newp)	{ addOp3p(newp); }
    virtual bool isGateOptimizable() const { return false; }	// Not relevant
    virtual bool isPredictOptimizable() const { return false; }	// Not relevant
    virtual int instrCount()	const { return instrCountBranch(); }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
};

struct AstChangeXor : public AstNodeBiComAsv {
    // A comparison to determine change detection, common & must be fast.
    // Returns 32-bit or 64-bit value where 0 indicates no change.
    // Parents: OR or LOGOR
    // Children: VARREF
    AstChangeXor(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
	: AstNodeBiComAsv(fl, lhsp, rhsp) {
	dtypeChgUInt32(); // Always used on, and returns word entities
    }
    ASTNODE_NODE_FUNCS(ChangeXor, CHANGEXOR)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opChangeXor(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f^ %r)"; }
    virtual string emitC() { return "VL_CHANGEXOR_%li(%lw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "^"; }
    virtual bool cleanOut() {return false;}  // Lclean && Rclean
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return widthInstrs(); }
};

struct AstChangeDet : public AstNodeStmt {
    // A comparison to determine change detection, common & must be fast.
private:
    bool	m_clockReq;	// Type of detection
public:
    // Null lhs+rhs used to indicate change needed with no spec vars
    AstChangeDet(FileLine* fl, AstNode* lhsp, AstNode* rhsp, bool clockReq)
	: AstNodeStmt(fl) {
	setNOp1p(lhsp); setNOp2p(rhsp); m_clockReq=clockReq;
	if (lhsp) widthSignedFrom(lhsp); }
    ASTNODE_NODE_FUNCS(ChangeDet, CHANGEDET)
    AstNode*	lhsp() 	const { return op1p(); }
    AstNode*	rhsp() 	const { return op2p(); }
    bool	isClockReq() const { return m_clockReq; }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual int instrCount()	const { return widthInstrs(); }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
};

struct AstInitial : public AstNode {
    AstInitial(FileLine* fl, AstNode* bodysp)
	: AstNode(fl) {
	addNOp1p(bodysp);
    }
    ASTNODE_NODE_FUNCS(Initial, INITIAL)
    AstNode*	bodysp() 	const { return op1p()->castNode(); }	// op1 = Expressions to evaluate
    // Special accessors
    bool isJustOneBodyStmt() const { return bodysp() && !bodysp()->nextp(); }
};

struct AstFinal : public AstNode {
    AstFinal(FileLine* fl, AstNode* bodysp)
	: AstNode(fl) {
	addNOp1p(bodysp);
    }
    ASTNODE_NODE_FUNCS(Final, FINAL)
    AstNode*	bodysp() 	const { return op1p()->castNode(); }	// op1 = Expressions to evaluate
};

struct AstInitArray : public AstNode {
    // Set a var to a large list of values
    // The values must be in sorted order, and not exceed the size of the var's array.
    // Parents: ASTVAR::init()
    // Children: CONSTs...
    AstInitArray(FileLine* fl, AstNode* initsp)
	: AstNode(fl) {
	addNOp1p(initsp);
    }
    ASTNODE_NODE_FUNCS(InitArray, INITARRAY)
    AstNode*	initsp() 	const { return op1p()->castNode(); }	// op1 = Initial value expressions
    void	addInitsp(AstNode* newp)	{ addOp1p(newp); }
};

struct AstPragma : public AstNode {
private:
    AstPragmaType	m_pragType;	// Type of pragma
public:
    // Pragmas don't result in any output code, they're just flags that affect
    // other processing in verilator.
    AstPragma(FileLine* fl, AstPragmaType pragType)
	: AstNode(fl) {
	m_pragType = pragType;
    }
    ASTNODE_NODE_FUNCS(Pragma, PRAGMA)
    AstPragmaType	pragType() 	const { return m_pragType; }	// *=type of the pragma
    virtual V3Hash sameHash() const { return V3Hash(pragType()); }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool same(AstNode* samep) const {
	return pragType()==samep->castPragma()->pragType(); }
};

struct AstStop : public AstNodeStmt {
    AstStop(FileLine* fl)
	: AstNodeStmt(fl) {}
    ASTNODE_NODE_FUNCS(Stop, STOP)
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool isPure() const { return false; }	// SPECIAL: $display has 'visual' ordering
    virtual bool isOutputter() const { return true; }	// SPECIAL: $display makes output
    virtual bool isUnlikely() const { return true; }
    virtual int instrCount()	const { return 0; }  // Rarely executes
    virtual V3Hash sameHash() const { return V3Hash(fileline()->lineno()); }
    virtual bool same(AstNode* samep) const {
	return fileline() == samep->fileline(); }
};

struct AstFinish : public AstNodeStmt {
    AstFinish(FileLine* fl)
	: AstNodeStmt(fl) {}
    ASTNODE_NODE_FUNCS(Finish, FINISH)
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool isPure() const { return false; }	// SPECIAL: $display has 'visual' ordering
    virtual bool isOutputter() const { return true; }	// SPECIAL: $display makes output
    virtual bool isUnlikely() const { return true; }
    virtual int instrCount()	const { return 0; }  // Rarely executes
    virtual V3Hash sameHash() const { return V3Hash(fileline()->lineno()); }
    virtual bool same(AstNode* samep) const {
	return fileline() == samep->fileline(); }
};

struct AstTraceDecl : public AstNodeStmt {
    // Trace point declaration
    // Separate from AstTraceInc; as a declaration can't be deleted
    // Parents:  {statement list}
    // Children: none
private:
    string	m_showname;	// Name of variable
    uint32_t	m_code;		// Trace identifier code; converted to ASCII by trace routines
    int		m_lsb;		// Property of var the trace details
    int		m_msb;		// Property of var the trace details
    uint32_t	m_arrayLsb;	// Property of var the trace details
    uint32_t	m_arrayMsb;	// Property of var the trace details
    uint32_t	m_codeInc;	// Code increment
public:
    AstTraceDecl(FileLine* fl, const string& showname, AstVar* varp)
	: AstNodeStmt(fl)
	, m_showname(showname) {
	widthSignedFrom(varp);
	m_code = 0;
	m_codeInc = varp->dtypep()->arrayElements() * varp->widthWords();
	AstBasicDType* bdtypep = varp->basicp();
	m_msb = bdtypep ? bdtypep->msbEndianed() : 0; 
	m_lsb = bdtypep ? bdtypep->lsbEndianed() : 0;
	if (AstArrayDType* adtypep = varp->dtypeSkipRefp()->castArrayDType()) {
	    m_arrayLsb = adtypep->arrayp()->lsbConst();
	    m_arrayMsb = adtypep->arrayp()->msbConst();
	} else {
	    m_arrayLsb = 0;
	    m_arrayMsb = 0;
	}
    }
    virtual int instrCount()	const { return 100; }  // Large...
    ASTNODE_NODE_FUNCS(TraceDecl, TRACEDECL)
    virtual string name()	const { return m_showname; }
    virtual bool maybePointedTo() const { return true; }
    virtual bool same(AstNode* samep) const { return false; }
    string showname()	const { return m_showname; }		// * = Var name
    // Details on what we're tracing
    uint32_t	code() const { return m_code; }
    void	code(uint32_t code) { m_code=code; }
    uint32_t	codeInc() const { return m_codeInc; }
    int		msbEndianed() const { return m_msb; }  // Note msb maybe < lsb if little endian
    int		lsbEndianed() const { return m_lsb; }
    uint32_t	arrayMsb() const { return m_arrayMsb; }
    uint32_t	arrayLsb() const { return m_arrayLsb; }
    uint32_t	arrayWidth() const { if (!arrayMsb()) return 0; return arrayMsb()-arrayLsb()+1; }
};

struct AstTraceInc : public AstNodeStmt {
    // Trace point; incremental change detect and dump
    // Parents:  {statement list}
    // Children: incremental value
private:
    AstTraceDecl*	m_declp;	// [After V3Trace] Pointer to declaration
public:
    AstTraceInc(FileLine* fl, AstTraceDecl* declp, AstNode* valuep)
	: AstNodeStmt(fl) {
	widthSignedFrom(declp);
	m_declp = declp;
	addNOp2p(valuep);
    }
    ASTNODE_NODE_FUNCS(TraceInc, TRACEINC)
    virtual bool broken() const { return !declp()->brokeExists(); }
    virtual void cloneRelink() { if (m_declp->clonep()) m_declp = m_declp->clonep()->castTraceDecl(); }
    virtual void dump(ostream& str);
    virtual int instrCount()	const { return 10+2*instrCountLd(); }
    virtual V3Hash sameHash() const { return V3Hash(declp()); }
    virtual bool same(AstNode* samep) const {
	return declp()==samep->castTraceInc()->declp(); }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool isOutputter() const { return true; }
    // but isPure()  true
    // op1 = Statements before the value
    AstNode*	precondsp()	const { return op1p()->castNode(); }	// op1= prepare statements for condition (exec every loop)
    void	addPrecondsp(AstNode* newp) { addOp1p(newp); }
    // op2 = Value to trace
    AstTraceDecl*	declp() const { return m_declp; }	// Where defined
    AstNode*	valuep() 	const { return op2p()->castNode(); }
};

struct AstActive : public AstNode {
    // Block of code with sensitivity activation
    // Parents:  MODULE | CFUNC
    // Children: SENTREE, statements
private:
    string	m_name;
    AstSenTree*	m_sensesp;
public:
    AstActive(FileLine* fileline, const string& name, AstSenTree* sensesp)
	: AstNode(fileline) {
	m_name = name;	// Copy it
	UASSERT(sensesp, "Sensesp required arg");
	m_sensesp = sensesp;
    }
    ASTNODE_NODE_FUNCS(Active, ACTIVE)
    virtual void dump(ostream& str=cout);
    virtual string name()	const { return m_name; }
    virtual bool broken() const { return (m_sensesp && !m_sensesp->brokeExists()); }
    virtual void cloneRelink() {
	if (m_sensesp->clonep()) {
	    m_sensesp = m_sensesp->clonep()->castSenTree();
	    UASSERT(m_sensesp, "Bad clone cross link: "<<this);
	}
    }
    // Statements are broken into pieces, as some must come before others.
    void	sensesp(AstSenTree* nodep) { m_sensesp=nodep; }
    AstSenTree*	sensesp() 	const { return m_sensesp; }
    // op1 = Sensitivity tree, if a clocked block in early stages
    void	sensesStorep(AstSenTree* nodep) { addOp1p(nodep); }
    AstSenTree*	sensesStorep() 	const { return op1p()->castSenTree(); }
    // op2 = Combo logic
    AstNode*	stmtsp() 	const { return op2p()->castNode(); }
    void addStmtsp(AstNode* nodep) { addOp2p(nodep); }
    // METHODS
    bool hasInitial() const { return m_sensesp->hasInitial(); }
    bool hasSettle() const { return m_sensesp->hasSettle(); }
    bool hasClocked() const { return m_sensesp->hasClocked(); }
};

struct AstAttrOf : public AstNode {
private:
    // Return a value of a attribute, for example a LSB or array LSB of a signal
    AstAttrType	m_attrType;	// What sort of extraction
public:
    AstAttrOf(FileLine* fl, AstAttrType attrtype, AstNode* fromp=NULL)
	: AstNode(fl) {
	setNOp1p(fromp);
	m_attrType = attrtype; }
    ASTNODE_NODE_FUNCS(AttrOf, ATTROF)
    AstNode*	fromp() const { return op1p(); }
    AstAttrType	attrType() const { return m_attrType; }
    virtual void dump(ostream& str=cout);
};

struct AstScopeName : public AstNodeMath {
    // For display %m and DPI context imports
    // Parents:  DISPLAY
    // Children: TEXT
private:
    bool	m_dpiExport;	// Is for dpiExport
public:
    AstScopeName(FileLine* fl) : AstNodeMath(fl), m_dpiExport(false) {
	dtypeChgUInt64(); }
    ASTNODE_NODE_FUNCS(ScopeName, SCOPENAME)
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return m_dpiExport==samep->castScopeName()->m_dpiExport; }
    virtual string emitVerilog() { return ""; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool cleanOut() { return true; }
    AstText*	scopeAttrp() const { return op1p()->castText(); }
    void 	scopeAttrp(AstNode* nodep) { addOp1p(nodep); }
    string scopeSymName() const;  // Name for __Vscope variable including children
    string scopePrettyName() const;  // Name for __Vscope printing
    bool dpiExport() const { return m_dpiExport; }
    void dpiExport(bool flag) { m_dpiExport=flag; }
};

struct AstUdpTable : public AstNode {
    AstUdpTable(FileLine* fl, AstNode* bodysp)
	: AstNode(fl) {
	addNOp1p(bodysp);
    }
    ASTNODE_NODE_FUNCS(UdpTable, UDPTABLE)
    AstUdpTableLine*	bodysp() 	const { return op1p()->castUdpTableLine(); }	// op1 = List of UdpTableLines
};

struct AstUdpTableLine : public AstNode {
    string	m_text;
public:
    AstUdpTableLine(FileLine* fl, const string& text)
	: AstNode(fl), m_text(text) {}
    ASTNODE_NODE_FUNCS(UdpTableLine, UDPTABLELINE)
    virtual string name()	const { return m_text; }
    string text() const { return m_text; }
};

//======================================================================
// non-ary ops

struct AstRand : public AstNodeTermop {
    // Return a random number, based upon width()
private:
    bool	m_reset;	// Random reset, versus always random
public:
    AstRand(FileLine* fl, int wwidth, bool reset) : AstNodeTermop(fl) {
	width(wwidth,wwidth); m_reset=reset; }
    AstRand(FileLine* fl) : AstNodeTermop(fl), m_reset(false) { }
    ASTNODE_NODE_FUNCS(Rand, RAND)
    virtual string emitVerilog() { return "%f$random"; }
    virtual string emitC() {
	return (m_reset ?
		"VL_RAND_RESET_%nq(%nw, %P)"
		:"VL_RANDOM_%nq(%nw, %P)"); }
    virtual bool cleanOut() { return true; }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual int instrCount()	const { return instrCountPli(); }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
};

struct AstTime : public AstNodeTermop {
    AstTime(FileLine* fl)	: AstNodeTermop(fl) {
	dtypeChgUInt64(); }
    ASTNODE_NODE_FUNCS(Time, TIME)
    virtual string emitVerilog() { return "%f$time"; }
    virtual string emitC() { return "VL_TIME_%nq()"; }
    virtual bool cleanOut() { return true; }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual int instrCount()	const { return instrCountTime(); }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
};

struct AstTimeD : public AstNodeTermop {
    AstTimeD(FileLine* fl)	: AstNodeTermop(fl) {
	dtypeChgDouble(); }
    ASTNODE_NODE_FUNCS(TimeD, TIMED)
    virtual string emitVerilog() { return "%f$realtime"; }
    virtual string emitC() { return "VL_TIME_D()"; }
    virtual bool cleanOut() { return true; }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual int instrCount()	const { return instrCountTime(); }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
};

struct AstUCFunc : public AstNodeMath {
    // User's $c function
    // Perhaps this should be an AstNodeListop; but there's only one list math right now
    AstUCFunc(FileLine* fl, AstNode* exprsp)
	: AstNodeMath(fl) {
	addNOp1p(exprsp);
    }
    ASTNODE_NODE_FUNCS(UCFunc, UCFUNC)
    virtual bool cleanOut() { return false; }
    virtual string emitVerilog() { V3ERROR_NA; return ""; }  // Implemented specially
    virtual string emitC() { V3ERROR_NA; return ""; }
    AstNode*	bodysp()	const { return op1p()->castNode(); }	// op1= expressions to print
    virtual bool isPure() const { return false; }	// SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const { return true; }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isSubstOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual int instrCount()	const { return instrCountPli(); }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
};

//======================================================================
// Unary ops

struct AstNegate : public AstNodeUniop {
    AstNegate(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    ASTNODE_NODE_FUNCS(Negate, NEGATE)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opNegate(lhs); }
    virtual string emitVerilog() { return "%f(- %l)"; }
    virtual string emitC() { return "VL_NEGATE_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return false;}
    virtual bool sizeMattersLhs() {return true;}
};
struct AstNegateD : public AstNodeUniop {
    AstNegateD(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeChgDouble(); }
    ASTNODE_NODE_FUNCS(NegateD, NEGATED)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opNegateD(lhs); }
    virtual string emitVerilog() { return "%f(- %l)"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual string emitSimpleOperator() { return "-"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return false;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return instrCountDouble(); }
    virtual bool doubleFlavor() const { return true; }
};
struct AstRedAnd : public AstNodeUniop {
    AstRedAnd(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(RedAnd, REDAND)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opRedAnd(lhs); }
    virtual string emitVerilog() { return "%f(& %l)"; }
    virtual string emitC() { return "VL_REDAND_%nq%lq(%nw,%lw, %P, %li)"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
};
struct AstRedOr : public AstNodeUniop {
    AstRedOr(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(RedOr, REDOR)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opRedOr(lhs); }
    virtual string emitVerilog() { return "%f(| %l)"; }
    virtual string emitC() { return "VL_REDOR_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
};
struct AstRedXor : public AstNodeUniop {
    AstRedXor(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(RedXor, REDXOR)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opRedXor(lhs); }
    virtual string emitVerilog() { return "%f(^ %l)"; }
    virtual string emitC() { return "VL_REDXOR_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {int w = lhsp()->width();
	return (w!=1 && w!=2 && w!=4 && w!=8 && w!=16); }
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return 1+V3Number::log2b(width()); }
};
struct AstRedXnor : public AstNodeUniop {
    // AstRedXnors are replaced with AstRedXors in V3Const.
    AstRedXnor(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(RedXnor, REDXNOR)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opRedXnor(lhs); }
    virtual string emitVerilog() { return "%f(~^ %l)"; }
    virtual string emitC() { v3fatalSrc("REDXNOR should have became REDXOR"); return ""; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return 1+V3Number::log2b(width()); }
};

struct AstLogNot : public AstNodeUniop {
    AstLogNot(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(LogNot, LOGNOT)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opLogNot(lhs); }
    virtual string emitVerilog() { return "%f(! %l)"; }
    virtual string emitC() { return "VL_LOGNOT_%nq%lq(%nw,%lw, %P, %li)"; }
    virtual string emitSimpleOperator() { return "!"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
};
struct AstNot : public AstNodeUniop {
    AstNot(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    ASTNODE_NODE_FUNCS(Not, NOT)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opNot(lhs); }
    virtual string emitVerilog() { return "%f(~ %l)"; }
    virtual string emitC() { return "VL_NOT_%lq(%lW, %P, %li)"; }
    virtual string emitSimpleOperator() { return "~"; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return false;}
    virtual bool sizeMattersLhs() {return true;}
};
struct AstExtend : public AstNodeUniop {
    // Expand a value into a wider entity by 0 extension.  Width is implied from nodep->width()
    AstExtend(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(Extend, EXTEND)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opAssign(lhs); }
    virtual string emitVerilog() { return "%l"; }
    virtual string emitC() { return "VL_EXTEND_%nq%lq(%nw,%lw, %P, %li)"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}  // Because the EXTEND operator self-casts
    virtual int instrCount()	const { return 0; }
};
struct AstExtendS : public AstNodeUniop {
    // Expand a value into a wider entity by sign extension.  Width is implied from nodep->width()
    AstExtendS(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(ExtendS, EXTENDS)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opExtendS(lhs); }
    virtual string emitVerilog() { return "%l"; }
    virtual string emitC() { return "VL_EXTENDS_%nq%lq(%nw,%lw, %P, %li)"; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}  // Because the EXTEND operator self-casts
    virtual int instrCount()	const { return 0; }
    virtual bool signedFlavor() const { return true; }
};
struct AstSigned : public AstNodeUniop {
    // $signed(lhs)
    AstSigned(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	if (v3Global.assertDTypesResolved()) { v3fatalSrc("not coded to create after dtypes resolved"); }
    }
    ASTNODE_NODE_FUNCS(Signed, SIGNED)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opAssign(lhs); out.isSigned(false); }
    virtual string emitVerilog() { return "%f$signed(%l)"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return false;}  // Eliminated before matters
    virtual bool sizeMattersLhs() {return true;}  // Eliminated before matters
    virtual int instrCount()	const { return 0; }
};
struct AstUnsigned : public AstNodeUniop {
    // $unsigned(lhs)
    AstUnsigned(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	if (v3Global.assertDTypesResolved()) { v3fatalSrc("not coded to create after dtypes resolved"); }
    }
    ASTNODE_NODE_FUNCS(Unsigned, UNSIGNED)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opAssign(lhs); out.isSigned(false); }
    virtual string emitVerilog() { return "%f$unsigned(%l)"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return false;}  // Eliminated before matters
    virtual bool sizeMattersLhs() {return true;}  // Eliminated before matters
    virtual int instrCount()	const { return 0; }
};
struct AstRToIS : public AstNodeUniop {
    // $rtoi(lhs)
    AstRToIS(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeChgSigned32(); }
    ASTNODE_NODE_FUNCS(RToIS, RTOIS)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opRToIS(lhs); }
    virtual string emitVerilog() { return "%f$rtoi(%l)"; }
    virtual string emitC() { return "VL_RTOI_I_D(%li)"; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return false;}  // Eliminated before matters
    virtual bool sizeMattersLhs() {return false;}  // Eliminated before matters
    virtual int instrCount()	const { return instrCountDouble(); }
};
struct AstRToIRoundS : public AstNodeUniop {
    AstRToIRoundS(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeChgSigned32(); }
    ASTNODE_NODE_FUNCS(RToIRoundS, RTOIROUNDS)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opRToIRoundS(lhs); }
    virtual string emitVerilog() { return "%f$rtoi_rounded(%l)"; }
    virtual string emitC() { return "VL_RTOIROUND_I_D(%li)"; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return false;}  // Eliminated before matters
    virtual bool sizeMattersLhs() {return false;}  // Eliminated before matters
    virtual int instrCount()	const { return instrCountDouble(); }
};
struct AstIToRD : public AstNodeUniop {
    AstIToRD(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeChgDouble(); }
    ASTNODE_NODE_FUNCS(IToRD, ITORD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opIToRD(lhs); }
    virtual string emitVerilog() { return "%f$itor(%l)"; }
    virtual string emitC() { return "VL_ITOR_D_I(%li)"; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return false;}  // Eliminated before matters
    virtual bool sizeMattersLhs() {return false;}  // Eliminated before matters
    virtual int instrCount()	const { return instrCountDouble(); }
};
struct AstRealToBits : public AstNodeUniop {
    AstRealToBits(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeChgUInt64(); }
    ASTNODE_NODE_FUNCS(RealToBits, REALTOBITS)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opRealToBits(lhs); }
    virtual string emitVerilog() { return "%f$realtobits(%l)"; }
    virtual string emitC() { return "VL_CVT_Q_D(%li)"; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return false;}  // Eliminated before matters
    virtual bool sizeMattersLhs() {return false;}  // Eliminated before matters
    virtual int instrCount()	const { return instrCountDouble(); }
};
struct AstBitsToRealD : public AstNodeUniop {
    AstBitsToRealD(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeChgDouble(); }
    ASTNODE_NODE_FUNCS(BitsToRealD, BITSTOREALD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opBitsToRealD(lhs); }
    virtual string emitVerilog() { return "%f$bitstoreal(%l)"; }
    virtual string emitC() { return "VL_CVT_D_Q(%li)"; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return false;}  // Eliminated before matters
    virtual bool sizeMattersLhs() {return false;}  // Eliminated before matters
    virtual int instrCount()	const { return instrCountDouble(); }
};

struct AstCLog2 : public AstNodeUniop {
    AstCLog2(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(CLog2, CLOG2)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opCLog2(lhs); }
    virtual string emitVerilog() { return "%f$clog2(%l)"; }
    virtual string emitC() { return "VL_CLOG2_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*16; }
};
struct AstCountOnes : public AstNodeUniop {
    // Number of bits set in vector
    AstCountOnes(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(CountOnes, COUNTONES)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opCountOnes(lhs); }
    virtual string emitVerilog() { return "%f$countones(%l)"; }
    virtual string emitC() { return "VL_COUNTONES_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*16; }
};
struct AstIsUnknown : public AstNodeUniop {
    // True if any unknown bits
    AstIsUnknown(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(IsUnknown, ISUNKNOWN)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opIsUnknown(lhs); }
    virtual string emitVerilog() { return "%f$isunknown(%l)"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return false;}
    virtual bool sizeMattersLhs() {return false;}
};
struct AstOneHot : public AstNodeUniop {
    // True if only single bit set in vector
    AstOneHot(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(OneHot, ONEHOT)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opOneHot(lhs); }
    virtual string emitVerilog() { return "%f$onehot(%l)"; }
    virtual string emitC() { return "VL_ONEHOT_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*4; }
};
struct AstOneHot0 : public AstNodeUniop {
    // True if only single bit, or no bits set in vector
    AstOneHot0(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(OneHot0, ONEHOT0)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opOneHot0(lhs); }
    virtual string emitVerilog() { return "%f$onehot0(%l)"; }
    virtual string emitC() { return "VL_ONEHOT0_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*3; }
};

struct AstCast : public AstNode {
    // Cast to appropriate data type - note lhsp is value, to match AstTypedef, AstCCast, etc
    AstCast(FileLine* fl, AstNode* lhsp, AstNodeDType* dtp) : AstNode(fl) {
	setOp1p(lhsp); setOp2p(dtp);
	if (dtp) { widthSignedFrom(dtp); }
    }
    ASTNODE_NODE_FUNCS(Cast, CAST)
    virtual string emitVerilog() { return "((%r)'(%l))"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool cleanOut() { V3ERROR_NA; return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
    AstNode* lhsp() const { return op1p(); }
    AstNodeDType* dtypep() const { return op2p()->castNodeDType(); }
};

struct AstCCast : public AstNodeUniop {
    // Cast to C-based data type
private:
    int		m_size;
public:
    AstCCast(FileLine* fl, AstNode* lhsp, int setwidth) : AstNodeUniop(fl, lhsp) {
	m_size=setwidth;
	if (setwidth) { width(setwidth,setwidth); }
    }
    AstCCast(FileLine* fl, AstNode* lhsp, AstNode* typeFromp) : AstNodeUniop(fl, lhsp) {
	if (typeFromp) { widthSignedFrom(typeFromp); }
	m_size=width();
    }
    ASTNODE_NODE_FUNCS(CCast, CCAST)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opAssign(lhs); }
    virtual string emitVerilog() { return "%f$_CAST(%l)"; }
    virtual string emitC() { return "VL_CAST_%nq%lq(%nw,%lw, %P, %li)"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}  // Special cased in V3Cast
    virtual V3Hash sameHash() const { return V3Hash(size()); }
    virtual bool same(AstNode* samep) const { return size()==samep->castCCast()->size(); }
    virtual void dump(ostream& str=cout);
    //
    int size()	const { return m_size; }
};

struct AstCvtPackString : public AstNodeUniop {
    // Convert to Verilator Packed Pack (aka Pack)
    AstCvtPackString(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeChgUInt64(); }  // Really, width should be dtypep -> STRING
    ASTNODE_NODE_FUNCS(CvtPackString, CVTPACKSTRING)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { V3ERROR_NA; }
    virtual string emitVerilog() { return "%f$_CAST(%l)"; }
    virtual string emitC() { return "VL_CVT_PACK_STR_N%lq(%lW, %li)"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
};

struct AstFEof : public AstNodeUniop {
    AstFEof(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(FEof, FEOF)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { V3ERROR_NA; }
    virtual string emitVerilog() { return "%f$feof(%l)"; }
    virtual string emitC() { return "(%li ? feof(VL_CVT_I_FP(%li)) : true)"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*16; }
    AstNode*	filep() const { return lhsp(); }
};

struct AstFGetC : public AstNodeUniop {
    AstFGetC(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(FGetC, FGETC)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { V3ERROR_NA; }
    virtual string emitVerilog() { return "%f$fgetc(%l)"; }
    // Non-existent filehandle returns EOF
    virtual string emitC() { return "(%li ? fgetc(VL_CVT_I_FP(%li)) : -1)"; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*64; }
    AstNode*	filep() const { return lhsp(); }
};

struct AstCeilD : public AstNodeUniop {
    AstCeilD(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeChgDouble(); }
    ASTNODE_NODE_FUNCS(CeilD, CEILD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) {
	out.setDouble(ceil(lhs.toDouble())); }
    virtual string emitVerilog() { return "%f$ceil(%l)"; }
    virtual string emitC() { return "ceil(%li)"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return false;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return instrCountDoubleTrig(); }
    virtual bool doubleFlavor() const { return true; }
};

struct AstExpD : public AstNodeUniop {
    AstExpD(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeChgDouble(); }
    ASTNODE_NODE_FUNCS(ExpD, EXPD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) {
	out.setDouble(exp(lhs.toDouble())); }
    virtual string emitVerilog() { return "%f$exp(%l)"; }
    virtual string emitC() { return "exp(%li)"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return false;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return instrCountDoubleTrig(); }
    virtual bool doubleFlavor() const { return true; }
};

struct AstFloorD : public AstNodeUniop {
    AstFloorD(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeChgDouble(); }
    ASTNODE_NODE_FUNCS(FloorD, FLOORD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) {
	out.setDouble(floor(lhs.toDouble())); }
    virtual string emitVerilog() { return "%f$floor(%l)"; }
    virtual string emitC() { return "floor(%li)"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return false;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return instrCountDoubleTrig(); }
    virtual bool doubleFlavor() const { return true; }
};

struct AstLogD : public AstNodeUniop {
    AstLogD(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeChgDouble(); }
    ASTNODE_NODE_FUNCS(LogD, LOGD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) {
	out.setDouble(log(lhs.toDouble())); }
    virtual string emitVerilog() { return "%f$ln(%l)"; }
    virtual string emitC() { return "log(%li)"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return false;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return instrCountDoubleTrig(); }
    virtual bool doubleFlavor() const { return true; }
};

struct AstLog10D : public AstNodeUniop {
    AstLog10D(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeChgDouble(); }
    ASTNODE_NODE_FUNCS(Log10D, LOG10D)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) {
	out.setDouble(log10(lhs.toDouble())); }
    virtual string emitVerilog() { return "%f$log10(%l)"; }
    virtual string emitC() { return "log10(%li)"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return false;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return instrCountDoubleTrig(); }
    virtual bool doubleFlavor() const { return true; }
};

struct AstSqrtD : public AstNodeUniop {
    AstSqrtD(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeChgDouble(); }
    ASTNODE_NODE_FUNCS(SqrtD, SQRTD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) {
	out.setDouble(sqrt(lhs.toDouble())); }
    virtual string emitVerilog() { return "%f$sqrt(%l)"; }
    virtual string emitC() { return "sqrt(%li)"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return false;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return instrCountDoubleTrig(); }
    virtual bool doubleFlavor() const { return true; }
};

//======================================================================
// Binary ops

struct AstLogOr : public AstNodeBiop {
    AstLogOr(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(LogOr, LOGOR)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLogOr(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f|| %r)"; }
    virtual string emitC() { return "VL_LOGOR_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "||"; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()+instrCountBranch(); }
};
struct AstLogAnd : public AstNodeBiop {
    AstLogAnd(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(LogAnd, LOGAND)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLogAnd(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f&& %r)"; }
    virtual string emitC() { return "VL_LOGAND_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "&&"; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()+instrCountBranch(); }
};
struct AstLogIf : public AstNodeBiop {
    AstLogIf(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(LogIf, LOGIF)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { V3ERROR_NA; }
    virtual string emitVerilog() { return "%k(%l %f-> %r)"; }
    virtual string emitC() { return "VL_LOGIF_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "->"; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()+instrCountBranch(); }
};
struct AstLogIff : public AstNodeBiCom {
    AstLogIff(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiCom(fl, lhsp, rhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(LogIff, LOGIFF)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { V3ERROR_NA; }
    virtual string emitVerilog() { return "%k(%l %f<-> %r)"; }
    virtual string emitC() { return "VL_LOGIFF_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "<->"; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()+instrCountBranch(); }
};
struct AstOr : public AstNodeBiComAsv {
    AstOr(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiComAsv(fl, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    ASTNODE_NODE_FUNCS(Or, OR)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opOr(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f| %r)"; }
    virtual string emitC() { return "VL_OR_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "|"; }
    virtual bool cleanOut() {V3ERROR_NA; return false;}  // Lclean && Rclean
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
struct AstAnd : public AstNodeBiComAsv {
    AstAnd(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiComAsv(fl, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    ASTNODE_NODE_FUNCS(And, AND)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opAnd(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f& %r)"; }
    virtual string emitC() { return "VL_AND_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "&"; }
    virtual bool cleanOut() {V3ERROR_NA; return false;}  // Lclean || Rclean
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
struct AstXor : public AstNodeBiComAsv {
    AstXor(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiComAsv(fl, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    ASTNODE_NODE_FUNCS(Xor, XOR)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opXor(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f^ %r)"; }
    virtual string emitC() { return "VL_XOR_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "^"; }
    virtual bool cleanOut() {return false;}  // Lclean && Rclean
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
struct AstXnor : public AstNodeBiComAsv {
    AstXnor(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiComAsv(fl, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    ASTNODE_NODE_FUNCS(Xnor, XNOR)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opXnor(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f^ ~ %r)"; }
    virtual string emitC() { return "VL_XNOR_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "^ ~"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return true;}
};
struct AstEq : public AstNodeBiCom {
    AstEq(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiCom(fl, lhsp, rhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(Eq, EQ)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opEq(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f== %r)"; }
    virtual string emitC() { return "VL_EQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "=="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
struct AstEqD : public AstNodeBiCom {
    AstEqD(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiCom(fl, lhsp, rhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(EqD, EQD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opEqD(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f== %r)"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual string emitSimpleOperator() { return "=="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return instrCountDouble(); }
    virtual bool doubleFlavor() const { return true; }
};
struct AstNeq : public AstNodeBiCom {
    AstNeq(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiCom(fl, lhsp, rhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(Neq, NEQ)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opNeq(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f!= %r)"; }
    virtual string emitC() { return "VL_NEQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "!="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
struct AstNeqD : public AstNodeBiCom {
    AstNeqD(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiCom(fl, lhsp, rhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(NeqD, NEQD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opNeqD(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f!= %r)"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual string emitSimpleOperator() { return "!="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return instrCountDouble(); }
    virtual bool doubleFlavor() const { return true; }
};
struct AstLt : public AstNodeBiop {
    AstLt(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(Lt, LT)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLt(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f< %r)"; }
    virtual string emitC() { return "VL_LT_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "<"; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
struct AstLtD : public AstNodeBiop {
    AstLtD(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(LtD, LTD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLtD(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f< %r)"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual string emitSimpleOperator() { return "<"; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return instrCountDouble(); }
    virtual bool doubleFlavor() const { return true; }
};
struct AstLtS : public AstNodeBiop {
    AstLtS(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(LtS, LTS)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLtS(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f< %r)"; }
    virtual string emitC() { return "VL_LTS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return ""; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual bool signedFlavor() const { return true; }
};
struct AstGt : public AstNodeBiop {
    AstGt(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(Gt, GT)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opGt(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f> %r)"; }
    virtual string emitC() { return "VL_GT_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return ">"; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
struct AstGtD : public AstNodeBiop {
    AstGtD(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(GtD, GTD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opGtD(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f> %r)"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual string emitSimpleOperator() { return ">"; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return instrCountDouble(); }
    virtual bool doubleFlavor() const { return true; }
};
struct AstGtS : public AstNodeBiop {
    AstGtS(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(GtS, GTS)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opGtS(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f> %r)"; }
    virtual string emitC() { return "VL_GTS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return ""; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual bool signedFlavor() const { return true; }
};
struct AstGte : public AstNodeBiop {
    AstGte(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(Gte, GTE)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opGte(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f>= %r)"; }
    virtual string emitC() { return "VL_GTE_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return ">="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
struct AstGteD : public AstNodeBiop {
    AstGteD(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(GteD, GTED)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opGteD(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f>= %r)"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual string emitSimpleOperator() { return ">="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return instrCountDouble(); }
    virtual bool doubleFlavor() const { return true; }
};
struct AstGteS : public AstNodeBiop {
    AstGteS(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(GteS, GTES)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opGteS(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f>= %r)"; }
    virtual string emitC() { return "VL_GTES_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return ""; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual bool signedFlavor() const { return true; }
};
struct AstLte : public AstNodeBiop {
    AstLte(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(Lte, LTE)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLte(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f<= %r)"; }
    virtual string emitC() { return "VL_LTE_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "<="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
struct AstLteD : public AstNodeBiop {
    AstLteD(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(LteD, LTED)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLteD(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f<= %r)"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual string emitSimpleOperator() { return "<="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return instrCountDouble(); }
    virtual bool doubleFlavor() const { return true; }
};
struct AstLteS : public AstNodeBiop {
    AstLteS(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(LteS, LTES)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLteS(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f<= %r)"; }
    virtual string emitC() { return "VL_LTES_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return ""; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual bool signedFlavor() const { return true; }
};
struct AstShiftL : public AstNodeBiop {
    AstShiftL(FileLine* fl, AstNode* lhsp, AstNode* rhsp, int setwidth=0)
	: AstNodeBiop(fl, lhsp, rhsp) {
	if (setwidth) { width(setwidth,setwidth); }
    }
    ASTNODE_NODE_FUNCS(ShiftL, SHIFTL)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opShiftL(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f<< %r)"; }
    virtual string emitC() { return "VL_SHIFTL_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "<<"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return false;}
};
struct AstShiftR : public AstNodeBiop {
    AstShiftR(FileLine* fl, AstNode* lhsp, AstNode* rhsp, int setwidth=0)
	: AstNodeBiop(fl, lhsp, rhsp) {
	if (setwidth) { width(setwidth,setwidth); }
    }
    ASTNODE_NODE_FUNCS(ShiftR, SHIFTR)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opShiftR(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f>> %r)"; }
    virtual string emitC() { return "VL_SHIFTR_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return ">>"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}  // LHS size might be > output size, so don't want to force size
};
struct AstShiftRS : public AstNodeBiop {
    AstShiftRS(FileLine* fl, AstNode* lhsp, AstNode* rhsp, int setwidth=0)
	: AstNodeBiop(fl, lhsp, rhsp) {
	if (setwidth) { width(setwidth,setwidth); }
    }
    ASTNODE_NODE_FUNCS(ShiftRS, SHIFTRS)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opShiftRS(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f>>> %r)"; }
    virtual string emitC() { return "VL_SHIFTRS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return ""; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual bool signedFlavor() const { return true; }
};
struct AstAdd : public AstNodeBiComAsv {
    AstAdd(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiComAsv(fl, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    ASTNODE_NODE_FUNCS(Add, ADD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opAdd(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f+ %r)"; }
    virtual string emitC() { return "VL_ADD_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "+"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return true;}
};
struct AstAddD : public AstNodeBiComAsv {
    AstAddD(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiComAsv(fl, lhsp, rhsp) {
	dtypeChgDouble(); }
    ASTNODE_NODE_FUNCS(AddD, ADDD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opAddD(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f+ %r)"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual string emitSimpleOperator() { return "+"; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return instrCountDouble(); }
    virtual bool doubleFlavor() const { return true; }
};
struct AstSub : public AstNodeBiop {
    AstSub(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    ASTNODE_NODE_FUNCS(Sub, SUB)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opSub(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f- %r)"; }
    virtual string emitC() { return "VL_SUB_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "-"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return true;}
};
struct AstSubD : public AstNodeBiop {
    AstSubD(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeChgDouble(); }
    ASTNODE_NODE_FUNCS(SubD, SUBD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opSubD(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f- %r)"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual string emitSimpleOperator() { return "-"; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return instrCountDouble(); }
    virtual bool doubleFlavor() const { return true; }
};
struct AstMul : public AstNodeBiComAsv {
    AstMul(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiComAsv(fl, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    ASTNODE_NODE_FUNCS(Mul, MUL)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opMul(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f* %r)"; }
    virtual string emitC() { return "VL_MUL_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "*"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return true;}
    virtual int instrCount()	const { return widthInstrs()*instrCountMul(); }
};
struct AstMulD : public AstNodeBiComAsv {
    AstMulD(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiComAsv(fl, lhsp, rhsp) {
	dtypeChgDouble(); }
    ASTNODE_NODE_FUNCS(MulD, MULD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opMulD(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f* %r)"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual string emitSimpleOperator() { return "*"; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return true;}
    virtual int instrCount()	const { return instrCountDouble(); }
    virtual bool doubleFlavor() const { return true; }
};
struct AstMulS : public AstNodeBiComAsv {
    AstMulS(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiComAsv(fl, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    ASTNODE_NODE_FUNCS(MulS, MULS)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opMulS(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f* %r)"; }
    virtual string emitC() { return "VL_MULS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return ""; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return true;}
    virtual int instrCount()	const { return widthInstrs()*instrCountMul(); }
    virtual bool signedFlavor() const { return true; }
};
struct AstDiv : public AstNodeBiop {
    AstDiv(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    ASTNODE_NODE_FUNCS(Div, DIV)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opDiv(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f/ %r)"; }
    virtual string emitC() { return "VL_DIV_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return true;}
    virtual int instrCount()	const { return widthInstrs()*instrCountDiv(); }
};
struct AstDivD : public AstNodeBiop {
    AstDivD(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeChgDouble(); }
    ASTNODE_NODE_FUNCS(DivD, DIVD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opDivD(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f/ %r)"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual string emitSimpleOperator() { return "/"; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return instrCountDoubleDiv(); }
    virtual bool doubleFlavor() const { return true; }
};
struct AstDivS : public AstNodeBiop {
    AstDivS(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    ASTNODE_NODE_FUNCS(DivS, DIVS)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opDivS(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f/ %r)"; }
    virtual string emitC() { return "VL_DIVS_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return true;}
    virtual int instrCount()	const { return widthInstrs()*instrCountDiv(); }
    virtual bool signedFlavor() const { return true; }
};
struct AstModDiv : public AstNodeBiop {
    AstModDiv(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    ASTNODE_NODE_FUNCS(ModDiv, MODDIV)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opModDiv(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f%% %r)"; }
    virtual string emitC() { return "VL_MODDIV_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return true;}
    virtual int instrCount()	const { return widthInstrs()*instrCountDiv(); }
};
struct AstModDivS : public AstNodeBiop {
    AstModDivS(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    ASTNODE_NODE_FUNCS(ModDivS, MODDIVS)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opModDivS(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f%% %r)"; }
    virtual string emitC() { return "VL_MODDIVS_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return true;}
    virtual int instrCount()	const { return widthInstrs()*instrCountDiv(); }
    virtual bool signedFlavor() const { return true; }
};
struct AstPow : public AstNodeBiop {
    AstPow(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    ASTNODE_NODE_FUNCS(Pow, POW)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opPow(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f** %r)"; }
    virtual string emitC() { return "VL_POW_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*instrCountMul(); }
};
struct AstPowD : public AstNodeBiop {
    AstPowD(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeChgDouble(); }
    ASTNODE_NODE_FUNCS(PowD, POWD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opPowD(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f** %r)"; }
    virtual string emitC() { return "pow(%li,%ri)"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return instrCountDoubleDiv(); }
    virtual bool doubleFlavor() const { return true; }
};
struct AstPowS : public AstNodeBiop {
    AstPowS(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    ASTNODE_NODE_FUNCS(PowS, POWS)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opPowS(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f** %r)"; }
    virtual string emitC() { return "VL_POWS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*instrCountMul(); }
    virtual bool signedFlavor() const { return true; }
};
struct AstEqCase : public AstNodeBiCom {
    AstEqCase(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiCom(fl, lhsp, rhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(EqCase, EQCASE)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opCaseEq(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f=== %r)"; }
    virtual string emitC() { return "VL_EQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "=="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
struct AstNeqCase : public AstNodeBiCom {
    AstNeqCase(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiCom(fl, lhsp, rhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(NeqCase, NEQCASE)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opCaseNeq(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f!== %r)"; }
    virtual string emitC() { return "VL_NEQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "!="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
struct AstEqWild : public AstNodeBiop {
    // Note wildcard operator rhs differs from lhs
    AstEqWild(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(EqWild, EQWILD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opWildEq(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f==? %r)"; }
    virtual string emitC() { return "VL_EQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "=="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
struct AstNeqWild : public AstNodeBiop {
    AstNeqWild(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeChgLogicBool(); }
    ASTNODE_NODE_FUNCS(NeqWild, NEQWILD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opWildNeq(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f!=? %r)"; }
    virtual string emitC() { return "VL_NEQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "!="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
struct AstConcat : public AstNodeBiop {
    // If you're looking for {#{}}, see AstReplicate
    AstConcat(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	if (lhsp->width() && rhsp->width()) width(lhsp->width()+rhsp->width(),lhsp->width()+rhsp->width());
    }
    ASTNODE_NODE_FUNCS(Concat, CONCAT)
    virtual string emitVerilog() { return "%f{%l, %k%r}"; }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opConcat(lhs,rhs); }
    virtual string emitC() { return "VL_CONCAT_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*2; }
};
struct AstReplicate : public AstNodeBiop {
    AstReplicate(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {}
    AstReplicate(FileLine* fl, AstNode* lhsp, uint32_t repCount)
	: AstNodeBiop(fl, lhsp, new AstConst(fl, repCount)) {}
    ASTNODE_NODE_FUNCS(Replicate, REPLICATE)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opRepl(lhs,rhs); }
    virtual string emitVerilog() { return "%f{%l{%k%r}}"; }
    virtual string emitC() { return "VL_REPLICATE_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*2; }
};
struct AstBufIf1 : public AstNodeBiop {
    // lhs is enable, rhs is data to drive
    AstBufIf1(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    ASTNODE_NODE_FUNCS(BufIf1, BUFIF1)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opBufIf1(lhs,rhs); }
    virtual string emitVerilog() { return "bufif(%r,%l)"; }
    virtual string emitC() { V3ERROR_NA; return "";}  // Lclean || Rclean
    virtual string emitSimpleOperator() { V3ERROR_NA; return "";}  // Lclean || Rclean
    virtual bool cleanOut() {V3ERROR_NA; return "";}  // Lclean || Rclean
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
struct AstFGetS : public AstNodeBiop {
    AstFGetS(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(FGetS, FGETS)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { V3ERROR_NA; }
    virtual string emitVerilog() { return "%f$fgets(%l,%r)"; }
    virtual string emitC() { return "VL_FGETS_%nqX%rq(%lw, %P, &(%li), %ri)"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*64; }
    AstNode*	strgp() const { return lhsp(); }
    AstNode*	filep() const { return rhsp(); }
};

//======================================================================
// SysVerilog assertions

struct AstVAssert : public AstNodeStmt {
    // Verilog Assertion
    // Parents:  {statement list}
    // Children: expression, if pass statements, if fail statements
    AstVAssert(FileLine* fl, AstNode* propp, AstNode* passsp, AstNode* failsp)
	: AstNodeStmt(fl) {
	addOp1p(propp);
	addNOp2p(passsp);
	addNOp3p(failsp);
    }
    ASTNODE_NODE_FUNCS(VAssert, VASSERT)
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
    AstNode*	propp()		const { return op1p(); }	// op1 = property
    AstNode*	passsp()	const { return op2p(); }	// op2 = if passes
    AstNode*	failsp()	const { return op3p(); }	// op3 = if fails
};

//======================================================================
// Assertions

struct AstClocking : public AstNode {
    // Set default clock region
    // Parents:  MODULE
    // Children: Assertions
    AstClocking(FileLine* fl, AstNodeSenItem* sensesp, AstNode* bodysp)
	: AstNode(fl) {
	addOp1p(sensesp);
	addNOp2p(bodysp);
    }
    ASTNODE_NODE_FUNCS(Clocking, CLOCKING)
    AstNodeSenItem* sensesp() 	const { return op1p()->castNodeSenItem(); }	// op1 = Sensitivity list
    AstNode*	bodysp() 	const { return op2p(); }	// op2 = Body
};

//======================================================================
// PSL

struct AstPslDefClock : public AstNode {
    // Set default PSL clock
    // Parents:  MODULE
    // Children: SENITEM
    AstPslDefClock(FileLine* fl, AstNodeSenItem* sensesp)
	: AstNode(fl) {
	addNOp1p(sensesp);
    }
    ASTNODE_NODE_FUNCS(PslDefClock, PSLDEFCLOCK)
    AstNodeSenItem* sensesp() const { return op1p()->castNodeSenItem(); }	// op1 = Sensitivity list
};

struct AstPslClocked : public AstNode {
    // A clocked property
    // Parents:  ASSERT|COVER (property)
    // Children: SENITEM, Properties
    AstPslClocked(FileLine* fl, AstNodeSenItem* sensesp, AstNode* disablep, AstNode* propp)
	: AstNode(fl) {
	addNOp1p(sensesp);
	addNOp2p(disablep);
	addOp3p(propp);
    }
    ASTNODE_NODE_FUNCS(PslClocked, PSLCLOCKED)
    AstNodeSenItem* sensesp() 	const { return op1p()->castNodeSenItem(); }	// op1 = Sensitivity list
    AstNode*	disablep()	const { return op2p(); }	// op2 = disable
    AstNode*	propp()		const { return op3p(); }	// op3 = property
};

struct AstPslAssert : public AstNodeStmt {
    // Psl Assertion
    // Parents:  {statement list}
    // Children: expression, report string
private:
    string	m_name;		// Name to report
public:
    AstPslAssert(FileLine* fl, AstNode* propp, const string& name="")
	: AstNodeStmt(fl)
	, m_name(name) {
	addOp1p(propp);
    }
    ASTNODE_NODE_FUNCS(PslAssert, PSLASSERT)
    virtual string name()	const { return m_name; }		// * = Var name
    virtual V3Hash sameHash() const { return V3Hash(name()); }
    virtual bool same(AstNode* samep) const { return samep->name() == name(); }
    AstNode*	propp()		const { return op1p(); }	// op1 = property
    AstSenTree*	sentreep()	const { return op2p()->castSenTree(); }	// op2 = clock domain
    void sentreep(AstSenTree* sentreep)  { addOp2p(sentreep); }	// op2 = clock domain
};

struct AstPslCover : public AstNodeStmt {
    // Psl Cover
    // Parents:  {statement list}
    // Children: expression, report string
private:
    string	m_name;		// Name to report
public:
    AstPslCover(FileLine* fl, AstNode* propp, AstNode* stmtsp, const string& name="")
	: AstNodeStmt(fl)
	, m_name(name) {
	addOp1p(propp);
	addNOp4p(stmtsp);
    }
    ASTNODE_NODE_FUNCS(PslCover, PSLCOVER)
    virtual string name()	const { return m_name; }		// * = Var name
    virtual V3Hash sameHash() const { return V3Hash(name()); }
    virtual bool same(AstNode* samep) const { return samep->name() == name(); }
    virtual void name(const string& name) { m_name = name; }
    AstNode*	propp()		const { return op1p(); }	// op1 = property
    AstSenTree*	sentreep()	const { return op2p()->castSenTree(); }	// op2 = clock domain
    void sentreep(AstSenTree* sentreep)  { addOp2p(sentreep); }	// op2 = clock domain
    AstNode*	coverincp()	const { return op3p(); }	// op3 = coverage node
    void coverincp(AstCoverInc* nodep)	{ addOp3p(nodep); }	// op3 = coverage node
    AstNode*	stmtsp()	const { return op4p(); }	// op4 = statements
};

//======================================================================
// PSL Expressions

struct AstPslBool : public AstNode {
    // Separates PSL Sere/sequences from the normal expression boolean layer below.
    // Note this excludes next() and similar functions; they are time domain, so not under AstPslBool.
    // Parents: Sequences, etc.
    // Children: math
    AstPslBool(FileLine* fileline, AstNode* exprp)
	: AstNode(fileline) {
	addOp1p(exprp);
    }
    ASTNODE_NODE_FUNCS(PslBool, PSLBOOL)
    AstNode*	exprp()	const { return op1p()->castNode(); }	// op1= expression
    virtual bool isGateOptimizable() const { return false; }	// Not relevant
    virtual bool isPredictOptimizable() const { return false; }	// Not relevant
    virtual int instrCount()	const { return 0; }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
};

//======================================================================
// Text based nodes

struct AstText : public AstNodeText {
private:
    bool	m_tracking;	// When emit, it's ok to parse the string to do indentation
public:
    AstText(FileLine* fl, const string& textp, bool tracking=false)
	: AstNodeText(fl, textp), m_tracking(tracking) {}
    ASTNODE_NODE_FUNCS(Text, TEXT)
    void tracking(bool flag) { m_tracking = flag; }
    bool tracking() const { return m_tracking; }
};

struct AstScCtor : public AstNodeText {
    AstScCtor(FileLine* fl, const string& textp)
	: AstNodeText(fl, textp) {}
    ASTNODE_NODE_FUNCS(ScCtor, SCCTOR)
    virtual bool isPure() const { return false; }	// SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const { return true; }
};

struct AstScDtor : public AstNodeText {
    AstScDtor(FileLine* fl, const string& textp)
	: AstNodeText(fl, textp) {}
    ASTNODE_NODE_FUNCS(ScDtor, SCDTOR)
    virtual bool isPure() const { return false; }	// SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const { return true; }
};

struct AstScHdr : public AstNodeText {
    AstScHdr(FileLine* fl, const string& textp)
	: AstNodeText(fl, textp) {}
    ASTNODE_NODE_FUNCS(ScHdr, SCHDR)
    virtual bool isPure() const { return false; }	// SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const { return true; }
};

struct AstScImp : public AstNodeText {
    AstScImp(FileLine* fl, const string& textp)
	: AstNodeText(fl, textp) {}
    ASTNODE_NODE_FUNCS(ScImp, SCIMP)
    virtual bool isPure() const { return false; }	// SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const { return true; }
};

struct AstScImpHdr : public AstNodeText {
    AstScImpHdr(FileLine* fl, const string& textp)
	: AstNodeText(fl, textp) {}
    ASTNODE_NODE_FUNCS(ScImpHdr, SCIMPHDR)
    virtual bool isPure() const { return false; }	// SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const { return true; }
};

struct AstScInt : public AstNodeText {
    AstScInt(FileLine* fl, const string& textp)
	: AstNodeText(fl, textp) {}
    ASTNODE_NODE_FUNCS(ScInt, SCINT)
    virtual bool isPure() const { return false; }	// SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const { return true; }
};

struct AstUCStmt : public AstNodeStmt {
    // User $c statement
    AstUCStmt(FileLine* fl, AstNode* exprsp)
	: AstNodeStmt(fl) {
	addNOp1p(exprsp);
    }
    ASTNODE_NODE_FUNCS(UCStmt, UCSTMT)
    AstNode*	bodysp()	const { return op1p()->castNode(); }	// op1= expressions to print
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool isPure() const { return false; }
    virtual bool isOutputter() const { return true; }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
};

//======================================================================
// Emit C nodes

struct AstCFile : public AstNode {
    // C++ output file
    // Parents:  NETLIST
    // Children: nothing yet
private:
    string	m_name;		///< Filename
    bool	m_slow:1;	///< Compile w/o optimization
    bool	m_source:1;	///< Source file (vs header file)
    bool	m_support:1;	///< Support file (non systemc)
public:
    AstCFile(FileLine* fl, const string& name)
	: AstNode(fl) {
	m_name = name;
	m_slow = false;
	m_source = false;
	m_support = false;
    }
    ASTNODE_NODE_FUNCS(CFile, CFILE)
    virtual string name()	const { return m_name; }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
    virtual void dump(ostream& str=cout);
    bool	slow() const { return m_slow; }
    void	slow(bool flag) { m_slow = flag; }
    bool	source() const { return m_source; }
    void	source(bool flag) { m_source = flag; }
    bool	support() const { return m_support; }
    void	support(bool flag) { m_support = flag; }
};

struct AstCFunc : public AstNode {
    // C++ function
    // Parents:  MODULE/SCOPE
    // Children: VAR/statements
private:
    AstCFuncType m_funcType;
    AstScope*	m_scopep;
    string	m_name;
    string	m_cname;		// C name, for dpiExports
    string	m_rtnType;		// void, bool, or other return type
    string	m_argTypes;
    bool	m_dontCombine:1;	// V3Combine shouldn't compare this func tree, it's special
    bool	m_skipDecl:1;		// Don't declare it
    bool	m_declPrivate:1;	// Declare it private
    bool	m_formCallTree:1;	// Make a global function to call entire tree of functions
    bool	m_slow:1;		// Slow routine, called once or just at init time
    bool	m_funcPublic:1;		// From user public task/function
    bool	m_isStatic:1;		// Function is declared static (no this)
    bool	m_symProlog:1;		// Setup symbol table for later instructions
    bool	m_entryPoint:1;		// User may call into this top level function
    bool	m_pure:1;		// Pure function
    bool	m_dpiExport:1;		// From dpi export
    bool	m_dpiExportWrapper:1;	// From dpi export; static function with dispatch table
    bool	m_dpiImport:1;		// From dpi import
public:
    AstCFunc(FileLine* fl, const string& name, AstScope* scopep, const string& rtnType="")
	: AstNode(fl) {
	m_funcType = AstCFuncType::FT_NORMAL;
	m_scopep = scopep;
	m_name = name;
	m_rtnType = rtnType;
	m_dontCombine = false;
	m_skipDecl = false;
	m_declPrivate = false;
	m_formCallTree = false;
	m_slow = false;
	m_funcPublic = false;
	m_isStatic = true;	// Note defaults to static, later we see where thisp is needed
	m_symProlog = false;
	m_entryPoint = false;
	m_pure = false;
	m_dpiExport = false;
	m_dpiExportWrapper = false;
	m_dpiImport = false;
    }
    ASTNODE_NODE_FUNCS(CFunc, CFUNC)
    virtual string name()	const { return m_name; }
    virtual bool broken() const { return ( (m_scopep && !m_scopep->brokeExists())); }
    virtual bool maybePointedTo() const { return true; }
    virtual void dump(ostream& str=cout);
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return ((funcType()==samep->castCFunc()->funcType())
						      && (rtnTypeVoid()==samep->castCFunc()->rtnTypeVoid())
						      && (argTypes()==samep->castCFunc()->argTypes())
						      && (!(dpiImport() || dpiExport())
							  || name()==samep->castCFunc()->name())); }
    //
    virtual void name(const string& name) { m_name = name; }
    virtual int instrCount()	const { return dpiImport() ? instrCountDpi() : 0; }
    void	cname(const string& name) { m_cname = name; }
    string	cname() const { return m_cname; }
    AstScope*	scopep() const { return m_scopep; }
    void	scopep(AstScope* nodep) { m_scopep = nodep; }
    string	rtnTypeVoid() const { return ((m_rtnType=="") ? "void" : m_rtnType); }
    bool	dontCombine() const { return m_dontCombine || funcType()!=AstCFuncType::FT_NORMAL; }
    void	dontCombine(bool flag) { m_dontCombine = flag; }
    bool	skipDecl() const { return m_skipDecl; }
    void	skipDecl(bool flag) { m_skipDecl = flag; }
    bool	declPrivate() const { return m_declPrivate; }
    void	declPrivate(bool flag) { m_declPrivate = flag; }
    bool	formCallTree() const { return m_formCallTree; }
    void	formCallTree(bool flag) { m_formCallTree = flag; }
    bool	slow() const { return m_slow; }
    void	slow(bool flag) { m_slow = flag; }
    bool	funcPublic() const { return m_funcPublic; }
    void	funcPublic(bool flag) { m_funcPublic = flag; }
    void	argTypes(const string& str) { m_argTypes = str; }
    string	argTypes() const { return m_argTypes; }
    void	funcType(AstCFuncType flag) { m_funcType = flag; }
    AstCFuncType funcType() const { return m_funcType; }
    bool	isStatic() const { return m_isStatic; }
    void	isStatic(bool flag) { m_isStatic = flag; }
    bool	symProlog() const { return m_symProlog; }
    void	symProlog(bool flag) { m_symProlog = flag; }
    bool	entryPoint() const { return m_entryPoint; }
    void	entryPoint(bool flag) { m_entryPoint = flag; }
    bool	pure() const { return m_pure; }
    void	pure(bool flag) { m_pure = flag; }
    bool	dpiExport() const { return m_dpiExport; }
    void	dpiExport(bool flag) { m_dpiExport = flag; }
    bool	dpiExportWrapper() const { return m_dpiExportWrapper; }
    void	dpiExportWrapper(bool flag) { m_dpiExportWrapper = flag; }
    bool	dpiImport() const { return m_dpiImport; }
    void	dpiImport(bool flag) { m_dpiImport = flag; }
    //
    // If adding node accessors, see below emptyBody
    AstNode*	argsp() 	const { return op1p()->castNode(); }
    void addArgsp(AstNode* nodep) { addOp1p(nodep); }
    AstNode*	initsp() 	const { return op2p()->castNode(); }
    void addInitsp(AstNode* nodep) { addOp2p(nodep); }
    AstNode*	stmtsp() 	const { return op3p()->castNode(); }
    void addStmtsp(AstNode* nodep) { addOp3p(nodep); }
    AstNode*	finalsp() 	const { return op4p()->castNode(); }
    void addFinalsp(AstNode* nodep) { addOp4p(nodep); }
    // Special methods
    bool	emptyBody() const { return argsp()==NULL && initsp()==NULL && stmtsp()==NULL && finalsp()==NULL; }
};

struct AstCCall : public AstNodeStmt {
    // C++ function call
    // Parents:  Anything above a statement
    // Children: Args to the function
private:
    AstCFunc*	m_funcp;
    string	m_hiername;
    string	m_argTypes;
public:
    AstCCall(FileLine* fl, AstCFunc* funcp, AstNode* argsp=NULL)
	: AstNodeStmt(fl) {
	m_funcp = funcp;
	addNOp1p(argsp);
    }
    AstCCall(AstCCall* oldp, AstCFunc* funcp)	// Replacement form for V3Combine
	// Note this removes old attachments from the oldp
	: AstNodeStmt(oldp->fileline()) {
	m_funcp = funcp;
	m_hiername = oldp->hiername();
	m_argTypes = oldp->argTypes();
	if (oldp->argsp()) addNOp1p(oldp->argsp()->unlinkFrBackWithNext());
    }
    ASTNODE_NODE_FUNCS(CCall, CCALL)
    virtual void dump(ostream& str=cout);
    virtual void cloneRelink() { if (m_funcp && m_funcp->clonep()) {
	m_funcp = m_funcp->clonep()->castCFunc();
    }}
    virtual bool broken() const { return (m_funcp && !m_funcp->brokeExists()); }
    virtual int instrCount()	const { return instrCountCall(); }
    virtual V3Hash sameHash() const { return V3Hash(funcp()); }
    virtual bool same(AstNode* samep) const {
	return (funcp()==samep->castCCall()->funcp()
		&& argTypes()==samep->castCCall()->argTypes()); }
    AstNode*	exprsp()	const { return op1p()->castNode(); }	// op1= expressions to print
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool isPure() const { return funcp()->pure(); }
    virtual bool isOutputter() const { return !(funcp()->pure()); }
    AstCFunc*	funcp() const { return m_funcp; }
    string hiername() const { return m_hiername; }
    void hiername(const string& hn) { m_hiername = hn; }
    void	argTypes(const string& str) { m_argTypes = str; }
    string	argTypes() const { return m_argTypes; }
    //
    AstNode*	argsp() 	const { return op1p()->castNode(); }
    void addArgsp(AstNode* nodep) { addOp1p(nodep); }
};

struct AstCReturn : public AstNodeStmt {
    // C++ return from a function
    // Parents:  CFUNC/statement
    // Children: Math
    AstCReturn(FileLine* fl, AstNode* lhsp)
	: AstNodeStmt(fl) {
	setOp1p(lhsp);
    }
    ASTNODE_NODE_FUNCS(CReturn, CRETURN)
    virtual int instrCount()	const { return widthInstrs(); }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode*) const { return true; }
    //
    AstNode*	lhsp() const { return op1p(); }
};

struct AstCMath : public AstNodeMath {
private:
    bool	m_cleanOut;
public:
    // Emit C textual math function (like AstUCFunc)
    AstCMath(FileLine* fl, AstNode* exprsp)
	: AstNodeMath(fl), m_cleanOut(true) {
	addOp1p(exprsp);
	widthSignedFrom(exprsp);
    }
    AstCMath(FileLine* fl, const string& textStmt, int setwidth, bool cleanOut=true)
	: AstNodeMath(fl), m_cleanOut(cleanOut) {
	addNOp1p(new AstText(fl, textStmt, true));
	if (setwidth) { width(setwidth,setwidth); }
    }
    ASTNODE_NODE_FUNCS(CMath, CMATH)
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool cleanOut() { return m_cleanOut; }
    virtual string emitVerilog() { V3ERROR_NA; return ""; }  // Implemented specially
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
    void addBodysp(AstNode* nodep) { addNOp1p(nodep); }
    AstNode*	bodysp()	const { return op1p()->castNode(); }	// op1= expressions to print
};


struct AstCStmt : public AstNodeStmt {
    // Emit C statement
    AstCStmt(FileLine* fl, AstNode* exprsp)
	: AstNodeStmt(fl) {
	addNOp1p(exprsp);
    }
    AstCStmt(FileLine* fl, const string& textStmt)
	: AstNodeStmt(fl) {
	addNOp1p(new AstText(fl, textStmt, true));
    }
    ASTNODE_NODE_FUNCS(CStmt, CSTMT)
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
    void addBodysp(AstNode* nodep) { addNOp1p(nodep); }
    AstNode*	bodysp()	const { return op1p()->castNode(); }	// op1= expressions to print
};

//######################################################################
// Top

struct AstNetlist : public AstNode {
    // All modules are under this single top node.
    // Parents:   none
    // Children:  MODULEs & CFILEs
    AstNetlist() : AstNode(new FileLine("AstRoot",0)) {}
    ASTNODE_NODE_FUNCS(Netlist, NETLIST)
    AstNodeModule*	modulesp() 	const { return op1p()->castNodeModule();}	// op1 = List of modules
    AstNodeModule*  topModulep() const { return op1p()->castNodeModule(); }	// * = Top module in hierarchy (first one added, for now)
    void addModulep(AstNodeModule* modulep) { addOp1p(modulep); }
    AstCFile*	filesp() 	const { return op2p()->castCFile();}	// op2 = List of files
    void addFilesp(AstCFile* filep) { addOp2p(filep); }
};

//######################################################################

#endif // Guard
