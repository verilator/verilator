// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Ast node structure
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2015 by Wilson Snyder.  This program is free software; you can
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

class AstConst : public AstNodeMath {
    // A constant
private:
    V3Number	m_num;		// Constant value
public:
    AstConst(FileLine* fl, const V3Number& num)
	:AstNodeMath(fl)
	,m_num(num) {
	if (m_num.isDouble()) {
	    dtypeSetDouble();
	} else if (m_num.isString()) {
	    dtypeSetString();
	} else {
	    dtypeSetLogicSized(m_num.width(), m_num.sized()?0:m_num.widthMin(),
			       m_num.isSigned() ? AstNumeric::SIGNED
			       : AstNumeric::UNSIGNED);
	}
    }
    AstConst(FileLine* fl, uint32_t num)
	:AstNodeMath(fl)
	,m_num(V3Number(fl,32,num)) { dtypeSetLogicSized(m_num.width(),
							 m_num.sized()?0:m_num.widthMin(),
							 AstNumeric::UNSIGNED); }
    class Unsized32 {};		// for creator type-overload selection
    AstConst(FileLine* fl, Unsized32, uint32_t num)  // Unsized 32-bit integer of specified value
	:AstNodeMath(fl)
	,m_num(V3Number(fl,32,num)) { m_num.width(32,false); dtypeSetLogicSized(32,m_num.widthMin(),
										AstNumeric::UNSIGNED); }
    class Signed32 {};		// for creator type-overload selection
    AstConst(FileLine* fl, Signed32, int32_t num)  // Signed 32-bit integer of specified value
	:AstNodeMath(fl)
	,m_num(V3Number(fl,32,num)) { m_num.width(32,32); dtypeSetLogicSized(32,m_num.widthMin(),
									     AstNumeric::SIGNED); }
    class RealDouble {};		// for creator type-overload selection
    AstConst(FileLine* fl, RealDouble, double num)
	:AstNodeMath(fl)
	,m_num(V3Number(fl,64)) { m_num.setDouble(num); dtypeSetDouble(); }
    class String {};		// for creator type-overload selection
    AstConst(FileLine* fl, String, const string& num)
	:AstNodeMath(fl)
	,m_num(V3Number(V3Number::String(), fl, num)) { dtypeSetString(); }
    class LogicFalse {};
    AstConst(FileLine* fl, LogicFalse) // Shorthand const 0, know the dtype should be a logic of size 1
	:AstNodeMath(fl)
	,m_num(V3Number(fl,1,0)) { dtypeSetLogicBool(); }
    class LogicTrue {};
    AstConst(FileLine* fl, LogicTrue) // Shorthand const 1, know the dtype should be a logic of size 1
	:AstNodeMath(fl)
	,m_num(V3Number(fl,1,1)) { dtypeSetLogicBool(); }

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
    bool isEqAllOnesV() const { return num().isEqAllOnes(widthMinV()); }
};

class AstRange : public AstNode {
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
    AstRange(FileLine* fl, VNumRange range)
	:AstNode(fl) {
	m_littleEndian = range.littleEndian();
	setOp2p(new AstConst(fl,range.hi())); setOp3p(new AstConst(fl,range.lo()));
    }
    ASTNODE_NODE_FUNCS(Range, RANGE)
    AstNode* msbp() const { return op2p()->castNode(); }	// op2 = Msb expression
    AstNode* lsbp() const { return op3p()->castNode(); }	// op3 = Lsb expression
    AstNode* leftp() const { return littleEndian()?lsbp():msbp(); }  // How to show a declaration
    AstNode* rightp() const { return littleEndian()?msbp():lsbp(); }
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

class AstGatePin : public AstNodeMath {
    // Possibly expand a gate primitive input pin value to match the range of the gate primitive
public:
    AstGatePin(FileLine* fl, AstNode* lhsp, AstRange* rangep) : AstNodeMath(fl) {
	setOp1p(lhsp); setOp2p(rangep);
    }
    ASTNODE_NODE_FUNCS(GatePin, GATEPIN)
    virtual string emitVerilog() { return "%l"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool cleanOut() { return true; }
    AstNode* exprp() const { return op1p(); }			// op1 = Pin expression
    AstRange* rangep() const { return op2p()->castRange(); }	// op2 = Range of pin
};

//######################################################################
//==== Data Types

class AstTypedef : public AstNode {
private:
    string	m_name;
    bool	m_attrPublic;
public:
    AstTypedef(FileLine* fl, const string& name, AstNode* attrsp, VFlagChildDType, AstNodeDType* dtp)
	: AstNode(fl), m_name(name) {
	childDTypep(dtp);  // Only for parser
	addAttrsp(attrsp);
	dtypep(NULL);  // V3Width will resolve
	m_attrPublic = false;
    }
    ASTNODE_NODE_FUNCS(Typedef, TYPEDEF)
    virtual void dump(ostream& str);
    AstNodeDType* getChildDTypep() const { return childDTypep(); }
    AstNodeDType* childDTypep() const { return op1p()->castNodeDType(); } // op1 = Type assigning to
    void	childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    AstNodeDType* subDTypep() const { return dtypep() ? dtypep() : childDTypep(); }
    void	addAttrsp(AstNode* nodep) { addNOp4p(nodep); }
    AstNode*	attrsp() const { return op4p()->castNode(); }	// op4 = Attributes during early parse
    // METHODS
    virtual string name() const { return m_name; }
    virtual bool maybePointedTo() const { return true; }
    virtual bool hasDType() const { return true; }
    void name(const string& flag) { m_name = flag; }
    bool attrPublic() const { return m_attrPublic; }
    void attrPublic(bool flag) { m_attrPublic = flag; }
};

class AstTypedefFwd : public AstNode {
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

class AstDefImplicitDType : public AstNodeDType {
    // For parsing enum/struct/unions that are declared with a variable rather than typedef
    // This allows "var enum {...} a,b" to share the enum definition for both variables
    // After link, these become typedefs
private:
    string	m_name;
    void*	m_containerp;	// In what scope is the name unique, so we can know what are duplicate definitions (arbitrary value)
    int		m_uniqueNum;
public:
    AstDefImplicitDType(FileLine* fl, const string& name, void* containerp,
			VFlagChildDType, AstNodeDType* dtp)
	: AstNodeDType(fl), m_name(name), m_containerp(containerp) {
	childDTypep(dtp);  // Only for parser
	dtypep(NULL);  // V3Width will resolve
	m_uniqueNum = uniqueNumInc();
    }
    ASTNODE_NODE_FUNCS(DefImplicitDType, DEFIMPLICITDTYPE)
    virtual bool same(AstNode* samep) const { return m_uniqueNum==samep->castDefImplicitDType()->m_uniqueNum; }
    virtual V3Hash sameHash() const { return V3Hash(m_uniqueNum); }
    AstNodeDType* getChildDTypep() const { return childDTypep(); }
    AstNodeDType* childDTypep() const { return op1p()->castNodeDType(); } // op1 = Range of variable
    void	childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    AstNodeDType* subDTypep() const { return dtypep() ? dtypep() : childDTypep(); }
    void*	containerp() const { return m_containerp; }
    // METHODS
    AstNodeDType* dtypeSkipRefp() const { return dtypep()->skipRefp(); }	// op1 = Range of variable
    virtual AstBasicDType* basicp() const { return subDTypep()->basicp(); }  // (Slow) recurse down to find basic data type
    virtual AstNodeDType* skipRefp() const { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToConstp() const { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToEnump() const { return (AstNodeDType*)this; }
    virtual int widthAlignBytes() const { return dtypep()->widthAlignBytes(); }
    virtual int widthTotalBytes() const { return dtypep()->widthTotalBytes(); }
    virtual string name() const { return m_name; }
    void name(const string& flag) { m_name = flag; }
};

class AstPackArrayDType : public AstNodeArrayDType {
    // Array data type, ie "some_dtype var_name [2:0]"
    // Children: DTYPE (moved to refDTypep() in V3Width)
    // Children: RANGE (array bounds)
public:
    AstPackArrayDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp, AstRange* rangep)
	: AstNodeArrayDType(fl) {
	childDTypep(dtp);  // Only for parser
	refDTypep(NULL);
	setOp2p(rangep);
	dtypep(NULL);  // V3Width will resolve
	int width = subDTypep()->width() * rangep->elementsConst();
	widthForce(width,width);
    }
    AstPackArrayDType(FileLine* fl, AstNodeDType* dtp, AstRange* rangep)
	: AstNodeArrayDType(fl) {
	refDTypep(dtp);
	setOp2p(rangep);
	dtypep(this);
	int width = subDTypep()->width() * rangep->elementsConst();
	widthForce(width,width);
    }
    ASTNODE_NODE_FUNCS(PackArrayDType, PACKARRAYDTYPE)
};

class AstUnpackArrayDType : public AstNodeArrayDType {
    // Array data type, ie "some_dtype var_name [2:0]"
    // Children: DTYPE (moved to refDTypep() in V3Width)
    // Children: RANGE (array bounds)
public:
    AstUnpackArrayDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp, AstRange* rangep)
	: AstNodeArrayDType(fl) {
	childDTypep(dtp);  // Only for parser
	refDTypep(NULL);
	setOp2p(rangep);
	dtypep(NULL);  // V3Width will resolve
	// For backward compatibility AstNodeArrayDType and others inherit width and signing from the subDType/base type
	widthFromSub(subDTypep());
    }
    AstUnpackArrayDType(FileLine* fl, AstNodeDType* dtp, AstRange* rangep)
	: AstNodeArrayDType(fl) {
	refDTypep(dtp);
	setOp2p(rangep);
	dtypep(this);
	// For backward compatibility AstNodeArrayDType and others inherit width and signing from the subDType/base type
	widthFromSub(subDTypep());
    }
    ASTNODE_NODE_FUNCS(UnpackArrayDType, UNPACKARRAYDTYPE)
};

class AstBasicDType : public AstNodeDType {
    // Builtin atomic/vectored data type
    // Children: RANGE (converted to constant in V3Width)
private:
    struct Members {
	AstBasicDTypeKwd m_keyword;	// (also in VBasicTypeKey) What keyword created basic type
	VNumRange	m_nrange;	// (also in VBasicTypeKey) Numeric msb/lsb (if non-opaque keyword)
	bool operator== (const Members& rhs) const {
	    return rhs.m_keyword == m_keyword
		&& rhs.m_nrange == m_nrange; }
    } m;
    // See also in AstNodeDtype: m_width, m_widthMin, m_numeric(issigned)
public:
    AstBasicDType(FileLine* fl, AstBasicDTypeKwd kwd, VSignedState signst=signedst_NOSIGN)
	: AstNodeDType(fl) {
	init(kwd, AstNumeric(signst), 0, -1, NULL);
    }
    AstBasicDType(FileLine* fl, VFlagLogicPacked, int wantwidth)
	: AstNodeDType(fl) {
	init(AstBasicDTypeKwd::LOGIC, AstNumeric::NOSIGN, wantwidth, -1, NULL);
    }
    AstBasicDType(FileLine* fl, VFlagBitPacked, int wantwidth)
	: AstNodeDType(fl) {
	init(AstBasicDTypeKwd::BIT, AstNumeric::NOSIGN, wantwidth, -1, NULL);
    }
    AstBasicDType(FileLine* fl, AstBasicDTypeKwd kwd, AstNumeric numer, int wantwidth, int widthmin)
	: AstNodeDType(fl) {
	init(kwd, numer, wantwidth, widthmin, NULL);
    }
    AstBasicDType(FileLine* fl, AstBasicDTypeKwd kwd, AstNumeric numer, VNumRange range, int widthmin)
	: AstNodeDType(fl) {
	init(kwd, numer, range.elements(), widthmin, NULL);
	m.m_nrange = range; // as init() presumes lsb==0, but range.lsb() might not be
    }
    // See also addRange in verilog.y
private:
    void init(AstBasicDTypeKwd kwd, AstNumeric numer,
	      int wantwidth, int wantwidthmin, AstRange* rangep) {
	// wantwidth=0 means figure it out, but if a widthmin is >=0
	//    we allow width 0 so that {{0{x}},y} works properly
	// wantwidthmin=-1:  default, use wantwidth if it is non zero
	m.m_keyword = kwd;
	// Implicitness: // "parameter X" is implicit and sized from initial value, "parameter reg x" not
	if (keyword()==AstBasicDTypeKwd::LOGIC_IMPLICIT) {
	    if (rangep || wantwidth) m.m_keyword = AstBasicDTypeKwd::LOGIC;
	}
        if (numer == AstNumeric::NOSIGN) {
	    if (keyword().isSigned()) numer = AstNumeric::SIGNED;
	    else if (keyword().isUnsigned()) numer = AstNumeric::UNSIGNED;
	}
	numeric(numer);
	if (!rangep && (wantwidth || wantwidthmin>=0)) { // Constant width
	    if (wantwidth>1) m.m_nrange.init(wantwidth-1, 0, false);
	    int wmin = wantwidthmin>=0 ? wantwidthmin : wantwidth;
	    widthForce(wantwidth, wmin);
	} else if (!rangep) {  // Set based on keyword properties
	    // V3Width will pull from this width
	    if (keyword().width() > 1 && !isOpaque()) {
		m.m_nrange.init(keyword().width()-1, 0, false);
	    }
	    widthForce(keyword().width(), keyword().width());
	} else {
	    widthForce(rangep->elementsConst(), rangep->elementsConst());  // Maybe unknown if parameters underneath it
	}
	setNOp1p(rangep);
	dtypep(this);
    }
public:
    ASTNODE_NODE_FUNCS(BasicDType, BASICDTYPE)
    virtual void dump(ostream& str);
    virtual V3Hash sameHash() const { return V3Hash(V3Hash(m.m_keyword), V3Hash(m.m_nrange.hi())); }
    virtual bool same(AstNode* samep) const {  // width/widthMin/numeric compared elsewhere
	return samep->castBasicDType()->m == m; }
    virtual string name()	const { return m.m_keyword.ascii(); }
    virtual const char* broken() const { BROKEN_RTN(dtypep()!=this); return NULL; }
    AstRange*	rangep() 	const { return op1p()->castRange(); }	// op1 = Range of variable
    void	rangep(AstRange* nodep) { setNOp1p(nodep); }
    void setSignedState(VSignedState signst) {
	// Note NOSIGN does NOT change the state; this is required by the parser
	if (signst==signedst_UNSIGNED) numeric(VSignedState(signst));
	else if (signst==signedst_SIGNED) numeric(VSignedState(signst));
    }
    // METHODS
    virtual AstBasicDType* basicp() const { return (AstBasicDType*)this; }  // (Slow) recurse down to find basic data type
    virtual AstNodeDType* skipRefp() const { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToConstp() const { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToEnump() const { return (AstNodeDType*)this; }
    virtual int widthAlignBytes() const; // (Slow) recurses - Structure alignment 1,2,4 or 8 bytes (arrays affect this)
    virtual int widthTotalBytes() const; // (Slow) recurses - Width in bytes rounding up 1,2,4,8,12,...
    AstBasicDTypeKwd keyword() const { return m.m_keyword; }  // Avoid using - use isSomething accessors instead
    bool	isBitLogic() const { return keyword().isBitLogic(); }
    bool	isDouble() const { return keyword().isDouble(); }
    bool	isOpaque() const { return keyword().isOpaque(); }
    bool	isString() const { return keyword().isString(); }
    bool	isSloppy() const { return keyword().isSloppy(); }
    bool	isZeroInit() const { return keyword().isZeroInit(); }
    bool	isRanged() const { return rangep() || m.m_nrange.ranged(); }
    const VNumRange& nrange() const { return m.m_nrange; } // Generally the msb/lsb/etc funcs should be used instead
    int		msb() const { return (rangep() ? rangep()->msbConst() : m.m_nrange.hi()); }
    int		lsb() const { return (rangep() ? rangep()->lsbConst() : m.m_nrange.lo()); }
    int		left() const { return littleEndian()?lsb():msb(); }  // How to show a declaration
    int		right() const { return littleEndian()?msb():lsb(); }
    bool	littleEndian() const { return (rangep() ? rangep()->littleEndian() : m.m_nrange.littleEndian()); }
    bool	implicit() const { return keyword() == AstBasicDTypeKwd::LOGIC_IMPLICIT; }
    VNumRange declRange() const { return isRanged() ? VNumRange(msb(), lsb(), littleEndian()) : VNumRange(); }
    void	cvtRangeConst() {  // Convert to smaller represenation
	if (rangep() && rangep()->msbp()->castConst() && rangep()->lsbp()->castConst()) {
	    m.m_nrange.init(rangep()->msbConst(), rangep()->lsbConst(),
			    rangep()->littleEndian());
	    rangep()->unlinkFrBackWithNext()->deleteTree();
	    rangep(NULL);
	}
    }
};

class AstConstDType : public AstNodeDType {
    // const data type, ie "const some_dtype var_name [2:0]"
    // ConstDType are removed in V3LinkLValue and become AstVar::isConst.
    // When more generic types are supported AstConstDType will be propagated further.
private:
    AstNodeDType*	m_refDTypep;	// Inherit from this base data type
public:
    AstConstDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp)
	: AstNodeDType(fl) {
	childDTypep(dtp);  // Only for parser
	refDTypep(NULL);  // V3Width will resolve
	dtypep(NULL);  // V3Width will resolve
	widthFromSub(subDTypep());
    }
    ASTNODE_NODE_FUNCS(ConstDType, CONSTDTYPE)
    virtual const char* broken() const { BROKEN_RTN(!((m_refDTypep && !childDTypep() && m_refDTypep->brokeExists())
						     || (!m_refDTypep && childDTypep()))); return NULL; }
    virtual void cloneRelink() { if (m_refDTypep && m_refDTypep->clonep()) {
	m_refDTypep = m_refDTypep->clonep()->castNodeDType();
    }}
    virtual bool same(AstNode* samep) const {
	return (m_refDTypep==samep->castConstDType()->m_refDTypep); }
    virtual V3Hash sameHash() const { return V3Hash(m_refDTypep); }  // node's type() included elsewhere
    AstNodeDType* getChildDTypep() const { return childDTypep(); }
    AstNodeDType* childDTypep() const { return op1p()->castNodeDType(); } // op1 = Range of variable
    void childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    AstNodeDType* subDTypep() const { return m_refDTypep ? m_refDTypep : childDTypep(); } // op1 = Range of variable
    void refDTypep(AstNodeDType* nodep) { m_refDTypep = nodep; }
    virtual AstNodeDType* virtRefDTypep() const { return m_refDTypep; }
    virtual void virtRefDTypep(AstNodeDType* nodep) { refDTypep(nodep); }
    // METHODS
    virtual AstBasicDType* basicp() const { return subDTypep()->basicp(); }  // (Slow) recurse down to find basic data type
    virtual AstNodeDType* skipRefp() const { return subDTypep()->skipRefp(); }
    virtual AstNodeDType* skipRefToConstp() const { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToEnump() const { return subDTypep()->skipRefToEnump(); }
    virtual int widthAlignBytes() const { return subDTypep()->widthAlignBytes(); }
    virtual int widthTotalBytes() const { return subDTypep()->widthTotalBytes(); }
};

class AstIfaceRefDType : public AstNodeDType {
    // Reference to an interface, either for a port, or inside parent cell
private:
    string		m_cellName;	// "" = no cell, such as when connects to 'input' iface
    string		m_ifaceName;	// Interface name
    string		m_modportName;	// "" = no modport
    AstIface*		m_ifacep;	// Pointer to interface; note cellp() should override
    AstCell*		m_cellp;	// When exact parent cell known; not a guess
    AstModport*		m_modportp;	// NULL = unlinked or no modport
public:
    AstIfaceRefDType(FileLine* fl, const string& cellName, const string& ifaceName)
	: AstNodeDType(fl), m_cellName(cellName), m_ifaceName(ifaceName), m_modportName(""),
	  m_ifacep(NULL), m_cellp(NULL), m_modportp(NULL) { }
    AstIfaceRefDType(FileLine* fl, const string& cellName, const string& ifaceName, const string& modport)
	: AstNodeDType(fl), m_cellName(cellName), m_ifaceName(ifaceName), m_modportName(modport),
	  m_ifacep(NULL), m_cellp(NULL), m_modportp(NULL) { }
    ASTNODE_NODE_FUNCS(IfaceRefDType, IFACEREFDTYPE)
    // METHODS
    virtual const char* broken() const;
    virtual void dump(ostream& str=cout);
    virtual void dumpSmall(ostream& str);
    virtual void cloneRelink();
    virtual AstBasicDType* basicp() const { return NULL; }
    virtual AstNodeDType* skipRefp() const { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToConstp() const { return (AstNodeDType*)this; }
    virtual AstNodeDType* skipRefToEnump() const { return (AstNodeDType*)this; }
    virtual int widthAlignBytes() const { return 1; }
    virtual int widthTotalBytes() const { return 1; }
    string cellName() const { return m_cellName; }
    void cellName(const string& name) { m_cellName=name; }
    string ifaceName() const { return m_ifaceName; }
    void ifaceName(const string& name) { m_ifaceName=name; }
    string modportName() const { return m_modportName; }
    void modportName(const string& name) { m_modportName=name; }
    AstIface* ifaceViaCellp() const;  // Use cellp or ifacep
    AstIface* ifacep() const { return m_ifacep; }
    void ifacep(AstIface* nodep) { m_ifacep=nodep; }
    AstCell* cellp() const { return m_cellp; }
    void cellp(AstCell* nodep) { m_cellp=nodep; }
    AstModport* modportp() const { return m_modportp; }
    void modportp(AstModport* modportp) { m_modportp=modportp; }
    bool isModport() { return !m_modportName.empty(); }
};

class AstRefDType : public AstNodeDType {
private:
    AstNodeDType* m_refDTypep;	// data type pointed to, BELOW the AstTypedef
    string	m_name;		// Name of an AstTypedef
    AstPackage*	m_packagep;	// Package hierarchy
public:
    AstRefDType(FileLine* fl, const string& name)
	: AstNodeDType(fl), m_refDTypep(NULL), m_name(name), m_packagep(NULL) {}
    AstRefDType(FileLine* fl, AstNodeDType* defp)
	: AstNodeDType(fl), m_refDTypep(defp), m_packagep(NULL) {
	dtypeFrom(defp->dtypep());
	widthFromSub(subDTypep());
    }
    ASTNODE_NODE_FUNCS(RefDType, REFDTYPE)
    // METHODS
    virtual const char* broken() const { BROKEN_RTN(m_refDTypep && !m_refDTypep->brokeExists()); return NULL; }
    virtual void cloneRelink() { if (m_refDTypep && m_refDTypep->clonep()) {
	m_refDTypep = m_refDTypep->clonep()->castNodeDType();
    }}
    virtual bool same(AstNode* samep) const {
	return (m_refDTypep==samep->castRefDType()->m_refDTypep
		&& m_name==samep->castRefDType()->m_name
		&& m_packagep==samep->castRefDType()->m_packagep); }
    virtual V3Hash sameHash() const { return V3Hash(V3Hash(m_refDTypep),V3Hash(m_packagep)); }
    virtual void dump(ostream& str=cout);
    virtual string name() const { return m_name; }
    virtual AstBasicDType* basicp() const { return subDTypep() ? subDTypep()->basicp() : NULL; }
    virtual AstNodeDType* skipRefp() const {
	// Skip past both the Ref and the Typedef
	if (defp()) return defp()->skipRefp();
	else { v3fatalSrc("Typedef not linked"); return NULL; }
    }
    virtual AstNodeDType* skipRefToConstp() const {
	if (defp()) return defp()->skipRefToConstp();
	else { v3fatalSrc("Typedef not linked"); return NULL; }
    }
    virtual AstNodeDType* skipRefToEnump() const {
	if (defp()) return defp()->skipRefToEnump();
	else { v3fatalSrc("Typedef not linked"); return NULL; }
    }
    virtual int widthAlignBytes() const { return dtypeSkipRefp()->widthAlignBytes(); }
    virtual int widthTotalBytes() const { return dtypeSkipRefp()->widthTotalBytes(); }
    void name(const string& flag) { m_name = flag; }
    AstNodeDType* dtypeSkipRefp() const { return defp()->skipRefp(); }	// op1 = Range of variable
    AstNodeDType* defp() const { return m_refDTypep; } // Code backward compatibility name for refDTypep
    AstNodeDType* refDTypep() const { return m_refDTypep; }
    void refDTypep(AstNodeDType* nodep) { m_refDTypep=nodep; }
    virtual AstNodeDType* virtRefDTypep() const { return refDTypep(); }
    virtual void virtRefDTypep(AstNodeDType* nodep) { refDTypep(nodep); }
    AstNodeDType* subDTypep() const { return m_refDTypep; }
    AstPackage* packagep() const { return m_packagep; }
    void packagep(AstPackage* nodep) { m_packagep=nodep; }
};

class AstStructDType : public AstNodeClassDType {
public:
    AstStructDType(FileLine* fl, AstNumeric numericUnpack)
	: AstNodeClassDType(fl,numericUnpack) {}
    ASTNODE_NODE_FUNCS(StructDType, STRUCTDTYPE)
    virtual string verilogKwd() const { return "struct"; };
};

class AstUnionDType : public AstNodeClassDType {
public:
    //UNSUP: bool isTagged;
    AstUnionDType(FileLine* fl, AstNumeric numericUnpack)
	: AstNodeClassDType(fl,numericUnpack) {}
    ASTNODE_NODE_FUNCS(UnionDType, UNIONDTYPE)
    virtual string verilogKwd() const { return "union"; };
};

class AstMemberDType : public AstNodeDType {
    // A member of a struct/union
    // PARENT: AstClassDType
private:
    AstNodeDType*	m_refDTypep;	// Elements of this type (after widthing)
    string	m_name;		// Name of variable
    int		m_lsb;		// Within this level's packed struct, the LSB of the first bit of the member
    //UNSUP: int m_randType;	// Randomization type (IEEE)
public:
    AstMemberDType(FileLine* fl, const string& name, VFlagChildDType, AstNodeDType* dtp)
	: AstNodeDType(fl)
	, m_name(name), m_lsb(-1) {
	childDTypep(dtp);  // Only for parser
	dtypep(NULL);  // V3Width will resolve
	refDTypep(NULL);
    }
    AstMemberDType(FileLine* fl, const string& name, AstNodeDType* dtp)
	: AstNodeDType(fl)
	, m_name(name), m_lsb(-1) {
	UASSERT(dtp,"AstMember created with no dtype");
	refDTypep(dtp);
	dtypep(this);
	widthFromSub(subDTypep());
    }
    ASTNODE_NODE_FUNCS(MemberDType, MEMBERDTYPE)
    virtual string name()	const { return m_name; }		// * = Var name
    virtual bool hasDType() const { return true; }
    virtual bool maybePointedTo() const { return true; }
    AstNodeDType* getChildDTypep() const { return childDTypep(); }
    AstNodeDType* childDTypep() const { return op1p()->castNodeDType(); }	// op1 = Range of variable
    void	childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    AstNodeDType* subDTypep() const { return m_refDTypep ? m_refDTypep : childDTypep(); }
    void refDTypep(AstNodeDType* nodep) { m_refDTypep = nodep; }
    virtual AstNodeDType* virtRefDTypep() const { return m_refDTypep; }
    virtual void virtRefDTypep(AstNodeDType* nodep) { refDTypep(nodep); }
    //
    virtual AstBasicDType* basicp() const { return subDTypep()->basicp(); }  // (Slow) recurse down to find basic data type (Note don't need virtual - AstVar isn't a NodeDType)
    AstNodeDType* dtypeSkipRefp() const { return subDTypep()->skipRefp(); }	// op1 = Range of variable (Note don't need virtual - AstVar isn't a NodeDType)
    virtual AstNodeDType* skipRefp() const { return subDTypep()->skipRefp(); }
    virtual AstNodeDType* skipRefToConstp() const { return subDTypep()->skipRefToConstp(); }
    virtual AstNodeDType* skipRefToEnump() const { return subDTypep()->skipRefToEnump(); }
    virtual int widthAlignBytes() const { return subDTypep()->widthAlignBytes(); } // (Slow) recurses - Structure alignment 1,2,4 or 8 bytes (arrays affect this)
    virtual int widthTotalBytes() const { return subDTypep()->widthTotalBytes(); } // (Slow) recurses - Width in bytes rounding up 1,2,4,8,12,...
    // METHODS
    virtual void name(const string& name) { m_name = name; }
    int lsb() const { return m_lsb; }
    void lsb(int lsb) { m_lsb=lsb; }
};

class AstEnumItem : public AstNode {
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
    virtual bool hasDType() const { return true; }
    void name(const string& flag) { m_name = flag; }
    AstRange* rangep() const { return op1p()->castRange(); } // op1 = Range for name appending
    void rangep(AstNode* nodep) { addOp1p(nodep); }
    AstNode* valuep() const { return op2p(); } // op2 = Value
    void valuep(AstNode* nodep) { addOp2p(nodep); }
};

class AstEnumItemRef : public AstNodeMath {
private:
    AstEnumItem* m_itemp;	// [AfterLink] Pointer to item
    AstPackage*	m_packagep;	// Package hierarchy
public:
    AstEnumItemRef(FileLine* fl, AstEnumItem* itemp, AstPackage* packagep)
	: AstNodeMath(fl), m_itemp(itemp), m_packagep(packagep) {
	dtypeFrom(m_itemp);
    }
    ASTNODE_NODE_FUNCS(EnumItemRef, ENUMITEMREF)
    virtual void dump(ostream& str);
    virtual string name() const { return itemp()->name(); }
    virtual const char* broken() const { BROKEN_RTN(!itemp()); return NULL; }
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

class AstEnumDType : public AstNodeDType {
    // Parents: TYPEDEF/MODULE
    // Children: ENUMVALUEs
private:
    AstNodeDType*	m_refDTypep;	// Elements are of this type after V3Width
    int		m_uniqueNum;
public:
    AstEnumDType(FileLine* fl, VFlagChildDType, AstNodeDType* dtp, AstNode* itemsp)
	: AstNodeDType(fl) {
	childDTypep(dtp);  // Only for parser
	refDTypep(NULL);
	addNOp2p(itemsp);
	dtypep(NULL);  // V3Width will resolve
	widthFromSub(subDTypep());
	m_uniqueNum = uniqueNumInc();
    }
    ASTNODE_NODE_FUNCS(EnumDType, ENUMDTYPE)
    virtual const char* broken() const { BROKEN_RTN(!((m_refDTypep && !childDTypep() && m_refDTypep->brokeExists())
						     || (!m_refDTypep && childDTypep()))); return NULL; }
    virtual void cloneRelink() { if (m_refDTypep && m_refDTypep->clonep()) {
	m_refDTypep = m_refDTypep->clonep()->castNodeDType();
    }}
    virtual bool same(AstNode* samep) const { return m_uniqueNum==samep->castEnumDType()->m_uniqueNum; }
    virtual V3Hash sameHash() const { return V3Hash(m_uniqueNum); }
    AstNodeDType* getChildDTypep() const { return childDTypep(); }
    AstNodeDType* childDTypep() const { return op1p()->castNodeDType(); } // op1 = Data type
    void childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    AstNodeDType* subDTypep() const { return m_refDTypep ? m_refDTypep : childDTypep(); } // op1 = Range of variable
    void refDTypep(AstNodeDType* nodep) { m_refDTypep = nodep; }
    virtual AstNodeDType* virtRefDTypep() const { return m_refDTypep; }
    virtual void virtRefDTypep(AstNodeDType* nodep) { refDTypep(nodep); }
    AstEnumItem* itemsp() const { return op2p()->castEnumItem(); } // op2 = AstEnumItem's
    void addValuesp(AstNode* nodep) { addOp2p(nodep); }
    // METHODS
    virtual AstBasicDType* basicp() const { return subDTypep()->basicp(); }  // (Slow) recurse down to find basic data type
    virtual AstNodeDType* skipRefp() const { return subDTypep()->skipRefp(); }
    virtual AstNodeDType* skipRefToConstp() const { return subDTypep()->skipRefToConstp(); }
    virtual AstNodeDType* skipRefToEnump() const { return (AstNodeDType*)this; }
    virtual int widthAlignBytes() const { return subDTypep()->widthAlignBytes(); }
    virtual int widthTotalBytes() const { return subDTypep()->widthTotalBytes(); }
};

//######################################################################

class AstArraySel : public AstNodeSel {
    // Parents: math|stmt
    // Children: varref|arraysel, math
private:
    unsigned m_start;
    unsigned m_length;
    void init(AstNode* fromp) {
	if (fromp && fromp->dtypep()->skipRefp()->castNodeArrayDType()) {
	    // Strip off array to find what array references
	    dtypeFrom(fromp->dtypep()->skipRefp()->castNodeArrayDType()->subDTypep());
	}
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
    static AstNode* baseFromp(AstNode* nodep);	///< What is the base variable (or const) this dereferences?
    virtual void dump(ostream& str);
};

class AstWordSel : public AstNodeSel {
    // Select a single word from a multi-word wide value
public:
    AstWordSel(FileLine* fl, AstNode* fromp, AstNode* bitp)
	:AstNodeSel(fl, fromp, bitp) {
	dtypeSetUInt32(); // Always used on IData arrays so returns word entities
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

class AstSelExtract : public AstNodePreSel {
    // Range extraction, gets replaced with AstSel
public:
    AstSelExtract(FileLine* fl, AstNode* fromp, AstNode* msbp, AstNode* lsbp)
	: AstNodePreSel(fl, fromp, msbp, lsbp) {}
    ASTNODE_NODE_FUNCS(SelExtract, SELEXTRACT)
    AstNode*	msbp() const { return rhsp(); }
    AstNode*	lsbp() const { return thsp(); }
};

class AstSelBit : public AstNodePreSel {
    // Single bit range extraction, perhaps with non-constant selection or array selection
    // Gets replaced during link with AstArraySel or AstSel
public:
    AstSelBit(FileLine* fl, AstNode* fromp, AstNode* bitp)
	:AstNodePreSel(fl, fromp, bitp, NULL) {
	if (v3Global.assertDTypesResolved()) { v3fatalSrc("not coded to create after dtypes resolved"); }
    }
    ASTNODE_NODE_FUNCS(SelBit, SELBIT)
    AstNode*	bitp() const { return rhsp(); }
};

class AstSelPlus : public AstNodePreSel {
    // +: range extraction, perhaps with non-constant selection
    // Gets replaced during link with AstSel
public:
    AstSelPlus(FileLine* fl, AstNode* fromp, AstNode* bitp, AstNode* widthp)
	:AstNodePreSel(fl, fromp, bitp, widthp) {}
    ASTNODE_NODE_FUNCS(SelPlus, SELPLUS)
    AstNode*	bitp() const { return rhsp(); }
    AstNode*	widthp() const { return thsp(); }
};

class AstSelMinus : public AstNodePreSel {
    // -: range extraction, perhaps with non-constant selection
    // Gets replaced during link with AstSel
public:
    AstSelMinus(FileLine* fl, AstNode* fromp, AstNode* bitp, AstNode* widthp)
	:AstNodePreSel(fl, fromp, bitp, widthp) {}
    ASTNODE_NODE_FUNCS(SelMinus, SELMINUS)
    AstNode*	bitp() const { return rhsp(); }
    AstNode*	widthp() const { return thsp(); }
};

class AstSel : public AstNodeTriop {
    // Multiple bit range extraction
    // Parents: math|stmt
    // Children: varref|arraysel, math, constant math
    // Tempting to have an lvalue() style method here as LHS selects are quite
    // different, but that doesn't play well with V3Inst and bidirects which don't know direction
private:
    VNumRange	m_declRange;	// Range of the 'from' array if isRanged() is set, else invalid
    int		m_declElWidth;	// If a packed array, the number of bits per element
public:
    AstSel(FileLine* fl, AstNode* fromp, AstNode* lsbp, AstNode* widthp)
	:AstNodeTriop(fl, fromp, lsbp, widthp) {
	m_declElWidth = 1;
	if (widthp->castConst()) {
	    dtypeSetLogicSized(widthp->castConst()->toUInt(),
			       widthp->castConst()->toUInt(),
			       AstNumeric::UNSIGNED);
	}
    }
    AstSel(FileLine* fl, AstNode* fromp, int lsb, int bitwidth)
	:AstNodeTriop(fl, fromp,
		      new AstConst(fl,lsb), new AstConst(fl,bitwidth)) {
	m_declElWidth = 1;
	dtypeSetLogicSized(bitwidth,bitwidth,AstNumeric::UNSIGNED);
    }
    ASTNODE_NODE_FUNCS(Sel, SEL)
    virtual void dump(ostream& str);
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
    VNumRange& declRange() { return m_declRange; }
    void declRange(const VNumRange& flag) { m_declRange = flag; }
    int declElWidth() const { return m_declElWidth; }
    void declElWidth(int flag) { m_declElWidth = flag; }
};

class AstMemberSel : public AstNodeMath {
    // Parents: math|stmt
    // Children: varref|arraysel, math
private:
    // Don't need the class we are extracting from, as the "fromp()"'s datatype can get us to it
    string m_name;
public:
    AstMemberSel(FileLine* fl, AstNode* fromp, VFlagChildDType, const string& name)
	: AstNodeMath(fl), m_name(name) {
	setOp1p(fromp);
	dtypep(NULL);  // V3Width will resolve
    }
    AstMemberSel(FileLine* fl, AstNode* fromp, AstMemberDType* dtp)
	: AstNodeMath(fl) {
	setOp1p(fromp);
	dtypep(dtp);
	m_name = dtp->name();
    }
    ASTNODE_NODE_FUNCS(MemberSel, MEMBERSEL)
    virtual string name() const { return m_name; }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) {
	V3ERROR_NA; /* How can from be a const? */ }
    virtual string emitVerilog() { V3ERROR_NA; return ""; }  // Implemented specially
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool cleanOut() { return false; }
    virtual bool same(AstNode* samep) const { return true; } // dtype comparison does it all for us
    virtual int instrCount() const { return widthInstrs(); }
    AstNode* fromp() const { return op1p()->castNode(); }	// op1 = Extracting what (NULL=TBD during parsing)
    void fromp(AstNode* nodep) { setOp1p(nodep); }
};

class AstMethodSel : public AstNode {
    // A reference to a member task (or function)
    // We do not support generic member calls yet, so this is only enough to make built-in methods work
private:
    string		m_name;		// Name of variable
public:
    AstMethodSel(FileLine* fl, AstNode* fromp, VFlagChildDType, const string& name, AstNode* pinsp)
	: AstNode(fl), m_name(name) {
	setOp1p(fromp);
	dtypep(NULL);  // V3Width will resolve
	addNOp2p(pinsp);
    }
    AstMethodSel(FileLine* fl, AstNode* fromp, const string& name, AstNode* pinsp)
	:AstNode(fl), m_name(name) {
	setOp1p(fromp);
	addNOp2p(pinsp);
    }
    ASTNODE_NODE_FUNCS(MethodSel, METHODSEL)
    virtual string name() const { return m_name; }		// * = Var name
    virtual void name(const string& name) { m_name = name; }
    AstNode* fromp() const { return op1p()->castNode(); }	// op1 = Extracting what (NULL=TBD during parsing)
    void fromp(AstNode* nodep) { setOp1p(nodep); }
    AstNode* pinsp() const { return op2p()->castNode(); }	// op2 = Pin interconnection list
    void addPinsp(AstNode* nodep) { addOp2p(nodep); }
};

class AstVar : public AstNode {
    // A variable (in/out/wire/reg/param) inside a module
private:
    string	m_name;		// Name of variable
    string	m_origName;	// Original name before dot addition
    AstVarType	m_varType;	// Type of variable
    bool	m_input:1;	// Input or inout
    bool	m_output:1;	// Output or inout
    bool	m_tristate:1;	// Inout or triwire or trireg
    bool	m_declOutput:1; // Inout or output before tristate resolution
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
    bool	m_isPulldown:1;	// Tri0
    bool	m_isPullup:1;	// Tri1
    bool	m_isIfaceParent:1;	// dtype is reference to interface present in this module
    bool	m_noSubst:1;	// Do not substitute out references
    bool	m_trace:1;	// Trace this variable
    AstVarAttrClocker m_attrClocker;

    void	init() {
	m_input=false; m_output=false; m_tristate=false; m_declOutput=false;
	m_primaryIO=false;
	m_sc=false; m_scClocked=false; m_scSensitive=false;
	m_usedClock=false; m_usedParam=false; m_usedLoopIdx=false;
	m_sigPublic=false; m_sigModPublic=false; m_sigUserRdPublic=false; m_sigUserRWPublic=false;
	m_funcLocal=false; m_funcReturn=false;
	m_attrClockEn=false; m_attrScBv=false; m_attrIsolateAssign=false; m_attrSFormat=false;
	m_fileDescr=false; m_isConst=false; m_isStatic=false; m_isPulldown=false; m_isPullup=false;
	m_isIfaceParent=false; m_attrClocker=AstVarAttrClocker::CLOCKER_UNKNOWN; m_noSubst=false;
	m_trace=false;
    }
public:
    AstVar(FileLine* fl, AstVarType type, const string& name, VFlagChildDType, AstNodeDType* dtp)
	:AstNode(fl)
	, m_name(name), m_origName(name) {
	init();
	combineType(type);
	childDTypep(dtp);  // Only for parser
	dtypep(NULL);  // V3Width will resolve
    }
    AstVar(FileLine* fl, AstVarType type, const string& name, AstNodeDType* dtp)
	:AstNode(fl)
	, m_name(name), m_origName(name) {
	init();
	combineType(type);
	UASSERT(dtp,"AstVar created with no dtype");
	dtypep(dtp);
    }
    AstVar(FileLine* fl, AstVarType type, const string& name, VFlagLogicPacked, int wantwidth)
	:AstNode(fl)
	, m_name(name), m_origName(name) {
	init();
	combineType(type);
	dtypeSetLogicSized(wantwidth,wantwidth,AstNumeric::UNSIGNED);
    }
    AstVar(FileLine* fl, AstVarType type, const string& name, VFlagBitPacked, int wantwidth)
	:AstNode(fl)
	, m_name(name), m_origName(name) {
	init();
	combineType(type);
	dtypeSetLogicSized(wantwidth,wantwidth,AstNumeric::UNSIGNED);
    }
    AstVar(FileLine* fl, AstVarType type, const string& name, AstVar* examplep)
	:AstNode(fl)
	, m_name(name), m_origName(name) {
	init();
	combineType(type);
	if (examplep->childDTypep()) {
	    childDTypep(examplep->childDTypep()->cloneTree(true));
	}
	dtypeFrom(examplep);
    }
    ASTNODE_NODE_FUNCS(Var, VAR)
    virtual void dump(ostream& str);
    virtual string name() const { return m_name; }		// * = Var name
    virtual bool hasDType() const { return true; }
    virtual bool maybePointedTo() const { return true; }
    string origName() const { return m_origName; }		// * = Original name
    void origName(const string& name) { m_origName = name; }
    AstVarType varType() const { return m_varType; }  // * = Type of variable
    void varType(AstVarType type) { m_varType = type; }
    void varType2Out() { m_tristate=0; m_input=0; m_output=1; }
    void varType2In() {  m_tristate=0; m_input=1; m_output=0; }
    string	scType() const;	  // Return SysC type: bool, uint32_t, uint64_t, sc_bv
    string	cPubArgType(bool named, bool forReturn) const;  // Return C /*public*/ type for argument: bool, uint32_t, uint64_t, etc.
    string	dpiArgType(bool named, bool forReturn) const;  // Return DPI-C type for argument
    string	vlArgType(bool named, bool forReturn, bool forFunc) const;  // Return Verilator internal type for argument: CData, SData, IData, WData
    string	vlEnumType() const;  // Return VerilatorVarType: VLVT_UINT32, etc
    string	vlEnumDir() const;  // Return VerilatorVarDir: VLVD_INOUT, etc
    void	combineType(AstVarType type);
    AstNodeDType* getChildDTypep() const { return childDTypep(); }
    AstNodeDType* childDTypep() const { return op1p()->castNodeDType(); }	// op1 = Range of variable
    AstNodeDType* dtypeSkipRefp() const { return subDTypep()->skipRefp(); }
    AstBasicDType* basicp() const { return subDTypep()->basicp(); }  // (Slow) recurse down to find basic data type (Note don't need virtual - AstVar isn't a NodeDType)
    AstNode* 	valuep() const { return op3p()->castNode(); } // op3 = Initial value that never changes (static const)
    void	valuep(AstNode* nodep) { setOp3p(nodep); }    // It's valuep, not constp, as may be more complicated than an AstConst
    void	addAttrsp(AstNode* nodep) { addNOp4p(nodep); }
    AstNode*	attrsp() const { return op4p()->castNode(); }	// op4 = Attributes during early parse
    void	childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    AstNodeDType* subDTypep() const { return dtypep() ? dtypep() : childDTypep(); }
    void	attrClockEn(bool flag) { m_attrClockEn = flag; }
    void	attrClocker(AstVarAttrClocker flag) { m_attrClocker = flag; }
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
    void	isIfaceParent(bool flag) { m_isIfaceParent = flag; }
    void	funcLocal(bool flag) { m_funcLocal = flag; }
    void	funcReturn(bool flag) { m_funcReturn = flag; }
    void noSubst(bool flag) { m_noSubst=flag; }
    bool noSubst() const { return m_noSubst; }
    void trace(bool flag) { m_trace=flag; }
    // METHODS
    virtual void name(const string& name) { m_name = name; }
    virtual string directionName() const { return (isInout() ? "inout" : isInput() ? "input"
						   : isOutput() ? "output" : varType().ascii()); }
    bool	isInput() const { return m_input; }
    bool	isOutput() const { return m_output; }
    bool	isInOnly() const { return m_input && !m_output; }
    bool	isOutOnly() const { return m_output && !m_input; }
    bool	isInout() const { return m_input && m_output; }
    bool	isTristate() const  { return m_tristate; }
    bool	isDeclOutput() const  { return m_declOutput; }
    bool	isPrimaryIO() const { return m_primaryIO; }
    bool	isPrimaryIn() const { return isPrimaryIO() && isInput(); }
    bool	isIO() const  { return (m_input||m_output); }
    bool	isIfaceRef() const { return (varType()==AstVarType::IFACEREF); }
    bool	isIfaceParent() const { return m_isIfaceParent; }
    bool	isSignal() const  { return varType().isSignal(); }
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
    bool	isScUint() const;
    bool	isScBigUint() const;
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
    bool	isPullup() const { return m_isPullup; }
    bool	isPulldown() const { return m_isPulldown; }
    bool	attrClockEn() const { return m_attrClockEn; }
    bool	attrScBv() const { return m_attrScBv; }
    bool	attrFileDescr() const { return m_fileDescr; }
    bool	attrScClocked() const { return m_scClocked; }
    bool	attrSFormat() const { return m_attrSFormat; }
    bool	attrIsolateAssign() const { return m_attrIsolateAssign; }
    AstVarAttrClocker attrClocker() const { return m_attrClocker; }
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
    static AstVar* scVarRecurse(AstNode* nodep);
};

class AstDefParam : public AstNode {
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

class AstImplicit : public AstNode {
    // Create implicit wires and do nothing else, for gates that are ignored
    // Parents: MODULE
public:
    AstImplicit(FileLine* fl, AstNode* exprsp)
	: AstNode(fl) {
	addNOp1p(exprsp);
    }
    ASTNODE_NODE_FUNCS(Implicit, IMPLICIT)
    AstNode* exprsp() const { return op1p()->castNode(); }	// op1 = Assign from
};

class AstScope : public AstNode {
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
    virtual const char* broken() const;
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

class AstTopScope : public AstNode {
    // In the top level netlist, a complete scope tree
    // There may be two of these, when we support "rare" and "usual" splitting
    // Parents: topMODULE
    // Children: SCOPEs
public:
    AstTopScope(FileLine* fl, AstScope* ascopep)
	:AstNode(fl)
	{addNOp2p(ascopep);}
    ASTNODE_NODE_FUNCS(TopScope, TOPSCOPE)
    AstNode*	stmtsp() 	const { return op1p()->castNode(); }
    void addStmtsp(AstNode* nodep) { addOp1p(nodep); }
    AstScope* scopep()		const { return op2p()->castScope(); }	// op1 = AstVarScope's
};

class AstVarScope : public AstNode {
    // A particular scoped usage of a variable
    // That is, as a module is used under multiple cells, we get a different varscope for each var in the module
    // Parents: MODULE
    // Children: none
private:
    AstScope*	m_scopep;	// Scope variable is underneath
    AstVar*	m_varp;		// [AfterLink] Pointer to variable itself
    bool	m_circular:1;	// Used in circular ordering dependency, need change detect
    bool	m_trace:1;	// Tracing is turned on for this scope
public:
    AstVarScope(FileLine* fl, AstScope* scopep, AstVar* varp)
	:AstNode(fl)
	, m_scopep(scopep), m_varp(varp) {
	m_circular = false;
	m_trace = true;
	dtypeFrom(varp);
    }
    ASTNODE_NODE_FUNCS(VarScope, VARSCOPE)
    virtual void cloneRelink() { if (m_varp && m_varp->clonep()) {
	m_varp = m_varp->clonep()->castVar();
	UASSERT(m_scopep->clonep(), "No clone cross link: "<<this);
	m_scopep = m_scopep->clonep()->castScope();
    }}
    virtual const char* broken() const { BROKEN_RTN(m_varp && !m_varp->brokeExists());
	BROKEN_RTN(m_scopep && !m_scopep->brokeExists()); return NULL; }
    virtual bool maybePointedTo() const { return true; }
    virtual string name() const {return scopep()->name()+"->"+varp()->name();}	// * = Var name
    virtual void dump(ostream& str);
    virtual bool hasDType() const { return true; }
    AstVar*	varp() const { return m_varp; }			// [After Link] Pointer to variable
    AstScope*	scopep() const { return m_scopep; }		// Pointer to scope it's under
    AstNode*	valuep()	const { return op1p(); }	// op1 = Calculation of value of variable, NULL=complicated
    void	valuep(AstNode* valuep) { addOp1p(valuep); }
    bool	isCircular() const { return m_circular; }
    void	circular(bool flag) { m_circular = flag; }
    bool	isTrace() const { return m_trace; }
    void	trace(bool flag) { m_trace = flag; }
};

class AstVarRef : public AstNodeVarRef {
    // A reference to a variable (lvalue or rvalue)
public:
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
    virtual bool same(AstNode* samep) const { return same(samep->castVarRef()); }
    inline bool same(AstVarRef* samep) const {
	if (varScopep()) return (varScopep()==samep->varScopep()
				 && lvalue()==samep->lvalue());
	else return (hiername()==samep->hiername()
		     && varp()->name()==samep->varp()->name()
		     && lvalue()==samep->lvalue()); }
    inline bool sameNoLvalue(AstVarRef* samep) const {
	if (varScopep()) return (varScopep()==samep->varScopep());
	else return (hiername()==samep->hiername()
		     && varp()->name()==samep->varp()->name()); }
    virtual int instrCount() const { return widthInstrs()*(lvalue()?1:instrCountLd()); }
    virtual string emitVerilog() { V3ERROR_NA; return ""; }  // Implemented specially
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool cleanOut() { return true; }
};

class AstVarXRef : public AstNodeVarRef {
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
	dtypeFrom(varp);
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

class AstPin : public AstNode {
    // A pin on a cell
private:
    int		m_pinNum;	// Pin number
    string	m_name;		// Pin name, or "" for number based interconnect
    AstVar*	m_modVarp;	// Input/output this pin connects to on submodule.
    bool	m_param;	// Pin connects to parameter
    bool	m_svImplicit;	// Pin is SystemVerilog .name'ed
public:
    AstPin(FileLine* fl, int pinNum, const string& name, AstNode* exprp)
	:AstNode(fl)
	,m_name(name), m_param(false), m_svImplicit(false) {
	m_pinNum = pinNum;
	m_modVarp = NULL;
	setNOp1p(exprp);
    }
    AstPin(FileLine* fl, int pinNum, AstVarRef* varname, AstNode* exprp)
	:AstNode(fl), m_param(false), m_svImplicit(false) {
	m_name = varname->name();
	m_pinNum = pinNum;
	m_modVarp = NULL;
	setNOp1p(exprp);
    }
    ASTNODE_NODE_FUNCS(Pin, PIN)
    virtual void dump(ostream& str);
    virtual const char* broken() const { BROKEN_RTN(m_modVarp && !m_modVarp->brokeExists()); return NULL; }
    virtual string name()	const { return m_name; }		// * = Pin name, ""=go by number
    virtual void name(const string& name) { m_name = name; }
    virtual string prettyOperatorName() const { return modVarp()
	    ? (modVarp()->directionName()+" port connection '"+modVarp()->prettyName()+"'")
	    : "port connection"; }
    bool	dotStar()	const { return name() == ".*"; }	// Special fake name for .* connections until linked
    int		pinNum()	const { return m_pinNum; }
    void	exprp(AstNode* nodep) { addOp1p(nodep); }
    AstNode*	exprp()		const { return op1p()->castNode(); }	// op1 = Expression connected to pin, NULL if unconnected
    AstVar*	modVarp()	const { return m_modVarp; }		// [After Link] Pointer to variable
    void  	modVarp(AstVar* varp) { m_modVarp=varp; }
    bool	param()	const { return m_param; }
    void        param(bool flag) { m_param=flag; }
    bool	svImplicit() const { return m_svImplicit; }
    void        svImplicit(bool flag) { m_svImplicit=flag; }
};

class AstArg : public AstNode {
    // An argument to a function/task
private:
    string	m_name;		// Pin name, or "" for number based interconnect
public:
    AstArg(FileLine* fl, const string& name, AstNode* exprp)
	: AstNode(fl)
	,m_name(name) {
	setNOp1p(exprp);
    }
    ASTNODE_NODE_FUNCS(Arg, ARG)
    virtual string name()	const { return m_name; }		// * = Pin name, ""=go by number
    virtual void name(const string& name) { m_name = name; }
    virtual V3Hash sameHash() const { return V3Hash(); }
    void	exprp(AstNode* nodep) { addOp1p(nodep); }
    AstNode*	exprp()		const { return op1p()->castNode(); }	// op1 = Expression connected to pin, NULL if unconnected
    bool	emptyConnectNoNext() const { return !exprp() && name()=="" && !nextp(); }
};

class AstModule : public AstNodeModule {
    // A module declaration
public:
    AstModule(FileLine* fl, const string& name)
	: AstNodeModule (fl,name) {}
    ASTNODE_NODE_FUNCS(Module, MODULE)
    virtual string verilogKwd() const { return "module"; }
};

class AstNotFoundModule : public AstNodeModule {
    // A missing module declaration
public:
    AstNotFoundModule(FileLine* fl, const string& name)
	: AstNodeModule (fl,name) {}
    ASTNODE_NODE_FUNCS(NotFoundModule, NOTFOUNDMODULE)
    virtual string verilogKwd() const { return "/*not-found-*/ module"; }
};

class AstPackage : public AstNodeModule {
    // A package declaration
public:
    AstPackage(FileLine* fl, const string& name)
	: AstNodeModule (fl,name) {}
    ASTNODE_NODE_FUNCS(Package, PACKAGE)
    virtual string verilogKwd() const { return "package"; }
    static string dollarUnitName() { return AstNode::encodeName("$unit"); }
    bool isDollarUnit() const { return name() == dollarUnitName(); }
};

class AstPrimitive : public AstNodeModule {
    // A primitive declaration
public:
    AstPrimitive(FileLine* fl, const string& name)
	: AstNodeModule (fl,name) {}
    ASTNODE_NODE_FUNCS(Primitive, PRIMITIVE)
    virtual string verilogKwd() const { return "primitive"; }
};

class AstPackageImport : public AstNode {
private:
    // A package import declaration
    string	m_name;
    AstPackage*	m_packagep;	// Package hierarchy
public:
    AstPackageImport(FileLine* fl, AstPackage* packagep, const string& name)
	: AstNode (fl), m_name(name), m_packagep(packagep) {}
    ASTNODE_NODE_FUNCS(PackageImport, PACKAGEIMPORT)
    virtual const char* broken() const { BROKEN_RTN(!m_packagep || !m_packagep->brokeExists()); return NULL; }
    virtual void cloneRelink() { if (m_packagep && m_packagep->clonep()) m_packagep = m_packagep->clonep()->castPackage(); }
    virtual void dump(ostream& str);
    virtual string name() const { return m_name; }
    AstPackage* packagep() const { return m_packagep; }
    void packagep(AstPackage* nodep) { m_packagep=nodep; }
};

class AstIface : public AstNodeModule {
    // A module declaration
public:
    AstIface(FileLine* fl, const string& name)
	: AstNodeModule (fl,name) { }
    ASTNODE_NODE_FUNCS(Iface, IFACE)
};

class AstModportFTaskRef : public AstNode {
    // An import/export referenced under a modport
    // The storage for the function itself is inside the interface/instantiator, thus this is a reference
    // PARENT: AstModport
private:
    string	m_name;		// Name of the variable referenced
    bool	m_export;	// Type of the function (import/export)
    AstNodeFTask* m_ftaskp;	// Link to the function
public:
    AstModportFTaskRef(FileLine* fl, const string& name, bool isExport)
	: AstNode(fl), m_name(name), m_export(isExport), m_ftaskp(NULL) { }
    ASTNODE_NODE_FUNCS(ModportFTaskRef, MODPORTFTASKREF)
    virtual const char* broken() const { BROKEN_RTN(m_ftaskp && !m_ftaskp->brokeExists()); return NULL; }
    virtual void dump(ostream& str);
    virtual string name() const { return m_name; }
    virtual void cloneRelink() { if (m_ftaskp && m_ftaskp->clonep()) m_ftaskp = m_ftaskp->clonep()->castNodeFTask(); }
    bool isImport() const { return !m_export; }
    bool isExport() const { return m_export; }
    AstNodeFTask* ftaskp() const { return m_ftaskp; }		// [After Link] Pointer to variable
    void ftaskp(AstNodeFTask* ftaskp) { m_ftaskp=ftaskp; }
};

class AstModportVarRef : public AstNode {
    // A input/output/etc variable referenced under a modport
    // The storage for the variable itself is inside the interface, thus this is a reference
    // PARENT: AstModport
private:
    string	m_name;		// Name of the variable referenced
    AstVarType	m_type;		// Type of the variable (in/out)
    AstVar*	m_varp;		// Link to the actual Var
public:
    AstModportVarRef(FileLine* fl, const string& name, AstVarType::en type)
	: AstNode(fl), m_name(name), m_type(type), m_varp(NULL) { }
    ASTNODE_NODE_FUNCS(ModportVarRef, MODPORTVARREF)
    virtual const char* broken() const { BROKEN_RTN(m_varp && !m_varp->brokeExists()); return NULL; }
    virtual void dump(ostream& str);
    virtual void cloneRelink() { if (m_varp && m_varp->clonep()) m_varp = m_varp->clonep()->castVar(); }
    virtual string name() const { return m_name; }
    AstVarType	varType() const { return m_type; }		// * = Type of variable
    bool isInput() const { return (varType()==AstVarType::INPUT || varType()==AstVarType::INOUT); }
    bool isOutput() const { return (varType()==AstVarType::OUTPUT || varType()==AstVarType::INOUT); }
    AstVar* varp() const { return m_varp; }		// [After Link] Pointer to variable
    void varp(AstVar* varp) { m_varp=varp; }
};

class AstModport : public AstNode {
    // A modport in an interface
private:
    string	m_name;		// Name of the modport
public:
    AstModport(FileLine* fl, const string& name, AstNode* varsp)
	: AstNode(fl), m_name(name) {
        addNOp1p(varsp); }
    virtual string name() const { return m_name; }
    virtual bool maybePointedTo() const { return true; }
    ASTNODE_NODE_FUNCS(Modport, MODPORT)
    AstNode* varsp() const { return op1p(); }	// op1 = List of Vars
};

class AstCell : public AstNode {
    // A instantiation cell or interface call (don't know which until link)
private:
    string	m_name;		// Cell name
    string	m_origName;	// Original name before dot addition
    string	m_modName;	// Module the cell instances
    AstNodeModule* m_modp;	// [AfterLink] Pointer to module instanced
    bool	m_hasIfaceVar:1; // True if a Var has been created for this cell
    bool	m_trace:1;	// Trace this cell
public:
    AstCell(FileLine* fl, const string& instName, const string& modName,
	    AstPin* pinsp, AstPin* paramsp, AstRange* rangep)
	: AstNode(fl)
	, m_name(instName), m_origName(instName), m_modName(modName)
	, m_modp(NULL), m_hasIfaceVar(false), m_trace(true) {
	addNOp1p(pinsp); addNOp2p(paramsp); setNOp3p(rangep); }
    ASTNODE_NODE_FUNCS(Cell, CELL)
    // No cloneRelink, we presume cloneee's want the same module linkages
    virtual void dump(ostream& str);
    virtual const char* broken() const { BROKEN_RTN(m_modp && !m_modp->brokeExists()); return NULL; }
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
    bool hasIfaceVar() const { return m_hasIfaceVar; }
    void hasIfaceVar(bool flag) { m_hasIfaceVar = flag; }
    void trace(bool flag) { m_trace=flag; }
    bool isTrace() const { return m_trace; }
};

class AstCellInline : public AstNode {
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

class AstBind : public AstNode {
    // Parents: MODULE
    // Children: CELL
private:
    string	m_name;		// Binding to name
public:
    AstBind(FileLine* fl, const string& name, AstNode* cellsp)
	: AstNode(fl)
	, m_name(name) {
	if (!cellsp->castCell()) cellsp->v3fatalSrc("Only cells allowed to be bound");
	addNOp1p(cellsp);
    }
    ASTNODE_NODE_FUNCS(Bind, BIND)
    // ACCESSORS
    virtual string name() const { return m_name; }		// * = Bind Target name
    virtual void name(const string& name) { m_name = name; }
    AstNode* cellsp() const { return op1p(); }	// op1= cells
};

class AstPort : public AstNode {
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

class AstGenerate : public AstNode {
    // A Generate/end block
    // Parents: MODULE
    // Children: modItems
public:
    AstGenerate(FileLine* fileline, AstNode* stmtsp)
	: AstNode(fileline) {
	addNOp1p(stmtsp);
    }
    ASTNODE_NODE_FUNCS(Generate, GENERATE)
    // op1 = Statements
    AstNode*	stmtsp() 	const { return op1p()->castNode(); }	// op1 = List of statements
    void addStmtp(AstNode* nodep) { addOp1p(nodep); }
};

class AstParseRef : public AstNode {
    // A reference to a variable, function or task
    // We don't know which at parse time due to bison constraints
    // The link stages will replace this with AstVarRef, or AstTaskRef, etc.
    // Parents: math|stmt
    // Children: TEXT|DOT|SEL*|TASK|FUNC (or expression under sel)
private:
    AstParseRefExp	m_expect;		// Type we think it should resolve to
    string		m_name;
public:
    AstParseRef(FileLine* fl, AstParseRefExp expect, const string& name, AstNode* lhsp, AstNodeFTaskRef* ftaskrefp)
	:AstNode(fl), m_expect(expect), m_name(name) { setNOp1p(lhsp); setNOp2p(ftaskrefp); }
    ASTNODE_NODE_FUNCS(ParseRef, PARSEREF)
    virtual void dump(ostream& str);
    virtual string name() const { return m_name; }		// * = Var name
    virtual V3Hash sameHash() const { return V3Hash(V3Hash(m_expect),V3Hash(m_name)); }
    virtual bool same(AstNode* samep) const {
	return (expect() == samep->castParseRef()->expect()
		&& m_name==samep->castParseRef()->m_name); }
    virtual string emitVerilog() { V3ERROR_NA; return ""; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual void name(const string& name) 	{ m_name = name; }
    AstParseRefExp expect() const { return m_expect; }
    void expect(AstParseRefExp exp) { m_expect=exp; }
    // op1 = Components
    AstNode*	lhsp() 		const { return op1p(); }	// op1 = List of statements
    AstNode*	ftaskrefp()	const { return op2p(); }	// op2 = Function/task reference
    void ftaskrefp(AstNodeFTaskRef* nodep) { setNOp2p(nodep); }	// op2 = Function/task reference
};

class AstPackageRef : public AstNode {
private:
    AstPackage*	m_packagep;	// Package hierarchy
public:
    AstPackageRef(FileLine* fl, AstPackage* packagep)
	: AstNode(fl), m_packagep(packagep) {}
    ASTNODE_NODE_FUNCS(PackageRef, PACKAGEREF)
    // METHODS
    virtual const char* broken() const { BROKEN_RTN(!m_packagep || !m_packagep->brokeExists()); return NULL; }
    virtual void cloneRelink() { if (m_packagep && m_packagep->clonep()) {
	m_packagep = m_packagep->clonep()->castPackage();
    }}
    virtual bool same(AstNode* samep) const {
	return (m_packagep==samep->castPackageRef()->m_packagep); }
    virtual V3Hash sameHash() const { return V3Hash(V3Hash(m_packagep)); }
    virtual void dump(ostream& str=cout);
    AstPackage* packagep() const { return m_packagep; }
    void packagep(AstPackage* nodep) { m_packagep=nodep; }
};

class AstDot : public AstNode {
    // A dot separating paths in an AstXRef, AstFuncRef or AstTaskRef
    // These are eliminated in the link stage
public:
    AstDot(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
	:AstNode(fl) { setOp1p(lhsp); setOp2p(rhsp); }
    ASTNODE_NODE_FUNCS(Dot, DOT)
    static AstNode* newIfPkg(FileLine*fl, AstPackage* packagep, AstNode* rhsp) {  // For parser, make only if non-null package
	if (!packagep) return rhsp;
	return new AstDot(fl, new AstPackageRef(fl, packagep), rhsp);
    }
    virtual void dump(ostream& str);
    virtual string emitVerilog() { V3ERROR_NA; return ""; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    AstNode* lhsp() const { return op1p(); }
    AstNode* rhsp() const { return op2p(); }
};

//######################################################################

class AstTask : public AstNodeFTask {
    // A task inside a module
public:
    AstTask(FileLine* fl, const string& name, AstNode* stmtp)
	:AstNodeFTask(fl, name, stmtp) {}
    ASTNODE_NODE_FUNCS(Task, TASK)
};

class AstFunc : public AstNodeFTask {
    // A function inside a module
public:
    AstFunc(FileLine* fl, const string& name, AstNode* stmtp, AstNode* fvarsp)
	:AstNodeFTask(fl, name, stmtp) {
	addNOp1p(fvarsp);
    }
    ASTNODE_NODE_FUNCS(Func, FUNC)
    virtual bool hasDType() const { return true; }
};

class AstTaskRef : public AstNodeFTaskRef {
    // A reference to a task
public:
    AstTaskRef(FileLine* fl, AstParseRef* namep, AstNode* pinsp)
	:AstNodeFTaskRef(fl, namep, pinsp) {}
    AstTaskRef(FileLine* fl, const string& name, AstNode* pinsp)
	:AstNodeFTaskRef(fl, name, pinsp) {}
    ASTNODE_NODE_FUNCS(TaskRef, TASKREF)
};

class AstFuncRef : public AstNodeFTaskRef {
    // A reference to a function
public:
    AstFuncRef(FileLine* fl, AstParseRef* namep, AstNode* pinsp)
	:AstNodeFTaskRef(fl, namep, pinsp) {}
    AstFuncRef(FileLine* fl, const string& name, AstNode* pinsp)
	:AstNodeFTaskRef(fl, name, pinsp) {}
    ASTNODE_NODE_FUNCS(FuncRef, FUNCREF)
    virtual bool hasDType() const { return true; }
};

class AstDpiExport : public AstNode {
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

class AstSenItem : public AstNodeSenItem {
    // Parents:  SENTREE
    // Children: (optional) VARREF SENGATE
private:
    AstEdgeType	m_edgeType;		// Edge type
public:
    class Combo {};		// for creator type-overload selection
    class Initial {};		// for creator type-overload selection
    class Settle {};		// for creator type-overload selection
    class Never {};		// for creator type-overload selection
    AstSenItem(FileLine* fl, AstEdgeType edgeType, AstNode* varrefp)
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

class AstSenGate : public AstNodeSenItem {
    // Parents:  SENTREE
    // Children: SENITEM expr
    // AND as applied to a sensitivity list and a gating expression
    // Performing this gating is optional; it may be removed by later optimizations
public:
    AstSenGate(FileLine* fl, AstSenItem* sensesp, AstNode* rhsp) : AstNodeSenItem(fl) {
	dtypeSetLogicBool(); addOp1p(sensesp); setOp2p(rhsp);
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

class AstSenTree : public AstNode {
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

class AstAlways : public AstNode {
    VAlwaysKwd m_keyword;
public:
    AstAlways(FileLine* fl, VAlwaysKwd keyword, AstSenTree* sensesp, AstNode* bodysp)
	: AstNode(fl), m_keyword(keyword) {
	addNOp1p(sensesp); addNOp2p(bodysp);
    }
    ASTNODE_NODE_FUNCS(Always, ALWAYS)
    //
    virtual void dump(ostream& str);
    AstSenTree*	sensesp() 	const { return op1p()->castSenTree(); }	// op1 = Sensitivity list
    AstNode*	bodysp() 	const { return op2p()->castNode(); }	// op2 = Statements to evaluate
    void addStmtp(AstNode* nodep) { addOp2p(nodep); }
    VAlwaysKwd keyword() const { return m_keyword; }
    // Special accessors
    bool isJustOneBodyStmt() const { return bodysp() && !bodysp()->nextp(); }
};

class AstAlwaysPublic : public AstNodeStmt {
    // "Fake" sensitivity created by /*verilator public_flat_rw @(edgelist)*/
    // Body statements are just AstVarRefs to the public signals
public:
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

class AstAlwaysPost : public AstNode {
    // Like always but post assignments for memory assignment IFs
public:
    AstAlwaysPost(FileLine* fl, AstSenTree* sensesp, AstNode* bodysp)
	: AstNode(fl) {
	addNOp1p(sensesp); addNOp2p(bodysp);
    }
    ASTNODE_NODE_FUNCS(AlwaysPost, ALWAYSPOST)
    //
    AstNode*	bodysp() 	const { return op2p()->castNode(); }	// op2 = Statements to evaluate
    void	addBodysp(AstNode* newp)	{ addOp2p(newp); }
};

class AstAssign : public AstNodeAssign {
public:
    AstAssign(FileLine* fileline, AstNode* lhsp, AstNode* rhsp)
	: AstNodeAssign(fileline, lhsp, rhsp) {
	dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(Assign, ASSIGN)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) { return new AstAssign(this->fileline(), lhsp, rhsp); }
};

class AstAssignAlias : public AstNodeAssign {
    // Like AstAssignW, but a true bidirect interconnection alias
    // If both sides are wires, there's no LHS vs RHS,
public:
    AstAssignAlias(FileLine* fileline, AstVarRef* lhsp, AstVarRef* rhsp)
	: AstNodeAssign(fileline, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(AssignAlias, ASSIGNALIAS)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) { V3ERROR_NA; return NULL; }
};

class AstAssignDly : public AstNodeAssign {
public:
    AstAssignDly(FileLine* fileline, AstNode* lhsp, AstNode* rhsp)
	: AstNodeAssign(fileline, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(AssignDly, ASSIGNDLY)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) { return new AstAssignDly(this->fileline(), lhsp, rhsp); }
    virtual bool isGateOptimizable() const { return false; }
    virtual string verilogKwd() const { return "<="; }
};

class AstAssignW : public AstNodeAssign {
    // Like assign, but wire/assign's in verilog, the only setting of the specified variable
public:
    AstAssignW(FileLine* fileline, AstNode* lhsp, AstNode* rhsp)
	: AstNodeAssign(fileline, lhsp, rhsp) { }
    ASTNODE_NODE_FUNCS(AssignW, ASSIGNW)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) { return new AstAssignW(this->fileline(), lhsp, rhsp); }
    AstAlways* convertToAlways() {
	AstNode* lhs1p = lhsp()->unlinkFrBack();
	AstNode* rhs1p = rhsp()->unlinkFrBack();
	AstAlways* newp = new AstAlways (fileline(), VAlwaysKwd::ALWAYS, NULL,
					 new AstAssign (fileline(), lhs1p, rhs1p));
	replaceWith(newp); // User expected to then deleteTree();
	return newp;
    }
};

class AstAssignVarScope : public AstNodeAssign {
    // Assign two VarScopes to each other
public:
    AstAssignVarScope(FileLine* fileline, AstNode* lhsp, AstNode* rhsp)
	: AstNodeAssign(fileline, lhsp, rhsp) {
	dtypeFrom(rhsp);
    }
    ASTNODE_NODE_FUNCS(AssignVarScope, ASSIGNVARSCOPE)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) { return new AstAssignVarScope(this->fileline(), lhsp, rhsp); }
};

class AstPull : public AstNode {
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

class AstAssignPre : public AstNodeAssign {
    // Like Assign, but predelayed assignment requiring special order handling
public:
    AstAssignPre(FileLine* fileline, AstNode* lhsp, AstNode* rhsp)
	: AstNodeAssign(fileline, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(AssignPre, ASSIGNPRE)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) { return new AstAssignPre(this->fileline(), lhsp, rhsp); }
};

class AstAssignPost : public AstNodeAssign {
    // Like Assign, but predelayed assignment requiring special order handling
public:
    AstAssignPost(FileLine* fileline, AstNode* lhsp, AstNode* rhsp)
	: AstNodeAssign(fileline, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(AssignPost, ASSIGNPOST)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) { return new AstAssignPost(this->fileline(), lhsp, rhsp); }
};

class AstComment : public AstNodeStmt {
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

class AstCond : public AstNodeCond {
    // Conditional ?: statement
    // Parents:  MATH
    // Children: MATH
public:
    AstCond(FileLine* fl, AstNode* condp, AstNode* expr1p, AstNode* expr2p)
	: AstNodeCond(fl, condp, expr1p, expr2p) {}
    ASTNODE_NODE_FUNCS(Cond, COND)
};

class AstCondBound : public AstNodeCond {
    // Conditional ?: statement, specially made for saftey checking of array bounds
    // Parents:  MATH
    // Children: MATH
public:
    AstCondBound(FileLine* fl, AstNode* condp, AstNode* expr1p, AstNode* expr2p)
	: AstNodeCond(fl, condp, expr1p, expr2p) {}
    ASTNODE_NODE_FUNCS(CondBound, CONDBOUND)
};

class AstCoverDecl : public AstNodeStmt {
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
    virtual const char* broken() const {
	BROKEN_RTN(m_dataDeclp && !m_dataDeclp->brokeExists());
	if (m_dataDeclp && m_dataDeclp->m_dataDeclp) v3fatalSrc("dataDeclp should point to real data, not be a list");  // Avoid O(n^2) accessing
        return NULL; }
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

class AstCoverInc : public AstNodeStmt {
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
    virtual const char* broken() const { BROKEN_RTN(!declp()->brokeExists()); return NULL; }
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

class AstCoverToggle : public AstNodeStmt {
    // Toggle analysis of given signal
    // Parents:  MODULE
    // Children: AstCoverInc, orig var, change det var
public:
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

class AstGenCase : public AstNodeCase {
    // Generate Case statement
    // Parents:  {statement list}
    // exprp Children:  MATHs
    // casesp Children: CASEITEMs
public:
    AstGenCase(FileLine* fileline, AstNode* exprp, AstNode* casesp)
	: AstNodeCase(fileline, exprp, casesp) {
    }
    ASTNODE_NODE_FUNCS(GenCase, GENCASE)
};

class AstCase : public AstNodeCase {
    // Case statement
    // Parents:  {statement list}
    // exprp Children:  MATHs
    // casesp Children: CASEITEMs
private:
    VCaseType	m_casex;		// 0=case, 1=casex, 2=casez
    bool	m_fullPragma;		// Synthesis full_case
    bool	m_parallelPragma;	// Synthesis parallel_case
    bool	m_uniquePragma;		// unique case
    bool	m_unique0Pragma;	// unique0 case
    bool	m_priorityPragma;	// priority case
public:
    AstCase(FileLine* fileline, VCaseType casex, AstNode* exprp, AstNode* casesp)
	: AstNodeCase(fileline, exprp, casesp) {
	m_casex=casex;
	m_fullPragma=false; m_parallelPragma=false;
	m_uniquePragma=false; m_unique0Pragma=false; m_priorityPragma=false;
    }
    ASTNODE_NODE_FUNCS(Case, CASE)
    virtual string  verilogKwd() const { return casez()?"casez":casex()?"casex":"case"; }
    virtual bool same(AstNode* samep) const {
	return m_casex==samep->castCase()->m_casex; }
    bool	casex()	const { return m_casex==VCaseType::CT_CASEX; }
    bool	casez()	const { return m_casex==VCaseType::CT_CASEZ; }
    bool	caseInside() const { return m_casex==VCaseType::CT_CASEINSIDE; }
    bool	caseSimple() const { return m_casex==VCaseType::CT_CASE; }
    void	caseInsideSet()	{ m_casex=VCaseType::CT_CASEINSIDE; }
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

class AstCaseItem : public AstNode {
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

class AstSFormatF : public AstNode {
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

class AstDisplay : public AstNodeStmt {
    // Parents: stmtlist
    // Children: file which must be a varref
    // Children: SFORMATF to generate print string
private:
    AstDisplayType	m_displayType;
public:
    AstDisplay(FileLine* fileline, AstDisplayType dispType, const string& text, AstNode* filep, AstNode* exprsp)
	: AstNodeStmt (fileline) {
	setOp1p(new AstSFormatF(fileline,text,true,exprsp));
	setNOp3p(filep);
	m_displayType = dispType;
    }
    ASTNODE_NODE_FUNCS(Display, DISPLAY)
    virtual void dump(ostream& str);
    virtual const char* broken() const { BROKEN_RTN(!fmtp()); return NULL; }
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

class AstSFormat : public AstNodeStmt {
    // Parents: statement container
    // Children: string to load
    // Children: SFORMATF to generate print string
public:
    AstSFormat(FileLine* fileline, AstNode* lhsp, const string& text, AstNode* exprsp)
	: AstNodeStmt (fileline) {
	setOp1p(new AstSFormatF(fileline,text,true,exprsp));
	setOp3p(lhsp);
    }
    ASTNODE_NODE_FUNCS(SFormat, SFORMAT)
    virtual const char* broken() const { BROKEN_RTN(!fmtp()); return NULL; }
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

class AstSysIgnore : public AstNodeStmt {
    // Parents: stmtlist
    // Children: varrefs or exprs
public:
    AstSysIgnore(FileLine* fileline, AstNode* exprsp)
	: AstNodeStmt (fileline) { addNOp1p(exprsp); }
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

class AstFClose : public AstNodeStmt {
    // Parents: stmtlist
    // Children: file which must be a varref
public:
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

class AstFOpen : public AstNodeStmt {
    // Although a system function in IEEE, here a statement which sets the file pointer (MCD)
public:
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

class AstFFlush : public AstNodeStmt {
    // Parents: stmtlist
    // Children: file which must be a varref
public:
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

class AstFScanF : public AstNodeMath {
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

class AstSScanF : public AstNodeMath {
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

class AstReadMem : public AstNodeStmt {
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

class AstSystemT : public AstNodeStmt {
    // $system used as task
public:
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

class AstSystemF : public AstNodeMath {
    // $system used as function
public:
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

class AstValuePlusArgs : public AstNodeMath {
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

class AstTestPlusArgs : public AstNodeMath {
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

class AstGenFor : public AstNodeFor {
public:
    AstGenFor(FileLine* fileline, AstNode* initsp, AstNode* condp,
	   AstNode* incsp, AstNode* bodysp)
	: AstNodeFor(fileline, initsp, condp, incsp, bodysp) {
    }
    ASTNODE_NODE_FUNCS(GenFor, GENFOR)
};

class AstRepeat : public AstNodeStmt {
public:
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

class AstWhile : public AstNodeStmt {
public:
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

class AstBreak : public AstNodeStmt {
public:
    AstBreak(FileLine* fileline)
	: AstNodeStmt (fileline) {}
    ASTNODE_NODE_FUNCS(Break, BREAK)
    virtual string verilogKwd() const { return "break"; };
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool isBrancher() const { return true; }	// SPECIAL: We don't process code after breaks
};

class AstContinue : public AstNodeStmt {
public:
    AstContinue(FileLine* fileline)
	: AstNodeStmt (fileline) {}
    ASTNODE_NODE_FUNCS(Continue, CONTINUE)
    virtual string verilogKwd() const { return "continue"; };
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool isBrancher() const { return true; }	// SPECIAL: We don't process code after breaks
};

class AstDisable : public AstNodeStmt {
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

class AstReturn : public AstNodeStmt {
public:
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

class AstGenIf : public AstNodeIf {
public:
    AstGenIf(FileLine* fileline, AstNode* condp, AstNode* ifsp, AstNode* elsesp)
	: AstNodeIf(fileline, condp, ifsp, elsesp) {
    }
    ASTNODE_NODE_FUNCS(GenIf, GENIF)
};

class AstIf : public AstNodeIf {
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

class AstJumpLabel : public AstNodeStmt {
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

class AstJumpGo : public AstNodeStmt {
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
    virtual const char* broken() const { BROKEN_RTN(!labelp()->brokeExistsAbove()); return NULL; }
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

class AstUntilStable : public AstNodeStmt {
    // Quasi-while loop until given signals are stable
    // Parents: CFUNC (generally)
    // Children: VARREF, statements
public:
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

class AstChangeXor : public AstNodeBiComAsv {
    // A comparison to determine change detection, common & must be fast.
    // Returns 32-bit or 64-bit value where 0 indicates no change.
    // Parents: OR or LOGOR
    // Children: VARREF
public:
    AstChangeXor(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
	: AstNodeBiComAsv(fl, lhsp, rhsp) {
	dtypeSetUInt32(); // Always used on, and returns word entities
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

class AstChangeDet : public AstNodeStmt {
    // A comparison to determine change detection, common & must be fast.
private:
    bool	m_clockReq;	// Type of detection
public:
    // Null lhs+rhs used to indicate change needed with no spec vars
    AstChangeDet(FileLine* fl, AstNode* lhsp, AstNode* rhsp, bool clockReq)
	: AstNodeStmt(fl) {
	setNOp1p(lhsp); setNOp2p(rhsp); m_clockReq=clockReq;
    }
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

class AstBegin : public AstNode {
    // A Begin/end named block, only exists shortly after parsing until linking
    // Parents: statement
    // Children: statements
private:
    string	m_name;		// Name of block
    bool	m_unnamed;	// Originally unnamed
    bool	m_generate;	// Underneath a generate
public:
    // Node that simply puts name into the output stream
    AstBegin(FileLine* fileline, const string& name, AstNode* stmtsp, bool generate=false)
	: AstNode(fileline)
	, m_name(name) {
	addNOp1p(stmtsp);
	m_unnamed = (name=="");
	m_generate = generate;
    }
    ASTNODE_NODE_FUNCS(Begin, BEGIN)
    virtual void dump(ostream& str);
    virtual string name()	const { return m_name; }		// * = Block name
    virtual void name(const string& name) { m_name = name; }
    // op1 = Statements
    AstNode* stmtsp() const { return op1p()->castNode(); }	// op1 = List of statements
    void addStmtsp(AstNode* nodep) { addNOp1p(nodep); }
    AstNode* genforp() const { return op2p(); } // op2 = GENFOR, if applicable,
    // might NOT be a GenFor, as loop unrolling replaces with Begin
    void addGenforp(AstGenFor* nodep) { addOp2p(nodep); }
    bool unnamed() const { return m_unnamed; }
    void generate(bool flag) { m_generate = flag; }
    bool generate() const { return m_generate; }
};

class AstInitial : public AstNode {
public:
    AstInitial(FileLine* fl, AstNode* bodysp)
	: AstNode(fl) {
	addNOp1p(bodysp);
    }
    ASTNODE_NODE_FUNCS(Initial, INITIAL)
    AstNode*	bodysp() 	const { return op1p()->castNode(); }	// op1 = Expressions to evaluate
    // Special accessors
    bool isJustOneBodyStmt() const { return bodysp() && !bodysp()->nextp(); }
};

class AstFinal : public AstNode {
public:
    AstFinal(FileLine* fl, AstNode* bodysp)
	: AstNode(fl) {
	addNOp1p(bodysp);
    }
    ASTNODE_NODE_FUNCS(Final, FINAL)
    AstNode*	bodysp() 	const { return op1p()->castNode(); }	// op1 = Expressions to evaluate
};

class AstInside : public AstNodeMath {
public:
    AstInside(FileLine* fl, AstNode* exprp, AstNode* itemsp)
	: AstNodeMath(fl) {
	addOp1p(exprp); addOp2p(itemsp);
	dtypeSetLogicBool();
    }
    ASTNODE_NODE_FUNCS(Inside, INSIDE)
    AstNode* exprp() const { return op1p()->castNode(); }	// op1 = LHS expression to compare with
    AstNode* itemsp() const { return op2p()->castNode(); }	// op2 = RHS, possibly a list of expr or AstInsideRange
    virtual string emitVerilog() { return "%l inside { %r }"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool cleanOut() { return false; }  // NA
};

class AstInsideRange : public AstNodeMath {
public:
    AstInsideRange(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
	: AstNodeMath(fl) {
	addOp1p(lhsp); addOp2p(rhsp);
    }
    ASTNODE_NODE_FUNCS(InsideRange, INSIDERANGE)
    AstNode* lhsp() const { return op1p()->castNode(); }	// op1 = LHS
    AstNode* rhsp() const { return op2p()->castNode(); }	// op2 = RHS
    virtual string emitVerilog() { return "[%l:%r]"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool cleanOut() { return false; }  // NA
};

class AstInitArray : public AstNode {
    // Set a var to a large list of values
    // The values must be in sorted order, and not exceed the size of the var's array.
    // The first value on the initsp() list is for the lo() index of the array.
    // Parents: ASTVAR::init()
    // Children: CONSTs...
public:
    AstInitArray(FileLine* fl, AstNodeArrayDType* newDTypep, AstNode* initsp)
	: AstNode(fl) {
	dtypep(newDTypep);
	addNOp1p(initsp);
    }
    ASTNODE_NODE_FUNCS(InitArray, INITARRAY)
    AstNode*	initsp() 	const { return op1p()->castNode(); }	// op1 = Initial value expressions
    void	addInitsp(AstNode* newp)	{ addOp1p(newp); }
    virtual bool hasDType() const { return true; }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
};

class AstPragma : public AstNode {
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

class AstStop : public AstNodeStmt {
public:
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

class AstFinish : public AstNodeStmt {
public:
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

class AstTraceDecl : public AstNodeStmt {
    // Trace point declaration
    // Separate from AstTraceInc; as a declaration can't be deleted
    // Parents:  {statement list}
    // Children: none
private:
    string	m_showname;	// Name of variable
    uint32_t	m_code;		// Trace identifier code; converted to ASCII by trace routines
    VNumRange	m_bitRange;	// Property of var the trace details
    VNumRange	m_arrayRange;	// Property of var the trace details
    uint32_t	m_codeInc;	// Code increment
public:
    AstTraceDecl(FileLine* fl, const string& showname, AstNode* valuep,
		 const VNumRange& bitRange, const VNumRange& arrayRange)
	: AstNodeStmt(fl)
	, m_showname(showname), m_bitRange(bitRange), m_arrayRange(arrayRange) {
	dtypeFrom(valuep);
	m_code = 0;
	m_codeInc = ((arrayRange.ranged() ? arrayRange.elements() : 1)
		     * valuep->dtypep()->widthWords());
    }
    virtual int instrCount()	const { return 100; }  // Large...
    ASTNODE_NODE_FUNCS(TraceDecl, TRACEDECL)
    virtual string name()	const { return m_showname; }
    virtual bool maybePointedTo() const { return true; }
    virtual bool hasDType() const { return true; }
    virtual bool same(AstNode* samep) const { return false; }
    string showname()	const { return m_showname; }		// * = Var name
    // Details on what we're tracing
    uint32_t	code() const { return m_code; }
    void	code(uint32_t code) { m_code=code; }
    uint32_t	codeInc() const { return m_codeInc; }
    const VNumRange& bitRange() const { return m_bitRange; }
    const VNumRange& arrayRange() const { return m_arrayRange; }
};

class AstTraceInc : public AstNodeStmt {
    // Trace point; incremental change detect and dump
    // Parents:  {statement list}
    // Children: incremental value
private:
    AstTraceDecl*	m_declp;	// [After V3Trace] Pointer to declaration
public:
    AstTraceInc(FileLine* fl, AstTraceDecl* declp, AstNode* valuep)
	: AstNodeStmt(fl) {
	dtypeFrom(declp);
	m_declp = declp;
	addNOp2p(valuep);
    }
    ASTNODE_NODE_FUNCS(TraceInc, TRACEINC)
    virtual const char* broken() const { BROKEN_RTN(!declp()->brokeExists()); return NULL; }
    virtual void cloneRelink() { if (m_declp->clonep()) m_declp = m_declp->clonep()->castTraceDecl(); }
    virtual void dump(ostream& str);
    virtual int instrCount()	const { return 10+2*instrCountLd(); }
    virtual bool hasDType() const { return true; }
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

class AstActive : public AstNode {
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
    virtual const char* broken() const { BROKEN_RTN(m_sensesp && !m_sensesp->brokeExists()); return NULL; }
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

class AstAttrOf : public AstNode {
private:
    // Return a value of a attribute, for example a LSB or array LSB of a signal
    AstAttrType	m_attrType;	// What sort of extraction
public:
    AstAttrOf(FileLine* fl, AstAttrType attrtype, AstNode* fromp=NULL, AstNode* dimp=NULL)
	: AstNode(fl) {
	setNOp1p(fromp);
	setNOp2p(dimp);
	m_attrType = attrtype; }
    ASTNODE_NODE_FUNCS(AttrOf, ATTROF)
    AstNode*	fromp() const { return op1p(); }
    AstNode*	dimp() const { return op2p(); }
    AstAttrType	attrType() const { return m_attrType; }
    virtual void dump(ostream& str=cout);
};

class AstScopeName : public AstNodeMath {
    // For display %m and DPI context imports
    // Parents:  DISPLAY
    // Children: TEXT
private:
    bool	m_dpiExport;	// Is for dpiExport
    string scopeNameFormatter(AstText* textp) const;
    string scopePrettyNameFormatter(AstText* textp) const;
public:
    AstScopeName(FileLine* fl) : AstNodeMath(fl), m_dpiExport(false) {
	dtypeSetUInt64(); }
    ASTNODE_NODE_FUNCS(ScopeName, SCOPENAME)
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return m_dpiExport==samep->castScopeName()->m_dpiExport; }
    virtual string emitVerilog() { return ""; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool cleanOut() { return true; }
    AstText*	scopeAttrp() const { return op1p()->castText(); }
    void 	scopeAttrp(AstNode* nodep) { addOp1p(nodep); }
    AstText*	scopeEntrp() const { return op2p()->castText(); }
    void 	scopeEntrp(AstNode* nodep) { addOp2p(nodep); }
    string scopeSymName() const { return scopeNameFormatter(scopeAttrp()); }  // Name for __Vscope variable including children
    string scopeDpiName() const { return scopeNameFormatter(scopeEntrp()); }  // Name for DPI import scope
    string scopePrettySymName() const { return scopePrettyNameFormatter(scopeAttrp()); }  // Name for __Vscope variable including children
    string scopePrettyDpiName() const { return scopePrettyNameFormatter(scopeEntrp()); }  // Name for __Vscope variable including children
    bool dpiExport() const { return m_dpiExport; }
    void dpiExport(bool flag) { m_dpiExport=flag; }
};

class AstUdpTable : public AstNode {
public:
    AstUdpTable(FileLine* fl, AstNode* bodysp)
	: AstNode(fl) {
	addNOp1p(bodysp);
    }
    ASTNODE_NODE_FUNCS(UdpTable, UDPTABLE)
    AstUdpTableLine*	bodysp() 	const { return op1p()->castUdpTableLine(); }	// op1 = List of UdpTableLines
};

class AstUdpTableLine : public AstNode {
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

class AstRand : public AstNodeTermop {
    // Return a random number, based upon width()
private:
    bool	m_reset;	// Random reset, versus always random
public:
    AstRand(FileLine* fl, AstNodeDType* dtp, bool reset) : AstNodeTermop(fl) {
	dtypep(dtp); m_reset=reset; }
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

class AstTime : public AstNodeTermop {
public:
    AstTime(FileLine* fl)	: AstNodeTermop(fl) {
	dtypeSetUInt64(); }
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

class AstTimeD : public AstNodeTermop {
public:
    AstTimeD(FileLine* fl)	: AstNodeTermop(fl) {
	dtypeSetDouble(); }
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

class AstUCFunc : public AstNodeMath {
    // User's $c function
    // Perhaps this should be an AstNodeListop; but there's only one list math right now
public:
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

class AstNegate : public AstNodeUniop {
public:
    AstNegate(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeFrom(lhsp); }
    ASTNODE_NODE_FUNCS(Negate, NEGATE)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opNegate(lhs); }
    virtual string emitVerilog() { return "%f(- %l)"; }
    virtual string emitC() { return "VL_NEGATE_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return false;}
    virtual bool sizeMattersLhs() {return true;}
};
class AstNegateD : public AstNodeUniop {
public:
    AstNegateD(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeSetDouble(); }
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
class AstRedAnd : public AstNodeUniop {
public:
    AstRedAnd(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeSetLogicBool(); }
    ASTNODE_NODE_FUNCS(RedAnd, REDAND)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opRedAnd(lhs); }
    virtual string emitVerilog() { return "%f(& %l)"; }
    virtual string emitC() { return "VL_REDAND_%nq%lq(%nw,%lw, %P, %li)"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
};
class AstRedOr : public AstNodeUniop {
public:
    AstRedOr(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeSetLogicBool(); }
    ASTNODE_NODE_FUNCS(RedOr, REDOR)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opRedOr(lhs); }
    virtual string emitVerilog() { return "%f(| %l)"; }
    virtual string emitC() { return "VL_REDOR_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
};
class AstRedXor : public AstNodeUniop {
public:
    AstRedXor(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeSetLogicBool(); }
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
class AstRedXnor : public AstNodeUniop {
    // AstRedXnors are replaced with AstRedXors in V3Const.
public:
    AstRedXnor(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeSetLogicBool(); }
    ASTNODE_NODE_FUNCS(RedXnor, REDXNOR)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opRedXnor(lhs); }
    virtual string emitVerilog() { return "%f(~^ %l)"; }
    virtual string emitC() { v3fatalSrc("REDXNOR should have became REDXOR"); return ""; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return 1+V3Number::log2b(width()); }
};

class AstLogNot : public AstNodeUniop {
public:
    AstLogNot(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeSetLogicBool(); }
    ASTNODE_NODE_FUNCS(LogNot, LOGNOT)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opLogNot(lhs); }
    virtual string emitVerilog() { return "%f(! %l)"; }
    virtual string emitC() { return "VL_LOGNOT_%nq%lq(%nw,%lw, %P, %li)"; }
    virtual string emitSimpleOperator() { return "!"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
};
class AstNot : public AstNodeUniop {
public:
    AstNot(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeFrom(lhsp); }
    ASTNODE_NODE_FUNCS(Not, NOT)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opNot(lhs); }
    virtual string emitVerilog() { return "%f(~ %l)"; }
    virtual string emitC() { return "VL_NOT_%lq(%lW, %P, %li)"; }
    virtual string emitSimpleOperator() { return "~"; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return false;}
    virtual bool sizeMattersLhs() {return true;}
};
class AstExtend : public AstNodeUniop {
    // Expand a value into a wider entity by 0 extension.  Width is implied from nodep->width()
public:
    AstExtend(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {}
    AstExtend(FileLine* fl, AstNode* lhsp, int width) : AstNodeUniop(fl, lhsp) {
	dtypeSetLogicSized(width,width,AstNumeric::UNSIGNED); }
    ASTNODE_NODE_FUNCS(Extend, EXTEND)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opAssign(lhs); }
    virtual string emitVerilog() { return "%l"; }
    virtual string emitC() { return "VL_EXTEND_%nq%lq(%nw,%lw, %P, %li)"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}  // Because the EXTEND operator self-casts
    virtual int instrCount()	const { return 0; }
};
class AstExtendS : public AstNodeUniop {
    // Expand a value into a wider entity by sign extension.  Width is implied from nodep->width()
public:
    AstExtendS(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {}
    AstExtendS(FileLine* fl, AstNode* lhsp, int width) : AstNodeUniop(fl, lhsp) {
	// Important that widthMin be correct, as opExtend requires it after V3Expand
	dtypeSetLogicSized(width,width,AstNumeric::UNSIGNED); }
    ASTNODE_NODE_FUNCS(ExtendS, EXTENDS)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) {
	out.opExtendS(lhs, lhsp()->widthMinV());
    }
    virtual string emitVerilog() { return "%l"; }
    virtual string emitC() { return "VL_EXTENDS_%nq%lq(%nw,%lw, %P, %li)"; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}  // Because the EXTEND operator self-casts
    virtual int instrCount()	const { return 0; }
    virtual bool signedFlavor() const { return true; }
};
class AstSigned : public AstNodeUniop {
    // $signed(lhs)
public:
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
class AstUnsigned : public AstNodeUniop {
    // $unsigned(lhs)
public:
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
class AstRToIS : public AstNodeUniop {
    // $rtoi(lhs)
public:
    AstRToIS(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeSetSigned32(); }
    ASTNODE_NODE_FUNCS(RToIS, RTOIS)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opRToIS(lhs); }
    virtual string emitVerilog() { return "%f$rtoi(%l)"; }
    virtual string emitC() { return "VL_RTOI_I_D(%li)"; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return false;}  // Eliminated before matters
    virtual bool sizeMattersLhs() {return false;}  // Eliminated before matters
    virtual int instrCount()	const { return instrCountDouble(); }
};
class AstRToIRoundS : public AstNodeUniop {
public:
    AstRToIRoundS(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeSetSigned32(); }
    ASTNODE_NODE_FUNCS(RToIRoundS, RTOIROUNDS)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opRToIRoundS(lhs); }
    virtual string emitVerilog() { return "%f$rtoi_rounded(%l)"; }
    virtual string emitC() { return "VL_RTOIROUND_I_D(%li)"; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return false;}  // Eliminated before matters
    virtual bool sizeMattersLhs() {return false;}  // Eliminated before matters
    virtual int instrCount()	const { return instrCountDouble(); }
};
class AstIToRD : public AstNodeUniop {
public:
    AstIToRD(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeSetDouble(); }
    ASTNODE_NODE_FUNCS(IToRD, ITORD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opIToRD(lhs); }
    virtual string emitVerilog() { return "%f$itor(%l)"; }
    virtual string emitC() { return "VL_ITOR_D_I(%li)"; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return false;}  // Eliminated before matters
    virtual bool sizeMattersLhs() {return false;}  // Eliminated before matters
    virtual int instrCount()	const { return instrCountDouble(); }
};
class AstRealToBits : public AstNodeUniop {
public:
    AstRealToBits(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeSetUInt64(); }
    ASTNODE_NODE_FUNCS(RealToBits, REALTOBITS)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opRealToBits(lhs); }
    virtual string emitVerilog() { return "%f$realtobits(%l)"; }
    virtual string emitC() { return "VL_CVT_Q_D(%li)"; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return false;}  // Eliminated before matters
    virtual bool sizeMattersLhs() {return false;}  // Eliminated before matters
    virtual int instrCount()	const { return instrCountDouble(); }
};
class AstBitsToRealD : public AstNodeUniop {
public:
    AstBitsToRealD(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeSetDouble(); }
    ASTNODE_NODE_FUNCS(BitsToRealD, BITSTOREALD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opBitsToRealD(lhs); }
    virtual string emitVerilog() { return "%f$bitstoreal(%l)"; }
    virtual string emitC() { return "VL_CVT_D_Q(%li)"; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return false;}  // Eliminated before matters
    virtual bool sizeMattersLhs() {return false;}  // Eliminated before matters
    virtual int instrCount()	const { return instrCountDouble(); }
};

class AstCLog2 : public AstNodeUniop {
public:
    AstCLog2(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(CLog2, CLOG2)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opCLog2(lhs); }
    virtual string emitVerilog() { return "%f$clog2(%l)"; }
    virtual string emitC() { return "VL_CLOG2_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*16; }
};
class AstCountOnes : public AstNodeUniop {
    // Number of bits set in vector
public:
    AstCountOnes(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(CountOnes, COUNTONES)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opCountOnes(lhs); }
    virtual string emitVerilog() { return "%f$countones(%l)"; }
    virtual string emitC() { return "VL_COUNTONES_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*16; }
};
class AstIsUnknown : public AstNodeUniop {
    // True if any unknown bits
public:
    AstIsUnknown(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeSetLogicBool(); }
    ASTNODE_NODE_FUNCS(IsUnknown, ISUNKNOWN)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opIsUnknown(lhs); }
    virtual string emitVerilog() { return "%f$isunknown(%l)"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return false;}
    virtual bool sizeMattersLhs() {return false;}
};
class AstOneHot : public AstNodeUniop {
    // True if only single bit set in vector
public:
    AstOneHot(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeSetLogicBool(); }
    ASTNODE_NODE_FUNCS(OneHot, ONEHOT)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opOneHot(lhs); }
    virtual string emitVerilog() { return "%f$onehot(%l)"; }
    virtual string emitC() { return "VL_ONEHOT_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*4; }
};
class AstOneHot0 : public AstNodeUniop {
    // True if only single bit, or no bits set in vector
public:
    AstOneHot0(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeSetLogicBool(); }
    ASTNODE_NODE_FUNCS(OneHot0, ONEHOT0)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opOneHot0(lhs); }
    virtual string emitVerilog() { return "%f$onehot0(%l)"; }
    virtual string emitC() { return "VL_ONEHOT0_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*3; }
};

class AstCast : public AstNode {
    // Cast to appropriate data type - note lhsp is value, to match AstTypedef, AstCCast, etc
public:
    AstCast(FileLine* fl, AstNode* lhsp, AstNodeDType* dtp) : AstNode(fl) {
	setOp1p(lhsp); setOp2p(dtp);
	dtypeFrom(dtp);
    }
    ASTNODE_NODE_FUNCS(Cast, CAST)
    virtual bool hasDType() const { return true; }
    virtual string emitVerilog() { return "((%d)'(%l))"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool cleanOut() { V3ERROR_NA; return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
    AstNode* lhsp() const { return op1p(); }
    AstNodeDType* getChildDTypep() const { return childDTypep(); }
    AstNodeDType* childDTypep() const { return op2p()->castNodeDType(); }
};

class AstCastParse : public AstNode {
    // Cast to appropriate type, where we haven't determined yet what the data type is
public:
    AstCastParse(FileLine* fl, AstNode* lhsp, AstNode* dtp) : AstNode(fl) {
	setOp1p(lhsp); setOp2p(dtp);
    }
    ASTNODE_NODE_FUNCS(CastParse, CASTPARSE)
    virtual string emitVerilog() { return "((%d)'(%l))"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool cleanOut() { V3ERROR_NA; return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
    AstNode* lhsp() const { return op1p(); }
    AstNode* dtp() const { return op2p(); }
};

class AstCastSize : public AstNode {
    // Cast to specific size; signed/twostate inherited from lower element per IEEE
public:
    AstCastSize(FileLine* fl, AstNode* lhsp, AstConst* rhsp) : AstNode(fl) {
	setOp1p(lhsp); setOp2p(rhsp);
    }
    ASTNODE_NODE_FUNCS(CastSize, CASTSIZE)
    // No hasDType because widthing removes this node before the hasDType check
    virtual string emitVerilog() { return "((%r)'(%l))"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool cleanOut() { V3ERROR_NA; return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
    AstNode* lhsp() const { return op1p(); }
    AstNode* rhsp() const { return op2p(); }
};

class AstCCast : public AstNodeUniop {
    // Cast to C-based data type
private:
    int		m_size;
public:
    AstCCast(FileLine* fl, AstNode* lhsp, int setwidth, int minwidth=-1) : AstNodeUniop(fl, lhsp) {
	m_size=setwidth;
	if (setwidth) {
	    if (minwidth==-1) minwidth=setwidth;
	    dtypeSetLogicSized(setwidth,minwidth,AstNumeric::UNSIGNED);
	}
    }
    AstCCast(FileLine* fl, AstNode* lhsp, AstNode* typeFromp) : AstNodeUniop(fl, lhsp) {
	dtypeFrom(typeFromp);
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

class AstCvtPackString : public AstNodeUniop {
    // Convert to Verilator Packed String (aka verilog "string")
public:
    AstCvtPackString(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeSetString(); }  // Really, width should be dtypep -> STRING
    ASTNODE_NODE_FUNCS(CvtPackString, CVTPACKSTRING)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { V3ERROR_NA; }
    virtual string emitVerilog() { return "%f$_CAST(%l)"; }
    virtual string emitC() { return "VL_CVT_PACK_STR_N%lq(%lW, %li)"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
};

class AstFEof : public AstNodeUniop {
public:
    AstFEof(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(FEof, FEOF)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { V3ERROR_NA; }
    virtual string emitVerilog() { return "%f$feof(%l)"; }
    virtual string emitC() { return "(%li ? feof(VL_CVT_I_FP(%li)) : true)"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*16; }
    virtual bool isPure() const { return false; }	// SPECIAL: $display has 'visual' ordering
    AstNode*	filep() const { return lhsp(); }
};

class AstFGetC : public AstNodeUniop {
public:
    AstFGetC(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(FGetC, FGETC)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { V3ERROR_NA; }
    virtual string emitVerilog() { return "%f$fgetc(%l)"; }
    // Non-existent filehandle returns EOF
    virtual string emitC() { return "(%li ? fgetc(VL_CVT_I_FP(%li)) : -1)"; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*64; }
    virtual bool isPure() const { return false; }	// SPECIAL: $display has 'visual' ordering
    AstNode*	filep() const { return lhsp(); }
};

class AstCeilD : public AstNodeUniop {
public:
    AstCeilD(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeSetDouble(); }
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

class AstExpD : public AstNodeUniop {
public:
    AstExpD(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeSetDouble(); }
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

class AstFloorD : public AstNodeUniop {
public:
    AstFloorD(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeSetDouble(); }
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

class AstLogD : public AstNodeUniop {
public:
    AstLogD(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeSetDouble(); }
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

class AstLog10D : public AstNodeUniop {
public:
    AstLog10D(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeSetDouble(); }
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

class AstSqrtD : public AstNodeUniop {
public:
    AstSqrtD(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	dtypeSetDouble(); }
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

class AstLogOr : public AstNodeBiop {
public:
    AstLogOr(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
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
class AstLogAnd : public AstNodeBiop {
public:
    AstLogAnd(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
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
class AstLogIf : public AstNodeBiop {
public:
    AstLogIf(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
    ASTNODE_NODE_FUNCS(LogIf, LOGIF)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLogIf(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f-> %r)"; }
    virtual string emitC() { return "VL_LOGIF_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "->"; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()+instrCountBranch(); }
};
class AstLogIff : public AstNodeBiCom {
public:
    AstLogIff(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiCom(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
    ASTNODE_NODE_FUNCS(LogIff, LOGIFF)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLogIff(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f<-> %r)"; }
    virtual string emitC() { return "VL_LOGIFF_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "<->"; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()+instrCountBranch(); }
};
class AstOr : public AstNodeBiComAsv {
public:
    AstOr(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiComAsv(fl, lhsp, rhsp) {
	dtypeFrom(lhsp); }
    ASTNODE_NODE_FUNCS(Or, OR)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opOr(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f| %r)"; }
    virtual string emitC() { return "VL_OR_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "|"; }
    virtual bool cleanOut() {V3ERROR_NA; return false;}  // Lclean && Rclean
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
class AstAnd : public AstNodeBiComAsv {
public:
    AstAnd(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiComAsv(fl, lhsp, rhsp) {
	dtypeFrom(lhsp); }
    ASTNODE_NODE_FUNCS(And, AND)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opAnd(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f& %r)"; }
    virtual string emitC() { return "VL_AND_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "&"; }
    virtual bool cleanOut() {V3ERROR_NA; return false;}  // Lclean || Rclean
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
class AstXor : public AstNodeBiComAsv {
public:
    AstXor(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiComAsv(fl, lhsp, rhsp) {
	dtypeFrom(lhsp); }
    ASTNODE_NODE_FUNCS(Xor, XOR)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opXor(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f^ %r)"; }
    virtual string emitC() { return "VL_XOR_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "^"; }
    virtual bool cleanOut() {return false;}  // Lclean && Rclean
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
class AstXnor : public AstNodeBiComAsv {
public:
    AstXnor(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiComAsv(fl, lhsp, rhsp) {
	dtypeFrom(lhsp); }
    ASTNODE_NODE_FUNCS(Xnor, XNOR)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opXnor(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f^ ~ %r)"; }
    virtual string emitC() { return "VL_XNOR_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "^ ~"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return true;}
};
class AstEq : public AstNodeBiCom {
public:
    AstEq(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiCom(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
    ASTNODE_NODE_FUNCS(Eq, EQ)
    static AstNodeBiop* newTyped(FileLine* fl, AstNode* lhsp, AstNode* rhsp);  // Return AstEq/AstEqD
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opEq(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f== %r)"; }
    virtual string emitC() { return "VL_EQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "=="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
class AstEqD : public AstNodeBiCom {
public:
    AstEqD(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiCom(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
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
class AstEqN : public AstNodeBiCom {
public:
    AstEqN(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiCom(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
    ASTNODE_NODE_FUNCS(EqN, EQN)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opEqN(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f== %r)"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual string emitSimpleOperator() { return "=="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return instrCountString(); }
    virtual bool stringFlavor() const { return true; }
};
class AstNeq : public AstNodeBiCom {
public:
    AstNeq(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiCom(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
    ASTNODE_NODE_FUNCS(Neq, NEQ)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opNeq(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f!= %r)"; }
    virtual string emitC() { return "VL_NEQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "!="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
class AstNeqD : public AstNodeBiCom {
public:
    AstNeqD(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiCom(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
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
class AstNeqN : public AstNodeBiCom {
public:
    AstNeqN(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiCom(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
    ASTNODE_NODE_FUNCS(NeqN, NEQN)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opNeqN(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f!= %r)"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual string emitSimpleOperator() { return "!="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return instrCountString(); }
    virtual bool stringFlavor() const { return true; }
};
class AstLt : public AstNodeBiop {
public:
    AstLt(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
    ASTNODE_NODE_FUNCS(Lt, LT)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLt(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f< %r)"; }
    virtual string emitC() { return "VL_LT_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "<"; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
class AstLtD : public AstNodeBiop {
public:
    AstLtD(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
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
class AstLtS : public AstNodeBiop {
public:
    AstLtS(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
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
class AstLtN : public AstNodeBiop {
public:
    AstLtN(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
    ASTNODE_NODE_FUNCS(LtN, LTN)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLtN(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f< %r)"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual string emitSimpleOperator() { return "<"; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return instrCountString(); }
    virtual bool stringFlavor() const { return true; }
};
class AstGt : public AstNodeBiop {
public:
    AstGt(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
    ASTNODE_NODE_FUNCS(Gt, GT)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opGt(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f> %r)"; }
    virtual string emitC() { return "VL_GT_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return ">"; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
class AstGtD : public AstNodeBiop {
public:
    AstGtD(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
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
class AstGtS : public AstNodeBiop {
public:
    AstGtS(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
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
class AstGtN : public AstNodeBiop {
public:
    AstGtN(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
    ASTNODE_NODE_FUNCS(GtN, GTN)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opGtN(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f> %r)"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual string emitSimpleOperator() { return ">"; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return instrCountString(); }
    virtual bool stringFlavor() const { return true; }
};
class AstGte : public AstNodeBiop {
public:
    AstGte(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
    ASTNODE_NODE_FUNCS(Gte, GTE)
    static AstNodeBiop* newTyped(FileLine* fl, AstNode* lhsp, AstNode* rhsp);  // Return AstGte/AstGteS/AstGteD
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opGte(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f>= %r)"; }
    virtual string emitC() { return "VL_GTE_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return ">="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
class AstGteD : public AstNodeBiop {
public:
    AstGteD(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
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
class AstGteS : public AstNodeBiop {
public:
    AstGteS(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
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
class AstGteN : public AstNodeBiop {
public:
    AstGteN(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
    ASTNODE_NODE_FUNCS(GteN, GTEN)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opGteN(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f>= %r)"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual string emitSimpleOperator() { return ">="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return instrCountString(); }
    virtual bool stringFlavor() const { return true; }
};
class AstLte : public AstNodeBiop {
public:
    AstLte(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
    ASTNODE_NODE_FUNCS(Lte, LTE)
    static AstNodeBiop* newTyped(FileLine* fl, AstNode* lhsp, AstNode* rhsp);  // Return AstLte/AstLteS/AstLteD
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLte(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f<= %r)"; }
    virtual string emitC() { return "VL_LTE_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "<="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
class AstLteD : public AstNodeBiop {
public:
    AstLteD(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
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
class AstLteS : public AstNodeBiop {
public:
    AstLteS(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
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
class AstLteN : public AstNodeBiop {
public:
    AstLteN(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
    ASTNODE_NODE_FUNCS(LteN, LTEN)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLteN(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f<= %r)"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual string emitSimpleOperator() { return "<="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return instrCountString(); }
    virtual bool stringFlavor() const { return true; }
};
class AstShiftL : public AstNodeBiop {
public:
    AstShiftL(FileLine* fl, AstNode* lhsp, AstNode* rhsp, int setwidth=0)
	: AstNodeBiop(fl, lhsp, rhsp) {
	if (setwidth) { dtypeSetLogicSized(setwidth,setwidth,AstNumeric::UNSIGNED); }
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
class AstShiftR : public AstNodeBiop {
public:
    AstShiftR(FileLine* fl, AstNode* lhsp, AstNode* rhsp, int setwidth=0)
	: AstNodeBiop(fl, lhsp, rhsp) {
	if (setwidth) { dtypeSetLogicSized(setwidth,setwidth,AstNumeric::UNSIGNED); }
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
class AstShiftRS : public AstNodeBiop {
    // Shift right with sign extension, >>> operator
    // Output data type's width determines which bit is used for sign extension
public:
    AstShiftRS(FileLine* fl, AstNode* lhsp, AstNode* rhsp, int setwidth=0)
	: AstNodeBiop(fl, lhsp, rhsp) {
	// Important that widthMin be correct, as opExtend requires it after V3Expand
	if (setwidth) { dtypeSetLogicSized(setwidth,setwidth,AstNumeric::SIGNED); }
    }
    ASTNODE_NODE_FUNCS(ShiftRS, SHIFTRS)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) {
	out.opShiftRS(lhs,rhs,lhsp()->widthMinV()); }
    virtual string emitVerilog() { return "%k(%l %f>>> %r)"; }
    virtual string emitC() { return "VL_SHIFTRS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return ""; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual bool signedFlavor() const { return true; }
};
class AstAdd : public AstNodeBiComAsv {
public:
    AstAdd(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiComAsv(fl, lhsp, rhsp) {
	dtypeFrom(lhsp); }
    ASTNODE_NODE_FUNCS(Add, ADD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opAdd(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f+ %r)"; }
    virtual string emitC() { return "VL_ADD_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "+"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return true;}
};
class AstAddD : public AstNodeBiComAsv {
public:
    AstAddD(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiComAsv(fl, lhsp, rhsp) {
	dtypeSetDouble(); }
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
class AstSub : public AstNodeBiop {
public:
    AstSub(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeFrom(lhsp); }
    ASTNODE_NODE_FUNCS(Sub, SUB)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opSub(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f- %r)"; }
    virtual string emitC() { return "VL_SUB_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "-"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return true;}
};
class AstSubD : public AstNodeBiop {
public:
    AstSubD(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeSetDouble(); }
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
class AstMul : public AstNodeBiComAsv {
public:
    AstMul(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiComAsv(fl, lhsp, rhsp) {
	dtypeFrom(lhsp); }
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
class AstMulD : public AstNodeBiComAsv {
public:
    AstMulD(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiComAsv(fl, lhsp, rhsp) {
	dtypeSetDouble(); }
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
class AstMulS : public AstNodeBiComAsv {
public:
    AstMulS(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiComAsv(fl, lhsp, rhsp) {
	dtypeFrom(lhsp); }
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
class AstDiv : public AstNodeBiop {
public:
    AstDiv(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeFrom(lhsp); }
    ASTNODE_NODE_FUNCS(Div, DIV)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opDiv(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f/ %r)"; }
    virtual string emitC() { return "VL_DIV_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return true;}
    virtual int instrCount()	const { return widthInstrs()*instrCountDiv(); }
};
class AstDivD : public AstNodeBiop {
public:
    AstDivD(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeSetDouble(); }
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
class AstDivS : public AstNodeBiop {
public:
    AstDivS(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeFrom(lhsp); }
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
class AstModDiv : public AstNodeBiop {
public:
    AstModDiv(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeFrom(lhsp); }
    ASTNODE_NODE_FUNCS(ModDiv, MODDIV)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opModDiv(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f%% %r)"; }
    virtual string emitC() { return "VL_MODDIV_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return true;}
    virtual int instrCount()	const { return widthInstrs()*instrCountDiv(); }
};
class AstModDivS : public AstNodeBiop {
public:
    AstModDivS(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeFrom(lhsp); }
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
class AstPow : public AstNodeBiop {
public:
    AstPow(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeFrom(lhsp); }
    ASTNODE_NODE_FUNCS(Pow, POW)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opPow(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f** %r)"; }
    virtual string emitC() { return "VL_POW_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*instrCountMul()*10; }
};
class AstPowD : public AstNodeBiop {
public:
    AstPowD(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeSetDouble(); }
    ASTNODE_NODE_FUNCS(PowD, POWD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opPowD(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f** %r)"; }
    virtual string emitC() { return "pow(%li,%ri)"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return instrCountDoubleDiv()*5; }
    virtual bool doubleFlavor() const { return true; }
};
class AstPowSU : public AstNodeBiop {
public:
    AstPowSU(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeFrom(lhsp); }
    ASTNODE_NODE_FUNCS(PowSU, POWSU)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opPowSU(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f** %r)"; }
    virtual string emitC() { return "VL_POWSS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri, 1,0)"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*instrCountMul()*10; }
    virtual bool signedFlavor() const { return true; }
};
class AstPowSS : public AstNodeBiop {
public:
    AstPowSS(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeFrom(lhsp); }
    ASTNODE_NODE_FUNCS(PowSS, POWSS)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opPowSS(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f** %r)"; }
    virtual string emitC() { return "VL_POWSS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri, 1,1)"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*instrCountMul()*10; }
    virtual bool signedFlavor() const { return true; }
};
class AstPowUS : public AstNodeBiop {
public:
    AstPowUS(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeFrom(lhsp); }
    ASTNODE_NODE_FUNCS(PowUS, POWUS)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opPowUS(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f** %r)"; }
    virtual string emitC() { return "VL_POWSS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri, 0,1)"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*instrCountMul()*10; }
    virtual bool signedFlavor() const { return true; }
};
class AstEqCase : public AstNodeBiCom {
public:
    AstEqCase(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiCom(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
    ASTNODE_NODE_FUNCS(EqCase, EQCASE)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opCaseEq(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f=== %r)"; }
    virtual string emitC() { return "VL_EQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "=="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
class AstNeqCase : public AstNodeBiCom {
public:
    AstNeqCase(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiCom(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
    ASTNODE_NODE_FUNCS(NeqCase, NEQCASE)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opCaseNeq(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f!== %r)"; }
    virtual string emitC() { return "VL_NEQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "!="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
class AstEqWild : public AstNodeBiop {
    // Note wildcard operator rhs differs from lhs
public:
    AstEqWild(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
    ASTNODE_NODE_FUNCS(EqWild, EQWILD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opWildEq(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f==? %r)"; }
    virtual string emitC() { return "VL_EQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "=="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
class AstNeqWild : public AstNodeBiop {
public:
    AstNeqWild(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeSetLogicBool(); }
    ASTNODE_NODE_FUNCS(NeqWild, NEQWILD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opWildNeq(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %f!=? %r)"; }
    virtual string emitC() { return "VL_NEQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "!="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
class AstConcat : public AstNodeBiop {
    // If you're looking for {#{}}, see AstReplicate
public:
    AstConcat(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	if (lhsp->dtypep() && rhsp->dtypep()) {
	    dtypeSetLogicSized(lhsp->dtypep()->width()+rhsp->dtypep()->width(),
			       lhsp->dtypep()->width()+rhsp->dtypep()->width(),
			       AstNumeric::UNSIGNED);
	}
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
class AstConcatN : public AstNodeBiop {
    // String concatenate
public:
    AstConcatN(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeSetString();
    }
    ASTNODE_NODE_FUNCS(ConcatN, CONCATN)
    virtual string emitVerilog() { return "%f{%l, %k%r}"; }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opConcatN(lhs,rhs); }
    virtual string emitC() { return "VL_CONCATN_NNN(%li, %ri)"; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return instrCountString(); }
    virtual bool stringFlavor() const { return true; }
};
class AstReplicate : public AstNodeBiop {
    // Also used as a "Uniop" flavor of Concat, e.g. "{a}"
    // Verilog {rhs{lhs}} - Note rhsp() is the replicate value, not the lhsp()
private:
    void init() {
	if (lhsp()) {
	    if (AstConst* constp=rhsp()->castConst()) {
		dtypeSetLogicSized(lhsp()->width()*constp->toUInt(), lhsp()->width()*constp->toUInt(), AstNumeric::UNSIGNED);
	    }
	}
    }
public:
    AstReplicate(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : AstNodeBiop(fl, lhsp, rhsp) { init(); }
    AstReplicate(FileLine* fl, AstNode* lhsp, uint32_t repCount)
	: AstNodeBiop(fl, lhsp, new AstConst(fl, repCount)) { init(); }
    ASTNODE_NODE_FUNCS(Replicate, REPLICATE)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opRepl(lhs,rhs); }
    virtual string emitVerilog() { return "%f{%r{%k%l}}"; }
    virtual string emitC() { return "VL_REPLICATE_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*2; }
};
class AstReplicateN : public AstNodeBiop {
    // String replicate
private:
    void init() { dtypeSetString(); }
public:
    AstReplicateN(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : AstNodeBiop(fl, lhsp, rhsp) { init(); }
    AstReplicateN(FileLine* fl, AstNode* lhsp, uint32_t repCount)
	: AstNodeBiop(fl, lhsp, new AstConst(fl, repCount)) { init(); }
    ASTNODE_NODE_FUNCS(ReplicateN, REPLICATEN)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opReplN(lhs,rhs); }
    virtual string emitVerilog() { return "%f{%r{%k%l}}"; }
    virtual string emitC() { return "VL_REPLICATEN_NN%rq(0,0,%rw, %li, %ri)"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*2; }
    virtual bool stringFlavor() const { return true; }
};
class AstStreamL : public AstNodeStream {
    // Verilog {rhs{lhs}} - Note rhsp() is the slice size, not the lhsp()
public:
    AstStreamL(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeStream(fl, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(StreamL, STREAML)
    virtual string emitVerilog() { return "%f{ << %r %k{%l} }"; }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opStreamL(lhs,rhs); }
    virtual string emitC() { return "VL_STREAML_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*2; }
};
class AstStreamR : public AstNodeStream {
    // Verilog {rhs{lhs}} - Note rhsp() is the slice size, not the lhsp()
public:
    AstStreamR(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeStream(fl, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(StreamR, STREAMR)
    virtual string emitVerilog() { return "%f{ >> %r %k{%l} }"; }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opAssign(lhs); }
    virtual string emitC() { return isWide() ? "VL_ASSIGN_W(%nw, %P, %li)" : "%li"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*2; }
};
class AstBufIf1 : public AstNodeBiop {
    // lhs is enable, rhs is data to drive
    // Note unlike the Verilog bufif1() UDP, this allows any width; each lhsp bit enables respective rhsp bit
public:
    AstBufIf1(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	dtypeFrom(lhsp); }
    ASTNODE_NODE_FUNCS(BufIf1, BUFIF1)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opBufIf1(lhs,rhs); }
    virtual string emitVerilog() { return "bufif(%r,%l)"; }
    virtual string emitC() { V3ERROR_NA; return "";}  // Lclean || Rclean
    virtual string emitSimpleOperator() { V3ERROR_NA; return "";}  // Lclean || Rclean
    virtual bool cleanOut() {V3ERROR_NA; return "";}  // Lclean || Rclean
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
class AstFGetS : public AstNodeBiop {
public:
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

class AstPattern : public AstNodeMath {
    // Verilog '{a,b,c,d...}
    // Parents: AstNodeAssign, AstPattern, ...
    // Children: expression, AstPattern, AstPatReplicate
public:
    AstPattern(FileLine* fl, AstNode* itemsp) : AstNodeMath(fl) {
	addNOp2p(itemsp);
    }
    ASTNODE_NODE_FUNCS(Pattern, PATTERN)
    virtual string emitVerilog() { V3ERROR_NA; return ""; }  // Implemented specially
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { V3ERROR_NA; }
    virtual string emitC() { V3ERROR_NA; return "";}
    virtual string emitSimpleOperator() { V3ERROR_NA; return "";}
    virtual bool cleanOut() {V3ERROR_NA; return "";}
    virtual int instrCount()	const { return widthInstrs(); }
    AstNodeDType* getChildDTypep() const { return childDTypep(); }
    AstNodeDType* childDTypep() const { return op1p()->castNodeDType(); } // op1 = Type assigning to
    void childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    AstNodeDType* subDTypep() const { return dtypep() ? dtypep() : childDTypep(); }
    AstNode* itemsp() const { return op2p(); } // op2 = AstPatReplicate, AstPatMember, etc
};
class AstPatMember : public AstNodeMath {
    // Verilog '{a} or '{a{b}}
    // Parents: AstPattern
    // Children: expression, AstPattern, replication count
private:
    bool	m_default;
public:
    AstPatMember(FileLine* fl, AstNode* lhsp, AstNode* keyp, AstNode* repp) : AstNodeMath(fl) {
	addOp1p(lhsp), setNOp2p(keyp), setNOp3p(repp); m_default = false; }
    ASTNODE_NODE_FUNCS(PatMember, PATMEMBER)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { V3ERROR_NA; }
    virtual string emitVerilog() { return lhssp()?"%f{%r{%k%l}}":"%l"; }
    virtual string emitC() { V3ERROR_NA; return "";}
    virtual string emitSimpleOperator() { V3ERROR_NA; return "";}
    virtual bool cleanOut() {V3ERROR_NA; return "";}
    virtual int instrCount()	const { return widthInstrs()*2; }
    AstNode* lhssp() const { return op1p(); } // op1 = expression to assign or another AstPattern (list if replicated)
    AstNode* keyp() const { return op2p(); } // op2 = assignment key (Const, id Text)
    AstNode* repp() const { return op3p(); } // op3 = replication count, or NULL for count 1
    bool isDefault() const { return m_default; }
    void isDefault(bool flag) { m_default = flag; }
};

//======================================================================
// SysVerilog assertions

class AstVAssert : public AstNodeStmt {
    // Verilog Assertion
    // Parents:  {statement list}
    // Children: expression, if pass statements, if fail statements
public:
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

class AstClocking : public AstNode {
    // Set default clock region
    // Parents:  MODULE
    // Children: Assertions
public:
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

class AstPslClocked : public AstNode {
    // A clocked property
    // Parents:  ASSERT|COVER (property)
    // Children: SENITEM, Properties
public:
    AstPslClocked(FileLine* fl, AstNodeSenItem* sensesp, AstNode* disablep, AstNode* propp)
	: AstNode(fl) {
	addNOp1p(sensesp);
	addNOp2p(disablep);
	addOp3p(propp);
    }
    ASTNODE_NODE_FUNCS(PslClocked, PSLCLOCKED)
    virtual bool hasDType() const { return true; }  // Used under PslCover, which expects a bool child
    AstNodeSenItem* sensesp() 	const { return op1p()->castNodeSenItem(); }	// op1 = Sensitivity list
    AstNode*	disablep()	const { return op2p(); }	// op2 = disable
    AstNode*	propp()		const { return op3p(); }	// op3 = property
};

class AstPslCover : public AstNodeStmt {
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
// Text based nodes

class AstText : public AstNodeText {
private:
    bool	m_tracking;	// When emit, it's ok to parse the string to do indentation
public:
    AstText(FileLine* fl, const string& textp, bool tracking=false)
	: AstNodeText(fl, textp), m_tracking(tracking) {}
    ASTNODE_NODE_FUNCS(Text, TEXT)
    void tracking(bool flag) { m_tracking = flag; }
    bool tracking() const { return m_tracking; }
};

class AstScCtor : public AstNodeText {
public:
    AstScCtor(FileLine* fl, const string& textp)
	: AstNodeText(fl, textp) {}
    ASTNODE_NODE_FUNCS(ScCtor, SCCTOR)
    virtual bool isPure() const { return false; }	// SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const { return true; }
};

class AstScDtor : public AstNodeText {
public:
    AstScDtor(FileLine* fl, const string& textp)
	: AstNodeText(fl, textp) {}
    ASTNODE_NODE_FUNCS(ScDtor, SCDTOR)
    virtual bool isPure() const { return false; }	// SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const { return true; }
};

class AstScHdr : public AstNodeText {
public:
    AstScHdr(FileLine* fl, const string& textp)
	: AstNodeText(fl, textp) {}
    ASTNODE_NODE_FUNCS(ScHdr, SCHDR)
    virtual bool isPure() const { return false; }	// SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const { return true; }
};

class AstScImp : public AstNodeText {
public:
    AstScImp(FileLine* fl, const string& textp)
	: AstNodeText(fl, textp) {}
    ASTNODE_NODE_FUNCS(ScImp, SCIMP)
    virtual bool isPure() const { return false; }	// SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const { return true; }
};

class AstScImpHdr : public AstNodeText {
public:
    AstScImpHdr(FileLine* fl, const string& textp)
	: AstNodeText(fl, textp) {}
    ASTNODE_NODE_FUNCS(ScImpHdr, SCIMPHDR)
    virtual bool isPure() const { return false; }	// SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const { return true; }
};

class AstScInt : public AstNodeText {
public:
    AstScInt(FileLine* fl, const string& textp)
	: AstNodeText(fl, textp) {}
    ASTNODE_NODE_FUNCS(ScInt, SCINT)
    virtual bool isPure() const { return false; }	// SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const { return true; }
};

class AstUCStmt : public AstNodeStmt {
    // User $c statement
public:
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

class AstCFile : public AstNode {
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

class AstCFunc : public AstNode {
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
    bool	m_isInline:1;		// Inline function
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
	m_isInline = false;
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
    virtual const char* broken() const { BROKEN_RTN((m_scopep && !m_scopep->brokeExists())); return NULL; }
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
    bool	dontInline() const { return dontCombine() || slow() || skipDecl() || funcPublic(); }
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
    bool	isInline() const { return m_isInline; }
    void	isInline(bool flag) { m_isInline = flag; }
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

class AstCCall : public AstNodeStmt {
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
    virtual const char* broken() const { BROKEN_RTN(m_funcp && !m_funcp->brokeExists()); return NULL; }
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

class AstCReturn : public AstNodeStmt {
    // C++ return from a function
    // Parents:  CFUNC/statement
    // Children: Math
public:
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

class AstCMath : public AstNodeMath {
private:
    bool	m_cleanOut;
public:
    // Emit C textual math function (like AstUCFunc)
    AstCMath(FileLine* fl, AstNode* exprsp)
	: AstNodeMath(fl), m_cleanOut(true) {
	addOp1p(exprsp);
	dtypeFrom(exprsp);
    }
    AstCMath(FileLine* fl, const string& textStmt, int setwidth, bool cleanOut=true)
	: AstNodeMath(fl), m_cleanOut(cleanOut) {
	addNOp1p(new AstText(fl, textStmt, true));
	if (setwidth) { dtypeSetLogicSized(setwidth,setwidth,AstNumeric::UNSIGNED); }
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


class AstCStmt : public AstNodeStmt {
    // Emit C statement
public:
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
// Right below top

class AstTypeTable : public AstNode {
    // Container for hash of standard data types
    // Children:  NODEDTYPEs
    typedef map<pair<int,int>,AstBasicDType*> LogicMap;
    AstBasicDType* m_basicps[AstBasicDTypeKwd::_ENUM_MAX];
    //
    enum { IDX0_LOGIC, IDX0_BIT, _IDX0_MAX };
    LogicMap m_logicMap[_IDX0_MAX][AstNumeric::_ENUM_MAX];  // uses above IDX enums
    //
    typedef map<VBasicTypeKey,AstBasicDType*> DetailedMap;
    DetailedMap m_detailedMap;
public:
    AstTypeTable(FileLine* fl) : AstNode(fl) {
	for (int i=0; i<AstBasicDTypeKwd::_ENUM_MAX; ++i) m_basicps[i] = NULL;
    }
    ASTNODE_NODE_FUNCS(TypeTable, TYPETABLE)
    AstNodeDType*     typesp() 	const { return op1p()->castNodeDType();}	// op1 = List of dtypes
    void addTypesp(AstNodeDType* nodep) { addOp1p(nodep); }
    AstBasicDType* findBasicDType(FileLine* fl, AstBasicDTypeKwd kwd);
    AstBasicDType* findLogicBitDType(FileLine* fl, AstBasicDTypeKwd kwd,
				     int width, int widthMin, AstNumeric numeric);
    AstBasicDType* findLogicBitDType(FileLine* fl, AstBasicDTypeKwd kwd,
				     VNumRange range, int widthMin, AstNumeric numeric);
    AstBasicDType* findInsertSameDType(AstBasicDType* nodep);
    void clearCache();
    void repairCache();
    virtual void dump(ostream& str=cout);
};

//######################################################################
// Top

class AstNetlist : public AstNode {
    // All modules are under this single top node.
    // Parents:   none
    // Children:  MODULEs & CFILEs
private:
    AstTypeTable* m_typeTablep;	// Reference to top type table, for faster lookup
    AstPackage*	  m_dollarUnitPkgp;
public:
    AstNetlist() : AstNode(new FileLine("AstRoot",0)) {
	m_typeTablep = NULL;
	m_dollarUnitPkgp = NULL;
    }
    ASTNODE_NODE_FUNCS(Netlist, NETLIST)
    virtual const char* broken() const { BROKEN_RTN(m_dollarUnitPkgp && !m_dollarUnitPkgp->brokeExists()); return NULL; }
    AstNodeModule*	modulesp() 	const { return op1p()->castNodeModule();}	// op1 = List of modules
    AstNodeModule*  topModulep() const { return op1p()->castNodeModule(); }	// * = Top module in hierarchy (first one added, for now)
    void addModulep(AstNodeModule* modulep) { addOp1p(modulep); }
    AstCFile*	filesp() 	const { return op2p()->castCFile();}	// op2 = List of files
    void addFilesp(AstCFile* filep) { addOp2p(filep); }
    AstNode*	miscsp() 	const { return op3p();}	// op3 = List of dtypes etc
    void addMiscsp(AstNode* nodep) { addOp3p(nodep); }
    AstTypeTable* typeTablep() { return m_typeTablep; }
    void addTypeTablep(AstTypeTable* nodep) { m_typeTablep = nodep; addMiscsp(nodep); }
    AstPackage* dollarUnitPkgp() const { return m_dollarUnitPkgp; }
    AstPackage* dollarUnitPkgAddp() {
	if (!m_dollarUnitPkgp) {
	    m_dollarUnitPkgp = new AstPackage(fileline(), AstPackage::dollarUnitName());
	    m_dollarUnitPkgp->inLibrary(true);  // packages are always libraries; don't want to make them a "top"
	    m_dollarUnitPkgp->modTrace(false);  // may reconsider later
	    m_dollarUnitPkgp->internal(true);
	    addModulep(m_dollarUnitPkgp);
	}
	return m_dollarUnitPkgp; }
};

//######################################################################

#endif // Guard
