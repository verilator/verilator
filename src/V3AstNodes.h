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
// Copyright 2003-2008 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
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
	width(m_num.width(), m_num.sized()?0:m_num.minWidth());
	isSigned(m_num.isSigned());
    }
    AstConst(FileLine* fl, uint32_t num)
	:AstNodeMath(fl)
	,m_num(V3Number(fl,32,num)) { width(m_num.width(), m_num.sized()?0:m_num.minWidth()); }
    virtual ~AstConst() {}
    virtual AstType type() const { return AstType::CONST;}
    virtual AstNode* clone() { return new AstConst(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual string name()	const { return num().ascii(); }		// * = Value
    virtual const V3Number& num()	const { return m_num; }		// * = Value
    uint32_t asInt()  const { return num().asInt(); }
    vluint64_t asQuad() const { return num().asQuad(); }
    virtual string emitVerilog() { V3ERROR_NA; return ""; }  // Implemented specially
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool cleanOut() { return true; }
    virtual V3Hash sameHash() const { return V3Hash(num().asHash()); }
    virtual bool same(AstNode* samep) const {
	return num().isCaseEq(samep->castConst()->num()); }
    virtual int instrCount() const { return widthInstrs(); }
};

struct AstRange : public AstNode {
    // Range specification, for use under variables and cells
    AstRange(FileLine* fl, AstNode* msbp, AstNode* lsbp)
	:AstNode(fl) {
	setOp2p(msbp); setOp3p(lsbp); }
    AstRange(FileLine* fl, int msb, int lsb)
	:AstNode(fl) {
	setOp2p(new AstConst(fl,msb)); setOp3p(new AstConst(fl,lsb));
	width(msb-lsb+1,msb-lsb+1);
    }
    virtual ~AstRange() {}
    virtual AstType type() const { return AstType::RANGE;}
    virtual AstNode* clone() { return new AstRange(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    AstRange*	cloneTree(bool cloneNextLink) { return AstNode::cloneTree(cloneNextLink)->castRange(); }
    AstNode* msbp()		const { return op2p()->castNode(); }	// op2 = Msb expression
    AstNode* lsbp()		const { return op3p()->castNode(); }	// op3 = Lsb expression
    int	     msbConst()	const { AstConst* constp=msbp()->castConst(); return (constp?constp->asInt():0); }
    int	     lsbConst()	const { AstConst* constp=lsbp()->castConst(); return (constp?constp->asInt():0); }
    int	     elementsConst() const { return msbConst()-lsbConst()+1; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
};

struct AstArraySel : public AstNodeSel {
    // Parents: math|stmt
    // Children: varref|arraysel, math
    AstArraySel(FileLine* fl, AstNode* fromp, AstNode* bitp)
	:AstNodeSel(fl, fromp, bitp) {
	if (fromp) widthSignedFrom(fromp);
    }
    virtual ~AstArraySel() {}
    virtual AstType type() const { return AstType::ARRAYSEL;}
    virtual AstNode* clone() { return new AstArraySel(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) {
	V3ERROR_NA; /* How can from be a const? */ }
    virtual string emitVerilog() { return "%k(%l%k[%r])"; }
    virtual string emitC() { return "%li%k[%ri]"; }
    virtual bool cleanOut() { return true; }
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
    virtual int instrCount() const { return widthInstrs(); }
    // Special operators
    static int dimension(AstNode* nodep) {	///< How many dimensions is this reference from the base variable?
	int dim = 0;
	while (nodep && nodep->castArraySel()) { dim++; nodep=nodep->castArraySel()->fromp(); }
	return dim;
    }
    static AstNode* baseFromp(AstNode* nodep) {	///< What is the base variable (or const) this dereferences?
	while (nodep && nodep->castArraySel()) { nodep=nodep->castArraySel()->fromp(); }
	return nodep;
    }
};

struct AstWordSel : public AstNodeSel {
    // Select a single word from a multi-word wide value
    AstWordSel(FileLine* fl, AstNode* fromp, AstNode* bitp)
	:AstNodeSel(fl, fromp, bitp) {
	width(VL_WORDSIZE,VL_WORDSIZE); // Always used on, and returns word entities
    }
    virtual ~AstWordSel() {}
    virtual AstType type() const { return AstType::WORDSEL;}
    virtual AstNode* clone() { return new AstWordSel(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& from, const V3Number& bit) { V3ERROR_NA; }
    virtual string emitVerilog() { return "%k(%l[%r])"; } // Not %k, as usually it's a small constant rhsp
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
    virtual ~AstSelExtract() {}
    virtual AstType type() const { return AstType::SELEXTRACT;}
    virtual AstNode* clone() { return new AstSelExtract(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
};

struct AstSelBit : public AstNodePreSel {
    // Single bit range extraction, perhaps with non-constant selection or array selection
    // Gets replaced during link with AstArraySel or AstSel
    AstSelBit(FileLine* fl, AstNode* fromp, AstNode* bitp)
	:AstNodePreSel(fl, fromp, bitp, NULL) {
	width(1,1);
    }
    virtual ~AstSelBit() {}
    virtual AstType type() const { return AstType::SELBIT;}
    virtual AstNode* clone() { return new AstSelBit(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
};

struct AstSelPlus : public AstNodePreSel {
    // +: range extraction, perhaps with non-constant selection
    // Gets replaced during link with AstSel
    AstSelPlus(FileLine* fl, AstNode* fromp, AstNode* bitp, AstNode* widthp)
	:AstNodePreSel(fl, fromp, bitp, widthp) {}
    virtual ~AstSelPlus() {}
    virtual AstType type() const { return AstType::SELPLUS;}
    virtual AstNode* clone() { return new AstSelPlus(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
};

struct AstSelMinus : public AstNodePreSel {
    // -: range extraction, perhaps with non-constant selection
    // Gets replaced during link with AstSel
    AstSelMinus(FileLine* fl, AstNode* fromp, AstNode* bitp, AstNode* widthp)
	:AstNodePreSel(fl, fromp, bitp, widthp) {}
    virtual ~AstSelMinus() {}
    virtual AstType type() const { return AstType::SELMINUS;}
    virtual AstNode* clone() { return new AstSelMinus(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
};

struct AstSel : public AstNodeTriop {
    // Multiple bit range extraction
    // Parents: math|stmt
    // Children: varref|arraysel, math, constant math
    AstSel(FileLine* fl, AstNode* fromp, AstNode* lsbp, AstNode* widthp)
	:AstNodeTriop(fl, fromp, lsbp, widthp) {
	if (widthp->castConst()) width(widthp->castConst()->asInt(), widthp->castConst()->asInt());
    }
    AstSel(FileLine* fl, AstNode* fromp, int lsbp, int bitwidth)
	:AstNodeTriop(fl, fromp,
		      new AstConst(fl,lsbp), new AstConst(fl,bitwidth)) {
	width(bitwidth,bitwidth);
    }
    virtual ~AstSel() {}
    virtual AstType type() const { return AstType::SEL;}
    virtual AstNode* clone() { return new AstSel(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& from, const V3Number& bit, const V3Number& width) {
	out.opRange(from, bit.asInt()+width.asInt()-1, bit.asInt()); }
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
    uint32_t	lsbConst()   const { return lsbp()->castConst()->asInt(); }
    uint32_t	widthConst() const { return widthp()->castConst()->asInt(); }
    uint32_t	msbConst()   const { return lsbConst()+widthConst()-1; }
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
    bool	m_sigPublic:1;	// User C code accesses this signal
    bool	m_sigModPublic:1;// User C code accesses this signal and module
    bool	m_usedClock:1;	// Signal used as a clock
    bool	m_usedParam:1;	// Parameter is referenced (on link; later signals not setup)
    bool	m_funcLocal:1;	// Local variable for a function
    bool	m_funcReturn:1;	// Return variable for a function
    bool	m_attrClockEn:1;// User clock enable attribute
    bool	m_attrIsolateAssign:1;// User isolate_assignments attribute
    bool	m_fileDescr:1;	// File descriptor
    bool	m_isConst:1;	// Table contains constant data
    bool	m_isStatic:1;	// Static variable
    bool	m_trace:1;	// Trace this variable

    void	init() {
	m_input=false; m_output=false; m_tristate=false;
	m_primaryIO=false;
	m_sc=false; m_scClocked=false; m_scSensitive=false;
	m_usedClock=false; m_usedParam=false;
	m_sigPublic=false; m_sigModPublic=false;
	m_funcLocal=false; m_funcReturn=false;
	m_attrClockEn=false; m_attrIsolateAssign=false;
	m_fileDescr=false; m_isConst=false; m_isStatic=false;
	m_trace=false;
    }
public:
    AstVar(FileLine* fl, AstVarType type, const string& name)
	:AstNode(fl)
	, m_name(name) {
	init();
	combineType(type);
	width(msb()-lsb()+1,0);
    }
    AstVar(FileLine* fl, AstVarType type, const string& name, AstRange* rangep, AstRange* arrayp=NULL)
	:AstNode(fl)
	, m_name(name) {
	init();
	combineType(type); setNOp1p(rangep); addNOp2p(arrayp);
	width(msb()-lsb()+1,0);
    }
    AstVar(FileLine* fl, AstVarType type, const string& name, AstVar* examplep)
	:AstNode(fl)
	, m_name(name) {
	init();
	combineType(type);
	if (examplep->rangep()) {
	    setOp1p(new AstRange(fl, examplep->msb(), examplep->lsb()));
	}
	width(msb()-lsb()+1,0);
    }
    virtual ~AstVar() {}
    virtual AstType type() const { return AstType::VAR;}
    virtual AstNode* clone() { return new AstVar(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void dump(ostream& str);
    virtual string name()	const { return m_name; }		// * = Var name
    virtual bool maybePointedTo() const { return true; }
    AstVarType	varType()	const { return m_varType; }		// * = Type of variable
    string	cType()		const;	// Return C type for declaration: bool, uint32_t, uint64_t, etc.
    string	scType()	const;	// Return SysC type: bool, uint32_t, uint64_t, sc_bv
    void	combineType(AstVarType type);
    AstRange*	rangep() 	const { return op1p()->castRange(); }	// op1 = Range of variable
    AstRange*	arraysp() 	const { return op2p()->castRange(); }	// op2 = Array(s) of variable
    AstRange*	arrayp(int dim)	const;					// op2 = Range for specific dimension #
    AstNode* 	initp()		const { return op3p()->castNode(); }	// op3 = Initial value that never changes (static const)
    void	initp(AstNode* nodep) { setOp3p(nodep); }
    bool	hasSimpleInit()	const { return (op3p() && !op3p()->castInitArray()); }
    void	rangep(AstRange* nodep) { setOp1p(nodep); }
    void	attrClockEn(bool flag) { m_attrClockEn = flag; }
    void	attrFileDescr(bool flag) { m_fileDescr = flag; }
    void	attrScClocked(bool flag) { m_scClocked = flag; }
    void	attrIsolateAssign(bool flag) { m_attrIsolateAssign = flag; }
    void	usedClock(bool flag) { m_usedClock = flag; }
    void	usedParam(bool flag) { m_usedParam = flag; }
    void	sigPublic(bool flag) { m_sigPublic = flag; }
    void	sigModPublic(bool flag) { m_sigModPublic = flag; }
    void	sc(bool flag) { m_sc = flag; }
    void	scSensitive(bool flag) { m_scSensitive = flag; }
    void	primaryIO(bool flag) { m_primaryIO = flag; }
    void	isConst(bool flag) { m_isConst = flag; }
    void	isStatic(bool flag) { m_isStatic = flag; }
    void	funcLocal(bool flag) { m_funcLocal = flag; }
    void	funcReturn(bool flag) { m_funcReturn = flag; }
    void	trace(bool flag) { m_trace=flag; }
    // METHODS
    void 	name(const string& name) 	{ m_name = name; }
    bool	isInput() const { return m_input; }
    bool	isOutput() const { return m_output; }
    bool	isInOnly() const { return m_input && !m_output; }
    bool	isOutOnly() const { return m_output && !m_input; }
    bool	isInout() const { return m_input && m_output; }
    bool	isTristate() const  { return m_tristate; }
    bool	isPrimaryIO() const { return m_primaryIO; }
    bool	isPrimaryIn() const { return isPrimaryIO() && isInput(); }
    bool	isIO() const  { return (m_input||m_output); }
    bool	isSignal() const  { return (varType()==AstVarType::WIRE || varType()==AstVarType::IMPLICIT
					    || varType()==AstVarType::REG || varType()==AstVarType::INTEGER); }
    bool	isTemp() const { return (varType()==AstVarType::BLOCKTEMP || varType()==AstVarType::MODULETEMP
					 || varType()==AstVarType::STMTTEMP); }
    bool	isStatementTemp() const { return (varType()==AstVarType::STMTTEMP); }
    bool	isMovableToBlock() const { return (varType()==AstVarType::BLOCKTEMP || isFuncLocal()); }
    bool	isParam() const { return (varType()==AstVarType::LPARAM || varType()==AstVarType::GPARAM); }
    bool	isGParam() const { return (varType()==AstVarType::GPARAM); }
    bool	isGenVar() const { return (varType()==AstVarType::GENVAR); }
    bool	isInteger() const { return (varType() == AstVarType::INTEGER); }
    bool	isUsedClock() const { return m_usedClock; }
    bool	isUsedParam() const { return m_usedParam; }
    bool	isSc() const { return m_sc; }
    bool	isScQuad() const;
    bool	isScWide() const;
    bool	isScSensitive() const { return m_scSensitive; }
    bool	isSigPublic()  const;
    bool	isSigModPublic() const { return m_sigModPublic; }
    bool	isTrace() const { return m_trace; }
    bool	isConst() const { return m_isConst; }
    bool	isStatic() const { return m_isStatic; }
    bool	isFuncLocal() const { return m_funcLocal; }
    bool	isFuncReturn() const { return m_funcReturn; }
    bool	attrClockEn() const { return m_attrClockEn; }
    bool	attrFileDescr() const { return m_fileDescr; }
    bool	attrScClocked() const { return m_scClocked; }
    bool	attrIsolateAssign() const { return m_attrIsolateAssign; }
    int		widthAlignBytes() const;	// Structure alignment 1,2,4 or 8 bytes (arrays affect this)
    int		widthTotalBytes() const;	// Width in bytes rounding up 1,2,4,8,12,...
    uint32_t	msb() const { if (!rangep()) return 0; return rangep()->msbConst(); }
    uint32_t	lsb() const { if (!rangep()) return 0; return rangep()->lsbConst(); }
    uint32_t	arrayElements() const;	// 1, or total multiplication of all dimensions
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
    virtual ~AstDefParam() {}
    virtual AstType type() const { return AstType::DEFPARAM;}
    virtual string name()	const { return m_name; }		// * = Scope name
    virtual AstNode* clone() { return new AstDefParam(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual bool cleanRhs() { return true; }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode*) const { return true; }
    AstNode* rhsp()		const { return op1p()->castNode(); }	// op1 = Assign from
    string   path()		const { return m_path; }
};

struct AstScope : public AstNode {
    // A particular usage of a cell
    // Parents: MODULE
    // Children: NODEBLOCK
private:
    string	m_name;		// Name
    AstScope*	m_aboveScopep;	// Scope above this one in the hierarchy (NULL if top)
    AstCell*	m_aboveCellp;	// Cell above this in the hierarchy (NULL if top)
    AstModule*	m_modp;		// Module scope corresponds to
public:
    AstScope(FileLine* fl, AstModule* modp, const string& name,
	     AstScope* aboveScopep, AstCell* aboveCellp)
	:AstNode(fl)
	,m_name(name) ,m_aboveScopep(aboveScopep) ,m_aboveCellp(aboveCellp), m_modp(modp) {}
    virtual ~AstScope() {}
    virtual AstType type() const { return AstType::SCOPE;}
    virtual AstNode* clone() { return new AstScope(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void cloneRelink();
    virtual bool broken() const;
    virtual bool maybePointedTo() const { return true; }
    virtual string name()	const { return m_name; }		// * = Scope name
    void name(const string& name) 	{ m_name = name; }
    string nameDotless() const;
    string nameVlSym() const { return (((string)"vlSymsp->") + nameDotless()); }
    AstModule* modp()		const { return m_modp; }
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
public:
    AstTopScope(FileLine* fl, AstScope* ascopep)
	:AstNode(fl)
	{addNOp2p(ascopep);}
    virtual ~AstTopScope() {}
    virtual AstType type() const { return AstType::TOPSCOPE;}
    virtual AstNode* clone() { return new AstTopScope(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
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
    virtual ~AstVarScope() {}
    virtual AstType type() const { return AstType::VARSCOPE;}
    virtual AstNode* clone() { return new AstVarScope(*this);}
    virtual void cloneRelink() { if (m_varp && m_varp->clonep()) {
	m_varp = m_varp->clonep()->castVar();
	UASSERT(m_scopep->clonep(), "No clone cross link: "<<this);
	m_scopep = m_scopep->clonep()->castScope();
    }}
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
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
private:
public:
    AstVarRef(FileLine* fl, const string& name, bool lvalue)
	:AstNodeVarRef(fl, name, NULL, lvalue) {}
    AstVarRef(FileLine* fl, AstVar* varp, bool lvalue)  // This form only allowed post-link
	:AstNodeVarRef(fl, varp->name(), varp, lvalue) {}		// because output/wire compression may lead to deletion of AstVar's
    AstVarRef(FileLine* fl, AstVarScope* varscp, bool lvalue)  // This form only allowed post-link
	:AstNodeVarRef(fl, varscp->varp()->name(), varscp->varp(), lvalue) {	// because output/wire compression may lead to deletion of AstVar's
	varScopep(varscp);
    }
    virtual ~AstVarRef() {}
    virtual AstType type() const { return AstType::VARREF;}
    virtual AstNode* clone() { return new AstVarRef(*this);}
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
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
    virtual ~AstVarXRef() {}
    virtual AstType type() const { return AstType::VARXREF;}
    virtual AstNode* clone() { return new AstVarXRef(*this);}
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
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
	setNOp1p(exprp); }
    virtual ~AstPin() {}
    virtual AstType type() const { return AstType::PIN;}
    virtual AstNode* clone() { return new AstPin(*this);}
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void dump(ostream& str);
    virtual bool broken() const { return (m_modVarp && !m_modVarp->brokeExists()); }
    virtual string name()	const { return m_name; }		// * = Pin name, ""=go by number
    void	name(const string& name)     { m_name = name; }
    int		pinNum()	const { return m_pinNum; }
    void	exprp(AstNode* nodep) { addOp1p(nodep); }
    AstNode*	exprp()		const { return op1p()->castNode(); }	// op1 = Expression connected to pin
    AstVar*	modVarp()	const { return m_modVarp; }		// [After Link] Pointer to variable
    void  	modVarp(AstVar* varp) { m_modVarp=varp; }
    bool	svImplicit()	const { return m_svImplicit; }
    void        svImplicit(bool flag) { m_svImplicit=flag; }
};

struct AstModule : public AstNode {
    // A module declaration
private:
    string	m_name;		// Name of the module
    string	m_origName;	// Name of the module, ignoring name() changes, for dot lookup
    bool	m_modPublic:1;	// Module has public references
    bool	m_modTrace:1;	// Tracing this module
    bool	m_inLibrary:1;	// From a library, no error if not used, never top level
    int		m_level;	// 1=top module, 2=cell off top module, ...
    int		m_varNum;	// Incrementing variable number
    AstVar*	m_clkReqVarp;	// Clock request variable
public:
    AstModule(FileLine* fl, const string& name)
	: AstNode (fl)
	,m_name(name), m_origName(name), m_modPublic(false)
	,m_modTrace(false), m_inLibrary(false)
	,m_level(0), m_varNum(0), m_clkReqVarp(NULL) { }
    virtual ~AstModule() {}
    virtual AstType type() const { return AstType::MODULE;}
    virtual AstNode* clone() { return new AstModule(*this);}
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void dump(ostream& str);
    virtual bool broken() const { return (m_clkReqVarp && !m_clkReqVarp->brokeExists()); }
    virtual bool maybePointedTo() const { return true; }
    virtual string name()	const { return m_name; }
    AstNode*	stmtsp() 	const { return op2p()->castNode(); }	// op2 = List of statements
    AstActive*  activesp()	const { return op3p()->castActive(); }	// op3 = List of i/sblocks
    // METHODS
    void addInlinesp(AstNode* nodep) { addOp1p(nodep); }
    void addStmtp(AstNode* nodep) { addOp2p(nodep); }
    void addActivep(AstNode* nodep) { addOp3p(nodep); }
    // ACCESSORS
    void name(const string& name) 	{ m_name = name; }
    string origName() const	{ return m_origName; }
    bool inLibrary() const 	{ return m_inLibrary; }
    void inLibrary(bool flag) 	{ m_inLibrary = flag; }
    void level(int level)	{ m_level = level; }
    int  level() const		{ return m_level; }
    bool isTop() const		{ return level()==1; }
    int  varNumGetInc() 	{ return ++m_varNum; }
    AstVar* clkReqVarp() const	{ return m_clkReqVarp; }
    void clkReqVarp(AstVar* varp) { m_clkReqVarp = varp; }
    void modPublic(bool flag) 	{ m_modPublic = flag; }
    bool modPublic() const 	{ return m_modPublic; }
    void modTrace(bool flag) 	{ m_modTrace = flag; }
    bool modTrace() const 	{ return m_modTrace; }
};

struct AstCell : public AstNode {
    // A instantiation cell
private:
    string	m_name;		// Cell name
    string	m_origName;	// Original name before dot addition
    string	m_modName;	// Module the cell instances
    bool	m_pinStar;	// Pin list has .*
    AstModule*	m_modp;		// [AfterLink] Pointer to module instanced
public:
    AstCell(FileLine* fl, const string& instName, const string& modName,
	    AstPin* pinsp, AstPin* paramsp, AstRange* rangep)
	: AstNode(fl)
	, m_name(instName), m_origName(instName), m_modName(modName)
	, m_pinStar(false), m_modp(NULL) {
	addNOp1p(pinsp); addNOp2p(paramsp); setNOp3p(rangep); }
    virtual ~AstCell() {}
    virtual AstType type() const { return AstType::CELL;}
    virtual AstNode* clone() { return new AstCell(*this);}
    // No cloneRelink, we presume cloneee's want the same module linkages
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void dump(ostream& str);
    virtual bool broken() const { return (m_modp && !m_modp->brokeExists()); }
    virtual bool maybePointedTo() const { return true; }
    // ACCESSORS
    virtual string name()	const { return m_name; }		// * = Cell name
    void name(const string& name) 	{ m_name = name; }
    string origName()		const { return m_origName; }		// * = Original name
    void origName(const string& name) 	{ m_origName = name; }
    string modName()		const { return m_modName; }		// * = Instance name
    void modName(const string& name)	{ m_modName = name; }
    bool pinStar()		const { return m_pinStar; }
    void pinStar(bool flag)		{ m_pinStar = flag; }
    AstPin* pinsp()		const { return op1p()->castPin(); }	// op1 = List of cell ports
    AstPin* paramsp()		const { return op2p()->castPin(); }	// op2 = List of parameter #(##) values
    AstRange* rangep()		const { return op3p()->castRange(); }	// op3 = Range of arrayed instants (NULL=not ranged)
    AstModule* modp()		const { return m_modp; }		// [AfterLink] = Pointer to module instantiated
    void addPinsp(AstPin* nodep) { addOp1p(nodep); }
    void addParamsp(AstPin* nodep) { addOp2p(nodep); }
    void modp(AstModule* nodep)	{ m_modp = nodep; }
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
    virtual ~AstCellInline() {}
    virtual AstType type() const { return AstType::CELLINLINE;}
    virtual AstNode* clone() { return new AstCellInline(*this);}
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void dump(ostream& str);
    // ACCESSORS
    virtual string name()	const { return m_name; }		// * = Cell name
    string origModName()	const { return m_origModName; }		// * = modp()->origName() before inlining
    void name(const string& name) 	{ m_name = name; }
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
    virtual ~AstPort() {}
    virtual AstType type() const { return AstType::PORT;}
    virtual AstNode* clone() { return new AstPort(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
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
public:
    // Node that simply puts name into the output stream
    AstBegin(FileLine* fileline, const string& name, AstNode* stmtsp)
	: AstNode(fileline)
	, m_name(name) {
	addNOp1p(stmtsp);
    }
    virtual ~AstBegin() {}
    virtual AstType type() const { return AstType::BEGIN;}
    virtual AstNode* clone() { return new AstBegin(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual string name()	const { return m_name; }		// * = Block name
    void name(const string& flag) { m_name=flag; }
    // op1 = Statements
    AstNode*	stmtsp() 	const { return op1p()->castNode(); }	// op1 = List of statements
    void addStmtp(AstNode* nodep) { addOp1p(nodep); }
};

struct AstGenerate : public AstNode {
    // A Generate/end block
    // Parents: MODULE
    // Children: modItems
    AstGenerate(FileLine* fileline, AstNode* stmtsp)
	: AstNode(fileline) {
	addNOp1p(stmtsp);
    }
    virtual ~AstGenerate() {}
    virtual AstType type() const { return AstType::GENERATE;}
    virtual AstNode* clone() { return new AstGenerate(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
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
    virtual ~AstParseRef() {}
    virtual AstType type() const { return AstType::PARSEREF;}
    virtual AstNode* clone() { return new AstParseRef(*this);}
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
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
    // A dot separating paths in a AstXRef, AstFuncRef or AstTaskRef
    // These are elimiated in the link stage
    AstDot(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
	:AstNode(fl) { setOp1p(lhsp); setOp2p(rhsp); }
    virtual ~AstDot() {}
    virtual AstType type() const { return AstType::DOT;}
    virtual AstNode* clone() { return new AstDot(*this);}
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
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
    virtual ~AstTask() {}
    virtual AstType type() const { return AstType::TASK;}
    virtual AstNode* clone() { return new AstTask(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
};

struct AstFunc : public AstNodeFTask {
    bool	m_attrIsolateAssign:1;// User isolate_assignments attribute
public:
    // A function inside a module
    AstFunc(FileLine* fl, const string& name, AstNode* stmtp, AstNode* fvarsp)
	:AstNodeFTask(fl, name, stmtp) {
	addNOp1p(fvarsp);
	m_attrIsolateAssign = false;
    }
    virtual ~AstFunc() {}
    virtual AstType type() const { return AstType::FUNC;}
    virtual AstNode* clone() { return new AstFunc(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    // op1 = Range output variable (functions only)
    AstNode*	fvarp() 	const { return op1p()->castNode(); }
    void addFvarp(AstNode* nodep) { addOp1p(nodep); }
    void	attrIsolateAssign(bool flag) { m_attrIsolateAssign = flag; }
    bool	attrIsolateAssign() const { return m_attrIsolateAssign; }
};

struct AstTaskRef : public AstNodeFTaskRef {
    // A reference to a task
    AstTaskRef(FileLine* fl, AstParseRef* namep, AstNode* pinsp)
	:AstNodeFTaskRef(fl, namep, pinsp) {}
    virtual ~AstTaskRef() {}
    virtual AstType type() const { return AstType::TASKREF;}
    virtual AstNode* clone() { return new AstTaskRef(*this);}
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
};

struct AstFuncRef : public AstNodeFTaskRef {
    // A reference to a function
    AstFuncRef(FileLine* fl, AstParseRef* namep, AstNode* pinsp)
	:AstNodeFTaskRef(fl, namep, pinsp) {}
    virtual ~AstFuncRef() {}
    virtual AstType type() const { return AstType::FUNCREF;}
    virtual AstNode* clone() { return new AstFuncRef(*this);}
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
};

//######################################################################

struct AstSenItem : public AstNode {
    // Parents:  SENTREE
    // Children: (optional) VARREF
private:
    AstEdgeType	m_edgeType;		// Edge type
public:
    class Combo {};		// for creator type-overload selection
    class Initial {};		// for creator type-overload selection
    class Settle {};		// for creator type-overload selection
    class Never {};		// for creator type-overload selection
    AstSenItem(FileLine* fl, AstEdgeType edgeType, AstNodeVarRef* varrefp)
	: AstNode(fl), m_edgeType(edgeType) {
	setOp1p(varrefp);
    }
    AstSenItem(FileLine* fl, AstEdgeType edgeType, AstParseRef* varrefp)
	: AstNode(fl), m_edgeType(edgeType) {
	setOp1p(varrefp);
    }
    AstSenItem(FileLine* fl, Combo)
	: AstNode(fl) {
	m_edgeType = AstEdgeType::COMBO;
    }
    AstSenItem(FileLine* fl, Initial)
	: AstNode(fl) {
	m_edgeType = AstEdgeType::INITIAL;
    }
    AstSenItem(FileLine* fl, Settle)
	: AstNode(fl) {
	m_edgeType = AstEdgeType::SETTLE;
    }
    AstSenItem(FileLine* fl, Never)
	: AstNode(fl) {
	m_edgeType = AstEdgeType::NEVER;
    }
    virtual ~AstSenItem() {}
    virtual AstType type() const { return AstType::SENITEM;}
    virtual AstNode* clone() { return new AstSenItem(*this); }
    AstSenItem*	cloneTree(bool cloneNextLink) { return AstNode::cloneTree(cloneNextLink)->castSenItem(); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void dump(ostream& str);
    virtual V3Hash sameHash() const { return V3Hash(V3Hash(edgeType())); }
    virtual bool same(AstNode* samep) const {
	return edgeType()==samep->castSenItem()->edgeType(); }
    AstEdgeType edgeType()	const { return m_edgeType; }		// * = Posedge/negedge
    void edgeType(AstEdgeType type)  { m_edgeType=type; editCountInc(); }// * = Posedge/negedge
    AstNode*	sensp()		const { return op1p(); }		// op1 = Signal sensitized
    AstNodeVarRef* varrefp()	const { return op1p()->castNodeVarRef(); }	// op1 = Signal sensitized
    //
    bool isClocked() const { return edgeType().clockedStmt(); }
    bool isCombo() const { return edgeType()==AstEdgeType::COMBO; }
    bool isInitial() const { return edgeType()==AstEdgeType::INITIAL; }
    bool isSettle() const { return edgeType()==AstEdgeType::SETTLE; }
    bool isNever() const { return edgeType()==AstEdgeType::NEVER; }
    bool hasVar() const { return !(isCombo()||isInitial()||isSettle()||isNever()); }
};

struct AstSenTree : public AstNode {
    // A list of senitems
    // Parents:  MODULE | SBLOCK
    // Children: SENITEM list
private:
    bool	m_multi;	// Created from combo logic by ORing multiple clock domains
public:
    AstSenTree(FileLine* fl, AstSenItem* sensesp)
	: AstNode(fl), m_multi(false) {
	addNOp1p(sensesp);
    }
    virtual ~AstSenTree() {}
    virtual AstType type() const { return AstType::SENTREE;}
    virtual AstNode* clone() { return new AstSenTree(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void dump(ostream& str);
    virtual bool maybePointedTo() const { return true; }
    bool isMulti() const { return m_multi; }
    AstSenItem*	sensesp() 	const { return op1p()->castSenItem(); }	// op1 = Sensitivity list
    void addSensesp(AstSenItem* nodep) { addOp1p(nodep); }
    void multi(bool flag) { m_multi = true; }
    // METHODS
    void sortSenses();	// Sort senitems in standard way
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
    virtual ~AstAlways() {}
    virtual AstType type() const { return AstType::ALWAYS;}
    virtual AstNode* clone() { return new AstAlways(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
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
    virtual ~AstAlwaysPost() {}
    virtual AstType type() const { return AstType::ALWAYSPOST;}
    virtual AstNode* clone() { return new AstAlwaysPost(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    //
    AstNode*	bodysp() 	const { return op2p()->castNode(); }	// op2 = Statements to evaluate
    void	addBodysp(AstNode* newp)	{ addOp2p(newp); }
};

struct AstAssign : public AstNodeAssign {
    AstAssign(FileLine* fileline, AstNode* lhsp, AstNode* rhsp)
	: AstNodeAssign(fileline, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp);
    }
    virtual ~AstAssign() {}
    virtual AstType type() const { return AstType::ASSIGN;}
    virtual AstNode* clone() { return new AstAssign(*this); }
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) { return new AstAssign(this->fileline(), lhsp, rhsp); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual string verilogKwd() const { return "="; };
};

struct AstAssignAlias : public AstNodeAssign {
    // Like AstAssignW, but a true bidirect interconnection alias
    // If both sides are wires, there's no LHS vs RHS,
public:
    AstAssignAlias(FileLine* fileline, AstVarRef* lhsp, AstVarRef* rhsp)
	: AstNodeAssign(fileline, lhsp, rhsp) {}
    virtual ~AstAssignAlias() {}
    virtual AstType type() const { return AstType::ASSIGNALIAS;}
    virtual AstNode* clone() { return new AstAssignAlias(*this); }
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) { V3ERROR_NA; return NULL; }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
};

struct AstAssignDly : public AstNodeAssign {
    AstAssignDly(FileLine* fileline, AstNode* lhsp, AstNode* rhsp)
	: AstNodeAssign(fileline, lhsp, rhsp) {}
    virtual ~AstAssignDly() {}
    virtual AstType type() const { return AstType::ASSIGNDLY;}
    virtual AstNode* clone() { return new AstAssignDly(*this); }
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) { return new AstAssignDly(this->fileline(), lhsp, rhsp); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual bool isGateOptimizable() const { return false; }
    virtual string verilogKwd() const { return "<="; };
};

struct AstAssignW : public AstNodeAssign {
    // Like assign, but wire/assign's in verilog, the only setting of the specified variable
private:
    bool	m_allowImplicit;	// Output can be a implicit wire
public:
    AstAssignW(FileLine* fileline, AstNode* lhsp, AstNode* rhsp)
	: AstNodeAssign(fileline, lhsp, rhsp) {
	m_allowImplicit = false;
    }
    virtual ~AstAssignW() {}
    virtual AstType type() const { return AstType::ASSIGNW;}
    virtual AstNode* clone() { return new AstAssignW(*this); }
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) { return new AstAssignW(this->fileline(), lhsp, rhsp); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    bool allowImplicit() const { return m_allowImplicit; }
    void allowImplicit(bool flag) { m_allowImplicit = flag; }
};

struct AstAssignPre : public AstNodeAssign {
    // Like Assign, but predelayed assignment requiring special order handling
    AstAssignPre(FileLine* fileline, AstNode* lhsp, AstNode* rhsp)
	: AstNodeAssign(fileline, lhsp, rhsp) {}
    virtual ~AstAssignPre() {}
    virtual AstType type() const { return AstType::ASSIGNPRE;}
    virtual AstNode* clone() { return new AstAssignPre(*this); }
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) { return new AstAssignPre(this->fileline(), lhsp, rhsp); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
};

struct AstAssignPost : public AstNodeAssign {
    // Like Assign, but predelayed assignment requiring special order handling
    AstAssignPost(FileLine* fileline, AstNode* lhsp, AstNode* rhsp)
	: AstNodeAssign(fileline, lhsp, rhsp) {}
    virtual ~AstAssignPost() {}
    virtual AstType type() const { return AstType::ASSIGNPOST;}
    virtual AstNode* clone() { return new AstAssignPost(*this); }
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) { return new AstAssignPost(this->fileline(), lhsp, rhsp); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
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
    virtual ~AstComment() {}
    virtual AstType type() const { return AstType::COMMENT;}
    virtual AstNode* clone() { return new AstComment(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
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
    virtual ~AstCond() {}
    virtual AstType type() const { return AstType::COND;}
    virtual AstNode* clone() { return new AstCond(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
};

struct AstCondBound : public AstNodeCond {
    // Conditional ?: statement, specially made for saftey checking of array bounds
    // Parents:  MATH
    // Children: MATH
    AstCondBound(FileLine* fl, AstNode* condp, AstNode* expr1p, AstNode* expr2p)
	: AstNodeCond(fl, condp, expr1p, expr2p) {}
    virtual ~AstCondBound() {}
    virtual AstType type() const { return AstType::CONDBOUND;}
    virtual AstNode* clone() { return new AstCondBound(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
};

struct AstCoverDecl : public AstNodeStmt {
    // Coverage analysis point declaration
    // Parents:  {statement list}
    // Children: none
private:
    string	m_typeText;
    string	m_text;
    string	m_hier;
    int		m_column;
public:
    AstCoverDecl(FileLine* fl, int column, const string& type, const string& comment)
	: AstNodeStmt(fl) {
	m_text = comment; m_typeText = type; m_column = column;
    }
    virtual ~AstCoverDecl() {}
    virtual AstType type() const { return AstType::COVERDECL;}
    virtual AstNode* clone() { return new AstCoverDecl(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void dump(ostream& str);
    virtual int instrCount()	const { return 1+2*instrCountLd(); }
    virtual bool maybePointedTo() const { return true; }
    int		column() 	const { return m_column; }
    const string& comment() const { return m_text; }			// text to insert in code
    const string& typeText() const { return m_typeText; }
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
    virtual ~AstCoverInc() {}
    virtual AstType type() const { return AstType::COVERINC;}
    virtual AstNode* clone() { return new AstCoverInc(*this); }
    virtual bool broken() const { return !declp()->brokeExists(); }
    virtual void cloneRelink() { if (m_declp->clonep()) m_declp = m_declp->clonep()->castCoverDecl(); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void dump(ostream& str);
    virtual int instrCount()	const { return 1+2*instrCountLd(); }
    virtual V3Hash sameHash() const { return V3Hash(declp()); }
    virtual bool same(AstNode* samep) const {
	return declp()==samep->castCoverInc()->declp(); }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool isOutputter() const { return true; }
    // but isSplittable()  true
    AstCoverDecl*	declp() const { return m_declp; }	// Where defined
};

struct AstGenCase : public AstNodeCase {
    // Generate Case statement
    // Parents:  {statement list}
    // exprp Children:  MATHs
    // casesp Children: CASEITEMs
public:
    AstGenCase(FileLine* fileline, AstNode* exprp, AstNode* casesp)
	: AstNodeCase(fileline, exprp, casesp) {
    }
    virtual ~AstGenCase() {}
    virtual AstType type() const { return AstType::GENCASE;}
    virtual AstNode* clone() { return new AstGenCase(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
};

struct AstCase : public AstNodeCase {
    // Case statement
    // Parents:  {statement list}
    // exprp Children:  MATHs
    // casesp Children: CASEITEMs
private:
    bool	m_casex;	// True if casex instead of normal case.
    bool	m_fullPragma;		// Synthesis full_case
    bool	m_parallelPragma;	// Synthesis parallel_case
public:
    AstCase(FileLine* fileline, bool casex, AstNode* exprp, AstNode* casesp)
	: AstNodeCase(fileline, exprp, casesp) {
	m_casex=casex;
	m_fullPragma=false; m_parallelPragma=false;
    }
    virtual ~AstCase() {}
    virtual AstType type() const { return AstType::CASE;}
    virtual AstNode* clone() { return new AstCase(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual string  verilogKwd() const { return casex()?"casex":"case"; }
    bool	casex()	const { return m_casex; }
    bool	fullPragma()	const { return m_fullPragma; }
    bool	parallelPragma()	const { return m_parallelPragma; }
    void	fullPragma(bool flag)	{ m_fullPragma=flag; }
    void	parallelPragma(bool flag) { m_parallelPragma=flag; }
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
    virtual ~AstCaseItem() {}
    virtual AstType type() const { return AstType::CASEITEM;}
    virtual AstNode* clone() { return new AstCaseItem(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual int instrCount()	const { return widthInstrs()+instrCountBranch(); }
    AstNode*	condsp()		const { return op1p()->castNode(); }	// op1= list of possible matching expressions
    AstNode*	bodysp()	const { return op2p()->castNode(); }	// op2= what to do
    void	condsp(AstNode* nodep) { setOp1p(nodep); }
    void	addBodysp(AstNode* newp)	{ addOp2p(newp); }
    bool	isDefault() const { return condsp()==NULL; }
    bool	ignoreOverlap() const { return m_ignoreOverlap; }
    void	ignoreOverlap(bool flag) { m_ignoreOverlap = flag; }
};

struct AstDisplay : public AstNodePli {
    // Parents: stmtlist
    // Children: file which must be a varref, MATH to print
private:
    AstDisplayType	m_displayType;
public:
    AstDisplay(FileLine* fileline, AstDisplayType dispType, const string& text, AstNode* filep, AstNode* exprsp)
	: AstNodePli (fileline, text, exprsp) {
	setNOp2p(filep);
	m_displayType = dispType;
    }
    virtual ~AstDisplay() {}
    virtual AstType type() const { return AstType::DISPLAY;}
    virtual AstNode* clone() { return new AstDisplay(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void dump(ostream& str);
    virtual string verilogKwd() const { return (filep() ? (string)"$f"+(string)displayType().ascii()
						: (string)"$"+(string)displayType().ascii()); }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool isSplittable() const { return false; }	// SPECIAL: $display has 'visual' ordering
    virtual bool isOutputter() const { return true; }	// SPECIAL: $display makes output
    virtual bool isUnlikely() const { return true; }
    virtual V3Hash sameHash() const { return V3Hash(text()); }
    virtual bool same(AstNode* samep) const {
	return displayType()==samep->castDisplay()->displayType()
	    && text()==samep->castDisplay()->text(); }
    // op1 used by AstNodePli
    AstDisplayType	displayType()	const { return m_displayType; }
    void	displayType(AstDisplayType type) { m_displayType = type; }
    bool	addNewline() const { return displayType().addNewline(); }  // * = Add a newline for $display
    AstNode*	filep() const { return op2p(); }
    void 	filep(AstNodeVarRef* nodep) { setNOp2p(nodep); }
    AstScopeName* scopeNamep() const { return op3p()->castScopeName(); }
    void 	scopeNamep(AstNode* nodep) { setNOp3p(nodep); }
};

struct AstFClose : public AstNodeStmt {
    // Parents: stmtlist
    // Children: file which must be a varref
    AstFClose(FileLine* fileline, AstNode* filep)
	: AstNodeStmt (fileline) {
	setNOp2p(filep);
    }
    virtual ~AstFClose() {}
    virtual AstType type() const { return AstType::FCLOSE;}
    virtual AstNode* clone() { return new AstFClose(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual string verilogKwd() const { return "$fclose"; };
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool isSplittable() const { return false; }
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
    virtual ~AstFOpen() {}
    virtual AstType type() const { return AstType::FOPEN;}
    virtual AstNode* clone() { return new AstFOpen(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual string verilogKwd() const { return "$fclose"; };
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool isSplittable() const { return false; }
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
    virtual ~AstFFlush() {}
    virtual AstType type() const { return AstType::FFLUSH;}
    virtual AstNode* clone() { return new AstFFlush(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual string verilogKwd() const { return "$fflush"; };
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool isSplittable() const { return false; }
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
    virtual ~AstFScanF() {}
    virtual AstType type() const { return AstType::FSCANF;}
    virtual AstNode* clone() { return new AstFScanF(*this); }
    virtual string name()	const { return m_text; }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual string verilogKwd() const { return "$fscanf"; }
    virtual string emitVerilog() { V3ERROR_NA; return ""; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool isSplittable() const { return false; }	// SPECIAL: has 'visual' ordering
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
    virtual ~AstSScanF() {}
    virtual AstType type() const { return AstType::SSCANF;}
    virtual AstNode* clone() { return new AstSScanF(*this); }
    virtual string name()	const { return m_text; }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual string verilogKwd() const { return "$sscanf"; }
    virtual string emitVerilog() { V3ERROR_NA; return ""; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool isSplittable() const { return false; }	// SPECIAL: has 'visual' ordering
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
    virtual ~AstReadMem() {}
    virtual AstType type() const { return AstType::READMEM;}
    virtual AstNode* clone() { return new AstReadMem(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual string verilogKwd() const { return (isHex()?"$readmemh":"$readmemb"); };
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool isSplittable() const { return false; }
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

struct AstGenFor : public AstNodeFor {
    AstGenFor(FileLine* fileline, AstNode* initsp, AstNode* condp,
	   AstNode* incsp, AstNode* bodysp)
	: AstNodeFor(fileline, initsp, condp, incsp, bodysp) {
    }
    virtual ~AstGenFor() {}
    virtual AstType type() const { return AstType::GENFOR;}
    virtual AstNode* clone() { return new AstGenFor(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
};

struct AstFor : public AstNodeFor {
    AstFor(FileLine* fileline, AstNode* initsp, AstNode* condp,
	   AstNode* incsp, AstNode* bodysp)
	: AstNodeFor(fileline, initsp, condp, incsp, bodysp) {
    }
    virtual ~AstFor() {}
    virtual AstType type() const { return AstType::FOR;}
    virtual AstNode* clone() { return new AstFor(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
};

struct AstWhile : public AstNodeStmt {
    AstWhile(FileLine* fileline, AstNode* condp, AstNode* bodysp)
	: AstNodeStmt(fileline) {
	setOp2p(condp); addNOp3p(bodysp);
    }
    virtual ~AstWhile() {}
    virtual AstType type() const { return AstType::WHILE;}
    virtual AstNode* clone() { return new AstWhile(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    AstNode*	precondsp()	const { return op1p()->castNode(); }	// op1= prepare statements for condition (exec every loop)
    AstNode*	condp()		const { return op2p()->castNode(); }	// op2= condition to continue
    AstNode*	bodysp()	const { return op3p()->castNode(); }	// op3= body of loop
    void	addPrecondsp(AstNode* newp)	{ addOp1p(newp); }
    void	addBodysp(AstNode* newp)	{ addOp3p(newp); }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual int instrCount()	const { return instrCountBranch(); }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
};

struct AstGenIf : public AstNodeIf {
    AstGenIf(FileLine* fileline, AstNode* condp, AstNode* ifsp, AstNode* elsesp)
	: AstNodeIf(fileline, condp, ifsp, elsesp) {
    }
    virtual ~AstGenIf() {}
    virtual AstType type() const { return AstType::GENIF;}
    virtual AstNode* clone() { return new AstGenIf(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
};

struct AstIf : public AstNodeIf {
    AstIf(FileLine* fileline, AstNode* condp, AstNode* ifsp, AstNode* elsesp)
	: AstNodeIf(fileline, condp, ifsp, elsesp) {
    }
    virtual ~AstIf() {}
    virtual AstType type() const { return AstType::IF;}
    virtual AstNode* clone() { return new AstIf(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
};

struct AstUntilStable : public AstNodeStmt {
    // Quasi-while loop until given signals are stable
    // Parents: CFUNC (generally)
    // Children: VARREF, statements
    AstUntilStable(FileLine* fileline, AstVarRef* stablesp, AstNode* bodysp)
	: AstNodeStmt(fileline) {
	addNOp2p(stablesp); addNOp3p(bodysp);
    }
    virtual ~AstUntilStable() {}
    virtual AstType type() const { return AstType::UNTILSTABLE;}
    virtual AstNode* clone() { return new AstUntilStable(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
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
	width(32,32); }
    virtual ~AstChangeXor() {}
    virtual AstType type() const { return AstType::CHANGEXOR;}
    virtual AstNode* clone() { return new AstChangeXor(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opChangeXor(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l ^ %r)"; }
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
    virtual ~AstChangeDet() {}
    virtual AstType type() const { return AstType::CHANGEDET;}
    virtual AstNode* clone() { return new AstChangeDet(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
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
    virtual ~AstInitial() {}
    virtual AstType type() const { return AstType::INITIAL;}
    virtual AstNode* clone() { return new AstInitial(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    AstNode*	bodysp() 	const { return op1p()->castNode(); }	// op1 = Expressions to evaluate
    // Special accessors
    bool isJustOneBodyStmt() const { return bodysp() && !bodysp()->nextp(); }
};

struct AstFinal : public AstNode {
    AstFinal(FileLine* fl, AstNode* bodysp)
	: AstNode(fl) {
	addNOp1p(bodysp);
    }
    virtual ~AstFinal() {}
    virtual AstType type() const { return AstType::FINAL;}
    virtual AstNode* clone() { return new AstFinal(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
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
    virtual ~AstInitArray() {}
    virtual AstType type() const { return AstType::INITARRAY;}
    virtual AstNode* clone() { return new AstInitArray(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
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
    virtual ~AstPragma() {}
    virtual AstType type() const { return AstType::PRAGMA;}
    virtual AstNode* clone() { return new AstPragma(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    AstPragmaType	pragType() 	const { return m_pragType; }	// *=type of the pragma
    virtual V3Hash sameHash() const { return V3Hash(pragType()); }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool same(AstNode* samep) const {
	return pragType()==samep->castPragma()->pragType(); }
};

struct AstStop : public AstNodeStmt {
    AstStop(FileLine* fl)
	: AstNodeStmt(fl) {}
    virtual ~AstStop() {}
    virtual AstType type() const { return AstType::STOP;}
    virtual AstNode* clone() { return new AstStop(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool isSplittable() const { return false; }	// SPECIAL: $display has 'visual' ordering
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
    virtual ~AstFinish() {}
    virtual AstType type() const { return AstType::FINISH;}
    virtual AstNode* clone() { return new AstFinish(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool isSplittable() const { return false; }	// SPECIAL: $display has 'visual' ordering
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
    uint32_t	m_lsb;		// Property of var the trace details
    uint32_t	m_msb;		// Property of var the trace details
    uint32_t	m_arrayLsb;	// Property of var the trace details
    uint32_t	m_arrayMsb;	// Property of var the trace details
    uint32_t	m_codeInc;	// Code increment
public:
    AstTraceDecl(FileLine* fl, const string& showname, AstVar* varp)
	: AstNodeStmt(fl)
	, m_showname(showname) {
	widthSignedFrom(varp);
	m_code = 0;
	m_codeInc = varp->arrayElements() * varp->widthWords();
	m_lsb = varp->lsb();  m_msb = varp->msb();
	m_arrayLsb = varp->arrayp(0) ? varp->arrayp(0)->lsbConst() : 0;
	m_arrayMsb = varp->arrayp(0) ? varp->arrayp(0)->msbConst() : 0;
    }
    virtual ~AstTraceDecl() {}
    virtual int instrCount()	const { return 100; }  // Large...
    virtual AstType type() const { return AstType::TRACEDECL;}
    virtual AstNode* clone() { return new AstTraceDecl(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual string name()	const { return m_showname; }
    virtual bool maybePointedTo() const { return true; }
    string showname()	const { return m_showname; }		// * = Var name
    virtual bool same(AstNode* samep) const { return false; }
    // Details on what we're tracing
    uint32_t	code() const { return m_code; }
    void	code(uint32_t code) { m_code=code; }
    uint32_t	codeInc() const { return m_codeInc; }
    uint32_t	msb() const { return m_msb; }
    uint32_t	lsb() const { return m_lsb; }
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
    virtual ~AstTraceInc() {}
    virtual AstType type() const { return AstType::TRACEINC;}
    virtual AstNode* clone() { return new AstTraceInc(*this); }
    virtual bool broken() const { return !declp()->brokeExists(); }
    virtual void cloneRelink() { if (m_declp->clonep()) m_declp = m_declp->clonep()->castTraceDecl(); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void dump(ostream& str);
    virtual int instrCount()	const { return 10+2*instrCountLd(); }
    virtual V3Hash sameHash() const { return V3Hash(declp()); }
    virtual bool same(AstNode* samep) const {
	return declp()==samep->castTraceInc()->declp(); }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool isOutputter() const { return true; }
    // but isSplittable()  true
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
    virtual ~AstActive() {}
    virtual AstType type() const { return AstType::ACTIVE;}
    virtual AstNode* clone() { return new AstActive(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
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
    int		m_dimension;	// Dimension number (0 is leftmost), for ARRAY_LSB extractions
public:
    AstAttrOf(FileLine* fl, AstAttrType attrtype, AstNode* fromp, int dimension=0)
	: AstNode(fl) {
	setOp1p(fromp); m_attrType = attrtype; m_dimension = dimension; }
    virtual ~AstAttrOf() {}
    virtual AstType type() const { return AstType::ATTROF;}
    virtual AstNode* clone() { return new AstAttrOf(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    AstNode*	fromp() const { return op1p(); }
    AstAttrType	attrType() const { return m_attrType; }
    int		dimension() const { return m_dimension; }
};

struct AstScopeName : public AstNode {
    // For display %m
    // Parents:  DISPLAY
    // Children: TEXT
    AstScopeName(FileLine* fl)
	: AstNode(fl) {}
    virtual ~AstScopeName() {}
    virtual AstType type() const { return AstType::SCOPENAME;}
    virtual AstNode* clone() { return new AstScopeName(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
    AstText*	scopeAttrp() const { return op1p()->castText(); }
    void 	scopeAttrp(AstNode* nodep) { addOp1p(nodep); }
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
    virtual ~AstRand() {}
    virtual AstType type() const { return AstType::RAND;}
    virtual AstNode* clone() { return new AstRand(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual string emitVerilog() { return "$random"; }
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
	width(64,64); }
    virtual ~AstTime() {}
    virtual AstType type() const { return AstType::TIME;}
    virtual AstNode* clone() { return new AstTime(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual string emitVerilog() { return "$time"; }
    virtual string emitC() { return "VL_TIME_%nq()"; }
    virtual bool cleanOut() { return true; }
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual int instrCount()	const { return instrCountTime(); }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
};

struct AstUCFunc : public AstNodeTermop {
    // User's $c function
public:
    AstUCFunc(FileLine* fl, AstNode* exprsp)
	: AstNodeTermop(fl) {
	addNOp1p(exprsp);
    }
    virtual ~AstUCFunc() {}
    virtual AstType type() const { return AstType::UCFUNC;}
    virtual AstNode* clone() { return new AstUCFunc(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual bool cleanOut() { return false; }
    virtual string emitVerilog() { V3ERROR_NA; return ""; }  // Implemented specially
    virtual string emitC() { V3ERROR_NA; return ""; }
    AstNode*	bodysp()	const { return op1p()->castNode(); }	// op1= expressions to print
    virtual bool isSplittable() const { return false; }	// SPECIAL: User may order w/other sigs
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

struct AstUnaryMin : public AstNodeUniop {
    AstUnaryMin(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    virtual ~AstUnaryMin() {}
    virtual AstType type() const { return AstType::UNARYMIN;}
    virtual AstNode* clone() { return new AstUnaryMin(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opUnaryMin(lhs); }
    virtual string emitVerilog() { return "%k(- %l)"; }
    virtual string emitC() { return "VL_UNARYMIN_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return false;}
    virtual bool sizeMattersLhs() {return true;}
};
struct AstRedAnd : public AstNodeUniop {
    AstRedAnd(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	width(1,1); }
    virtual ~AstRedAnd() {}
    virtual AstType type() const { return AstType::REDAND;}
    virtual AstNode* clone() { return new AstRedAnd(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opRedAnd(lhs); }
    virtual string emitVerilog() { return "%k(& %l)"; }
    virtual string emitC() { return "VL_REDAND_%nq%lq(%nw,%lw, %P, %li)"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
};
struct AstRedOr : public AstNodeUniop {
    AstRedOr(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	width(1,1); }
    virtual ~AstRedOr() {}
    virtual AstType type() const { return AstType::REDOR;}
    virtual AstNode* clone() { return new AstRedOr(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opRedOr(lhs); }
    virtual string emitVerilog() { return "%k(| %l)"; }
    virtual string emitC() { return "VL_REDOR_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
};
struct AstRedXor : public AstNodeUniop {
    AstRedXor(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	width(1,1); }
    virtual ~AstRedXor() {}
    virtual AstType type() const { return AstType::REDXOR;}
    virtual AstNode* clone() { return new AstRedXor(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opRedXor(lhs); }
    virtual string emitVerilog() { return "%k(^ %l)"; }
    virtual string emitC() { return "VL_REDXOR_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return (lhsp()->width()!=1 && lhsp()->width()!=2 && lhsp()->width()!=4
				     && lhsp()->width()!=8 && lhsp()->width()!=16);}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return 1+V3Number::log2b(width()); }
};
struct AstRedXnor : public AstNodeUniop {
    // AstRedXnors are replaced with AstRedXors in V3Const.
    AstRedXnor(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	width(1,1); }
    virtual ~AstRedXnor() {}
    virtual AstType type() const { return AstType::REDXNOR;}
    virtual AstNode* clone() { return new AstRedXnor(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opRedXnor(lhs); }
    virtual string emitVerilog() { return "%k(~^ %l)"; }
    virtual string emitC() { v3fatalSrc("REDXNOR should have became REDXOR"); return ""; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return 1+V3Number::log2b(width()); }
};

struct AstLogNot : public AstNodeUniop {
    AstLogNot(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	width(1,1); }
    virtual ~AstLogNot() {}
    virtual AstType type() const { return AstType::LOGNOT;}
    virtual AstNode* clone() { return new AstLogNot(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opLogNot(lhs); }
    virtual string emitVerilog() { return "%k(! %l)"; }
    virtual string emitC() { return "VL_LOGNOT_%nq%lq(%nw,%lw, %P, %li)"; }
    virtual string emitSimpleOperator() { return "!"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
};
struct AstNot : public AstNodeUniop {
    AstNot(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    virtual ~AstNot() {}
    virtual AstType type() const { return AstType::NOT;}
    virtual AstNode* clone() { return new AstNot(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opNot(lhs); }
    virtual string emitVerilog() { return "%k(~ %l)"; }
    virtual string emitC() { return "VL_NOT_%lq(%lW, %P, %li)"; }
    virtual string emitSimpleOperator() { return "~"; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return false;}
    virtual bool sizeMattersLhs() {return true;}
};
struct AstExtend : public AstNodeUniop {
    // Expand a value into a wider entity by 0 extension.  Width is implied from nodep->width()
    AstExtend(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {}
    virtual ~AstExtend() {}
    virtual AstType type() const { return AstType::EXTEND;}
    virtual AstNode* clone() { return new AstExtend(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
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
    virtual ~AstExtendS() {}
    virtual AstType type() const { return AstType::EXTENDS;}
    virtual AstNode* clone() { return new AstExtendS(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
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
	isSigned(true);
    }
    virtual ~AstSigned() {}
    virtual AstType type() const { return AstType::SIGNED;}
    virtual AstNode* clone() { return new AstSigned(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opAssign(lhs); out.isSigned(false); }
    virtual string emitVerilog() { return "%k$signed(%l)"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return false;}  // Eliminated before matters
    virtual bool sizeMattersLhs() {return true;}  // Eliminated before matters
    virtual int instrCount()	const { return 0; }
};
struct AstUnsigned : public AstNodeUniop {
    // $unsigned(lhs)
    AstUnsigned(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	isSigned(false);
    }
    virtual ~AstUnsigned() {}
    virtual AstType type() const { return AstType::UNSIGNED;}
    virtual AstNode* clone() { return new AstUnsigned(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opAssign(lhs); out.isSigned(false); }
    virtual string emitVerilog() { return "%k$unsigned(%l)"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return false;}  // Eliminated before matters
    virtual bool sizeMattersLhs() {return true;}  // Eliminated before matters
    virtual int instrCount()	const { return 0; }
};
struct AstCLog2 : public AstNodeUniop {
    AstCLog2(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {}
    virtual ~AstCLog2() {}
    virtual AstType type() const { return AstType::CLOG2;}
    virtual AstNode* clone() { return new AstCLog2(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opCLog2(lhs); }
    virtual string emitVerilog() { return "%k$clog2(%l)"; }
    virtual string emitC() { return "VL_CLOG2_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*16; }
};
struct AstCountOnes : public AstNodeUniop {
    // Number of bits set in vector
    AstCountOnes(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {}
    virtual ~AstCountOnes() {}
    virtual AstType type() const { return AstType::COUNTONES;}
    virtual AstNode* clone() { return new AstCountOnes(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opCountOnes(lhs); }
    virtual string emitVerilog() { return "%k$countones(%l)"; }
    virtual string emitC() { return "VL_COUNTONES_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*16; }
};
struct AstIsUnknown : public AstNodeUniop {
    // True if any unknown bits
    AstIsUnknown(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	width(1,1);}
    virtual ~AstIsUnknown() {}
    virtual AstType type() const { return AstType::ISUNKNOWN;}
    virtual AstNode* clone() { return new AstIsUnknown(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opIsUnknown(lhs); }
    virtual string emitVerilog() { return "%k$isunknown(%l)"; }
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return false;}
    virtual bool sizeMattersLhs() {return false;}
};
struct AstOneHot : public AstNodeUniop {
    // True if only single bit set in vector
    AstOneHot(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	width(1,1);}
    virtual ~AstOneHot() {}
    virtual AstType type() const { return AstType::ONEHOT;}
    virtual AstNode* clone() { return new AstOneHot(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opOneHot(lhs); }
    virtual string emitVerilog() { return "%k$onehot(%l)"; }
    virtual string emitC() { return "VL_ONEHOT_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*4; }
};
struct AstOneHot0 : public AstNodeUniop {
    // True if only single bit, or no bits set in vector
    AstOneHot0(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {
	width(1,1);}
    virtual ~AstOneHot0() {}
    virtual AstType type() const { return AstType::ONEHOT0;}
    virtual AstNode* clone() { return new AstOneHot0(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opOneHot0(lhs); }
    virtual string emitVerilog() { return "%k$onehot0(%l)"; }
    virtual string emitC() { return "VL_ONEHOT0_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*3; }
};

struct AstCast : public AstNodeUniop {
    // Cast to appropriate data type
private:
    int		m_size;
public:
    AstCast(FileLine* fl, AstNode* lhsp, int setwidth) : AstNodeUniop(fl, lhsp) {
	m_size=setwidth;
	if (setwidth) { width(setwidth,setwidth); }
    }
    AstCast(FileLine* fl, AstNode* lhsp, AstNode* widthFromp) : AstNodeUniop(fl, lhsp) {
	if (widthFromp) { widthSignedFrom(widthFromp); }
	m_size=width();
    }
    virtual ~AstCast() {}
    virtual AstType type() const { return AstType::CAST;}
    virtual AstNode* clone() { return new AstCast(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { out.opAssign(lhs); }
    virtual string emitVerilog() { return "%k$_CAST(%l)"; }
    virtual string emitC() { return "VL_CAST_%nq%lq(%nw,%lw, %P, %li)"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}  // Special cased in V3Cast
    virtual V3Hash sameHash() const { return V3Hash(size()); }
    virtual bool same(AstNode* samep) const { return size()==samep->castCast()->size(); }
    virtual void dump(ostream& str=cout);
    //
    int size()	const { return m_size; }
};

struct AstFEof : public AstNodeUniop {
    AstFEof(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {}
    virtual ~AstFEof() {}
    virtual AstType type() const { return AstType::FEOF;}
    virtual AstNode* clone() { return new AstFEof(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { V3ERROR_NA; }
    virtual string emitVerilog() { return "%k$feof(%l)"; }
    virtual string emitC() { return "(%li ? feof(VL_CVT_Q_FP(%li)) : true)"; }
    virtual bool cleanOut() {return true;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*16; }
    AstNode*	filep() const { return lhsp(); }
};

struct AstFGetC : public AstNodeUniop {
    AstFGetC(FileLine* fl, AstNode* lhsp) : AstNodeUniop(fl, lhsp) {}
    virtual ~AstFGetC() {}
    virtual AstType type() const { return AstType::FEOF;}
    virtual AstNode* clone() { return new AstFGetC(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs) { V3ERROR_NA; }
    virtual string emitVerilog() { return "%k$fgetc(%l)"; }
    // Non-existant filehandle returns EOF
    virtual string emitC() { return "(%li ? fgetc(VL_CVT_Q_FP(%li)) : -1)"; }
    virtual bool cleanOut() {return false;} virtual bool cleanLhs() {return true;}
    virtual bool sizeMattersLhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*64; }
    AstNode*	filep() const { return lhsp(); }
};

//======================================================================
// Binary ops

struct AstLogOr : public AstNodeBiComAsv {
    AstLogOr(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiComAsv(fl, lhsp, rhsp) {
	width(1,1); }
    virtual ~AstLogOr() {}
    virtual AstType type() const { return AstType::LOGOR;}
    virtual AstNode* clone() { return new AstLogOr(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLogOr(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k|| %r)"; }
    virtual string emitC() { return "VL_LOGOR_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "||"; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()+instrCountBranch(); }
};
struct AstLogAnd : public AstNodeBiComAsv {
    AstLogAnd(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiComAsv(fl, lhsp, rhsp) {
	width(1,1); }
    virtual ~AstLogAnd() {}
    virtual AstType type() const { return AstType::LOGAND;}
    virtual AstNode* clone() { return new AstLogAnd(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLogAnd(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k&& %r)"; }
    virtual string emitC() { return "VL_LOGAND_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "&&"; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()+instrCountBranch(); }
};
struct AstLogIf : public AstNodeBiop {
    AstLogIf(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	width(1,1); }
    virtual ~AstLogIf() {}
    virtual AstType type() const { return AstType::LOGIF;}
    virtual AstNode* clone() { return new AstLogIf(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { V3ERROR_NA; }
    virtual string emitVerilog() { return "%k(%l %k-> %r)"; }
    virtual string emitC() { return "VL_LOGIF_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "->"; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()+instrCountBranch(); }
};
struct AstLogIff : public AstNodeBiCom {
    AstLogIff(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiCom(fl, lhsp, rhsp) {
	width(1,1); }
    virtual ~AstLogIff() {}
    virtual AstType type() const { return AstType::LOGIFF;}
    virtual AstNode* clone() { return new AstLogIff(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { V3ERROR_NA; }
    virtual string emitVerilog() { return "%k(%l %k<-> %r)"; }
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
    virtual ~AstOr() {}
    virtual AstType type() const { return AstType::OR;}
    virtual AstNode* clone() { return new AstOr(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opOr(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k| %r)"; }
    virtual string emitC() { return "VL_OR_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "|"; }
    virtual bool cleanOut() {V3ERROR_NA; return false;}  // Lclean && Rclean
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
struct AstAnd : public AstNodeBiComAsv {
    AstAnd(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiComAsv(fl, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    virtual ~AstAnd() {}
    virtual AstType type() const { return AstType::AND;}
    virtual AstNode* clone() { return new AstAnd(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opAnd(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k& %r)"; }
    virtual string emitC() { return "VL_AND_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "&"; }
    virtual bool cleanOut() {V3ERROR_NA; return false;}  // Lclean || Rclean
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
struct AstXor : public AstNodeBiComAsv {
    AstXor(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiComAsv(fl, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    virtual ~AstXor() {}
    virtual AstType type() const { return AstType::XOR;}
    virtual AstNode* clone() { return new AstXor(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opXor(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k^ %r)"; }
    virtual string emitC() { return "VL_XOR_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "^"; }
    virtual bool cleanOut() {return false;}  // Lclean && Rclean
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
struct AstXnor : public AstNodeBiComAsv {
    AstXnor(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiComAsv(fl, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    virtual ~AstXnor() {}
    virtual AstType type() const { return AstType::XNOR;}
    virtual AstNode* clone() { return new AstXnor(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opXnor(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k^ ~ %r)"; }
    virtual string emitC() { return "VL_XNOR_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "^ ~"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return true;}
};
struct AstEq : public AstNodeBiCom {
    AstEq(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiCom(fl, lhsp, rhsp) {
	width(1,1); }
    virtual ~AstEq() {}
    virtual AstType type() const { return AstType::EQ;}
    virtual AstNode* clone() { return new AstEq(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opEq(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k== %r)"; }
    virtual string emitC() { return "VL_EQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "=="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
struct AstNeq : public AstNodeBiCom {
    AstNeq(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiCom(fl, lhsp, rhsp) {
	width(1,1); }
    virtual ~AstNeq() {}
    virtual AstType type() const { return AstType::NEQ;}
    virtual AstNode* clone() { return new AstNeq(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opNeq(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k!= %r)"; }
    virtual string emitC() { return "VL_NEQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "!="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
struct AstLt : public AstNodeBiop {
    AstLt(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	width(1,1); }
    virtual ~AstLt() {}
    virtual AstType type() const { return AstType::LT;}
    virtual AstNode* clone() { return new AstLt(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLt(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k< %r)"; }
    virtual string emitC() { return "VL_LT_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "<"; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
struct AstLtS : public AstNodeBiop {
    AstLtS(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	width(1,1); }
    virtual ~AstLtS() {}
    virtual AstType type() const { return AstType::LTS;}
    virtual AstNode* clone() { return new AstLtS(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLtS(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k< %r)"; }
    virtual string emitC() { return "VL_LTS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return ""; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual bool signedFlavor() const { return true; }
};
struct AstGt : public AstNodeBiop {
    AstGt(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	width(1,1); }
    virtual ~AstGt() {}
    virtual AstType type() const { return AstType::GT;}
    virtual AstNode* clone() { return new AstGt(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opGt(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k> %r)"; }
    virtual string emitC() { return "VL_GT_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return ">"; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
struct AstGtS : public AstNodeBiop {
    AstGtS(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	width(1,1); }
    virtual ~AstGtS() {}
    virtual AstType type() const { return AstType::GTS;}
    virtual AstNode* clone() { return new AstGtS(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opGtS(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k> %r)"; }
    virtual string emitC() { return "VL_GTS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return ""; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual bool signedFlavor() const { return true; }
};
struct AstGte : public AstNodeBiop {
    AstGte(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	width(1,1); }
    virtual ~AstGte() {}
    virtual AstType type() const { return AstType::GTE;}
    virtual AstNode* clone() { return new AstGte(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opGte(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k>= %r)"; }
    virtual string emitC() { return "VL_GTE_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return ">="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
struct AstGteS : public AstNodeBiop {
    AstGteS(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	width(1,1); }
    virtual ~AstGteS() {}
    virtual AstType type() const { return AstType::GTES;}
    virtual AstNode* clone() { return new AstGteS(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opGteS(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k>= %r)"; }
    virtual string emitC() { return "VL_GTES_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return ""; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual bool signedFlavor() const { return true; }
};
struct AstLte : public AstNodeBiop {
    AstLte(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	width(1,1); }
    virtual ~AstLte() {}
    virtual AstType type() const { return AstType::LTE;}
    virtual AstNode* clone() { return new AstLte(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLte(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k<= %r)"; }
    virtual string emitC() { return "VL_LTE_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "<="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
struct AstLteS : public AstNodeBiop {
    AstLteS(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	width(1,1); }
    virtual ~AstLteS() {}
    virtual AstType type() const { return AstType::LTES;}
    virtual AstNode* clone() { return new AstLteS(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opLteS(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k<= %r)"; }
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
    virtual ~AstShiftL() {}
    virtual AstType type() const { return AstType::SHIFTL;}
    virtual AstNode* clone() { return new AstShiftL(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opShiftL(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k<< %r)"; }
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
    virtual ~AstShiftR() {}
    virtual AstType type() const { return AstType::SHIFTR;}
    virtual AstNode* clone() { return new AstShiftR(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opShiftR(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k>> %r)"; }
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
    virtual ~AstShiftRS() {}
    virtual AstType type() const { return AstType::SHIFTRS;}
    virtual AstNode* clone() { return new AstShiftRS(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opShiftRS(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k>>> %r)"; }
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
    virtual ~AstAdd() {}
    virtual AstType type() const { return AstType::ADD;}
    virtual AstNode* clone() { return new AstAdd(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opAdd(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k+ %r)"; }
    virtual string emitC() { return "VL_ADD_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "+"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return true;}
};
struct AstSub : public AstNodeBiop {
    AstSub(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    virtual ~AstSub() {}
    virtual AstType type() const { return AstType::SUB;}
    virtual AstNode* clone() { return new AstSub(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opSub(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k- %r)"; }
    virtual string emitC() { return "VL_SUB_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "-"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return false;} virtual bool cleanRhs() {return false;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return true;}
};
struct AstMul : public AstNodeBiComAsv {
    AstMul(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiComAsv(fl, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    virtual ~AstMul() {}
    virtual AstType type() const { return AstType::MUL;}
    virtual AstNode* clone() { return new AstMul(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opMul(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k* %r)"; }
    virtual string emitC() { return "VL_MUL_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "*"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return true;}
    virtual int instrCount()	const { return widthInstrs()*instrCountMul(); }
};
struct AstMulS : public AstNodeBiComAsv {
    AstMulS(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiComAsv(fl, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    virtual ~AstMulS() {}
    virtual AstType type() const { return AstType::MULS;}
    virtual AstNode* clone() { return new AstMulS(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opMulS(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k* %r)"; }
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
    virtual ~AstDiv() {}
    virtual AstType type() const { return AstType::DIV;}
    virtual AstNode* clone() { return new AstDiv(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opDiv(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k/ %r)"; }
    virtual string emitC() { return "VL_DIV_%lq(%lW, %P, %li, %ri)"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return true;}
    virtual int instrCount()	const { return widthInstrs()*instrCountDiv(); }
};
struct AstDivS : public AstNodeBiop {
    AstDivS(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    virtual ~AstDivS() {}
    virtual AstType type() const { return AstType::DIVS;}
    virtual AstNode* clone() { return new AstDivS(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opDivS(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k/ %r)"; }
    virtual string emitC() { return "VL_DIVS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return true;}
    virtual int instrCount()	const { return widthInstrs()*instrCountDiv(); }
    virtual bool signedFlavor() const { return true; }
};
struct AstModDiv : public AstNodeBiop {
    AstModDiv(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    virtual ~AstModDiv() {}
    virtual AstType type() const { return AstType::MODDIV;}
    virtual AstNode* clone() { return new AstModDiv(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opModDiv(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k%% %r)"; }
    virtual string emitC() { return "VL_MODDIV_%lq(%lW, %P, %li, %ri)"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return true;}
    virtual int instrCount()	const { return widthInstrs()*instrCountDiv(); }
};
struct AstModDivS : public AstNodeBiop {
    AstModDivS(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    virtual ~AstModDivS() {}
    virtual AstType type() const { return AstType::MODDIVS;}
    virtual AstNode* clone() { return new AstModDivS(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opModDivS(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k%% %r)"; }
    virtual string emitC() { return "VL_MODDIVS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return true;}
    virtual int instrCount()	const { return widthInstrs()*instrCountDiv(); }
    virtual bool signedFlavor() const { return true; }
};
struct AstPow : public AstNodeBiop {
    AstPow(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    virtual ~AstPow() {}
    virtual AstType type() const { return AstType::POW;}
    virtual AstNode* clone() { return new AstPow(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opPow(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k** %r)"; }
    virtual string emitC() { return "VL_POW_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*instrCountMul(); }
};
struct AstPowS : public AstNodeBiop {
    AstPowS(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	if (lhsp) widthSignedFrom(lhsp); }
    virtual ~AstPowS() {}
    virtual AstType type() const { return AstType::POWS;}
    virtual AstNode* clone() { return new AstPowS(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opPowS(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k** %r)"; }
    virtual string emitC() { return "VL_POWS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return true;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*instrCountMul(); }
    virtual bool signedFlavor() const { return true; }
};
struct AstEqCase : public AstNodeBiCom {
    AstEqCase(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiCom(fl, lhsp, rhsp) {
	width(1,1); }
    virtual ~AstEqCase() {}
    virtual AstType type() const { return AstType::EQCASE;}
    virtual AstNode* clone() { return new AstEqCase(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opCaseEq(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k=== %r)"; }
    virtual string emitC() { return "VL_EQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "=="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
struct AstNeqCase : public AstNodeBiCom {
    AstNeqCase(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiCom(fl, lhsp, rhsp) {
	width(1,1); }
    virtual ~AstNeqCase() {}
    virtual AstType type() const { return AstType::NEQCASE;}
    virtual AstNode* clone() { return new AstNeqCase(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opCaseNeq(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k!== %r)"; }
    virtual string emitC() { return "VL_NEQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "!="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
struct AstEqWild : public AstNodeBiop {
    // Note wildcard operator rhs differs from lhs
    AstEqWild(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	width(1,1); }
    virtual ~AstEqWild() {}
    virtual AstType type() const { return AstType::EQWILD;}
    virtual AstNode* clone() { return new AstEqWild(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opWildEq(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k==? %r)"; }
    virtual string emitC() { return "VL_EQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() { return "=="; }
    virtual bool cleanOut() {return true;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
};
struct AstNeqWild : public AstNodeBiop {
    AstNeqWild(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {
	width(1,1); }
    virtual ~AstNeqWild() {}
    virtual AstType type() const { return AstType::NEQWILD;}
    virtual AstNode* clone() { return new AstNeqWild(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opWildNeq(lhs,rhs); }
    virtual string emitVerilog() { return "%k(%l %k!=? %r)"; }
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
    virtual ~AstConcat() {}
    virtual AstType type() const { return AstType::CONCAT;}
    virtual AstNode* clone() { return new AstConcat(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual string emitVerilog() { return "%k{%l, %k%r}"; }
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
    virtual ~AstReplicate() {}
    virtual AstType type() const { return AstType::REPLICATE;}
    virtual AstNode* clone() { return new AstReplicate(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { out.opRepl(lhs,rhs); }
    virtual string emitVerilog() { return "%k{%l{%k%r}}"; }
    virtual string emitC() { return "VL_REPLICATE_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual bool cleanOut() {return false;}
    virtual bool cleanLhs() {return true;} virtual bool cleanRhs() {return true;}
    virtual bool sizeMattersLhs() {return false;} virtual bool sizeMattersRhs() {return false;}
    virtual int instrCount()	const { return widthInstrs()*2; }
};
struct AstFGetS : public AstNodeBiop {
    AstFGetS(FileLine* fl, AstNode* lhsp, AstNode* rhsp) : AstNodeBiop(fl, lhsp, rhsp) {}
    virtual ~AstFGetS() {}
    virtual AstType type() const { return AstType::FEOF;}
    virtual AstNode* clone() { return new AstFGetS(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) { V3ERROR_NA; }
    virtual string emitVerilog() { return "%k$fgets(%l,%r)"; }
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
    virtual ~AstVAssert() {}
    virtual AstType type() const { return AstType::VASSERT;}
    virtual AstNode* clone() { return new AstVAssert(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
    AstNode*	propp()		const { return op1p(); }	// op1 = property
    AstNode*	passsp()	const { return op2p(); }	// op2 = if passes
    AstNode*	failsp()	const { return op3p(); }	// op3 = if fails
};

//======================================================================
// PSL

struct AstPslDefClock : public AstNode {
    // Set default PSL clock
    // Parents:  MODULE
    // Children: SENITEM
public:
    AstPslDefClock(FileLine* fl, AstSenItem* sensesp)
	: AstNode(fl) {
	addNOp1p(sensesp);
    }
    virtual ~AstPslDefClock() {}
    virtual AstType type() const { return AstType::PSLDEFCLOCK;}
    virtual AstNode* clone() { return new AstPslDefClock(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    AstSenItem*	sensesp() 	const { return op1p()->castSenItem(); }	// op1 = Sensitivity list
};

struct AstPslClocked : public AstNode {
    // A clocked property
    // Parents:  ASSERT|COVER (property)
    // Children: SENITEM, Properties
public:
    AstPslClocked(FileLine* fl, AstSenItem* sensesp, AstNode* propp)
	: AstNode(fl) {
	addNOp1p(sensesp);
	addOp2p(propp);
    }
    virtual ~AstPslClocked() {}
    virtual AstType type() const { return AstType::PSLCLOCKED;}
    virtual AstNode* clone() { return new AstPslClocked(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    AstSenItem*	sensesp() 	const { return op1p()->castSenItem(); }	// op1 = Sensitivity list
    AstNode*	propp()		const { return op2p(); }	// op2 = property
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
    virtual ~AstPslAssert() {}
    virtual AstType type() const { return AstType::PSLASSERT;}
    virtual AstNode* clone() { return new AstPslAssert(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
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
    AstPslCover(FileLine* fl, AstNode* propp, const string& name="")
	: AstNodeStmt(fl)
	, m_name(name) {
	addOp1p(propp);
    }
    virtual ~AstPslCover() {}
    virtual AstType type() const { return AstType::PSLCOVER;}
    virtual AstNode* clone() { return new AstPslCover(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual string name()	const { return m_name; }		// * = Var name
    virtual V3Hash sameHash() const { return V3Hash(name()); }
    virtual bool same(AstNode* samep) const { return samep->name() == name(); }
    AstNode*	propp()		const { return op1p(); }	// op1 = property
    AstSenTree*	sentreep()	const { return op2p()->castSenTree(); }	// op2 = clock domain
    void sentreep(AstSenTree* sentreep)  { addOp2p(sentreep); }	// op2 = clock domain
    AstNode*	coverincp()	const { return op3p(); }	// op3 = coverage node
    void coverincp(AstCoverInc* nodep)	{ addOp3p(nodep); }	// op3 = coverage node
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
    virtual ~AstPslBool() {}
    virtual AstType type() const { return AstType::PSLBOOL;}
    virtual AstNode* clone() { return new AstPslBool(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
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
    AstText(FileLine* fl, const string& textp)
	: AstNodeText(fl, textp) {}
    virtual ~AstText() {}
    virtual AstType type() const { return AstType::TEXT;}
    virtual AstNode* clone() { return new AstText(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
};

struct AstScCtor : public AstNodeText {
    AstScCtor(FileLine* fl, const string& textp)
	: AstNodeText(fl, textp) {}
    virtual ~AstScCtor() {}
    virtual AstType type() const { return AstType::SCCTOR;}
    virtual AstNode* clone() { return new AstScCtor(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual bool isSplittable() const { return false; }	// SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const { return true; }
};

struct AstScDtor : public AstNodeText {
    AstScDtor(FileLine* fl, const string& textp)
	: AstNodeText(fl, textp) {}
    virtual ~AstScDtor() {}
    virtual AstType type() const { return AstType::SCDTOR;}
    virtual AstNode* clone() { return new AstScDtor(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual bool isSplittable() const { return false; }	// SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const { return true; }
};

struct AstScHdr : public AstNodeText {
    AstScHdr(FileLine* fl, const string& textp)
	: AstNodeText(fl, textp) {}
    virtual ~AstScHdr() {}
    virtual AstType type() const { return AstType::SCHDR;}
    virtual AstNode* clone() { return new AstScHdr(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual bool isSplittable() const { return false; }	// SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const { return true; }
};

struct AstScImp : public AstNodeText {
    AstScImp(FileLine* fl, const string& textp)
	: AstNodeText(fl, textp) {}
    virtual ~AstScImp() {}
    virtual AstType type() const { return AstType::SCIMP;}
    virtual AstNode* clone() { return new AstScImp(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual bool isSplittable() const { return false; }	// SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const { return true; }
};

struct AstScImpHdr : public AstNodeText {
    AstScImpHdr(FileLine* fl, const string& textp)
	: AstNodeText(fl, textp) {}
    virtual ~AstScImpHdr() {}
    virtual AstType type() const { return AstType::SCIMPHDR;}
    virtual AstNode* clone() { return new AstScImpHdr(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual bool isSplittable() const { return false; }	// SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const { return true; }
};

struct AstScInt : public AstNodeText {
    AstScInt(FileLine* fl, const string& textp)
	: AstNodeText(fl, textp) {}
    virtual ~AstScInt() {}
    virtual AstType type() const { return AstType::SCINT;}
    virtual AstNode* clone() { return new AstScInt(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual bool isSplittable() const { return false; }	// SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const { return true; }
};

struct AstUCStmt : public AstNodeStmt {
    // User $c statement
    AstUCStmt(FileLine* fl, AstNode* exprsp)
	: AstNodeStmt(fl) {
	addNOp1p(exprsp);
    }
    virtual ~AstUCStmt() {}
    virtual AstType type() const { return AstType::UCSTMT;}
    virtual AstNode* clone() { return new AstUCStmt(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    AstNode*	bodysp()	const { return op1p()->castNode(); }	// op1= expressions to print
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool isSplittable() const { return false; }
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
    virtual ~AstCFile() {}
    virtual AstType type() const { return AstType::CFILE;}
    virtual AstNode* clone() { return new AstCFile(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
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
public:
    AstCFunc(FileLine* fl, const string& name, AstScope* scopep, const string& rtnType="")
	: AstNode(fl) {
	m_funcType = AstCFuncType::NORMAL;
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
    }
    virtual ~AstCFunc() {}
    virtual AstType type() const { return AstType::CFUNC;}
    virtual AstNode* clone() { return new AstCFunc(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual string name()	const { return m_name; }
    virtual bool broken() const { return ( (m_scopep && !m_scopep->brokeExists())); }
    virtual bool maybePointedTo() const { return true; }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return ((funcType()==samep->castCFunc()->funcType())
						      && (rtnTypeVoid()==samep->castCFunc()->rtnTypeVoid())
						      && (argTypes()==samep->castCFunc()->argTypes())); }
    //
    void	name(const string& flag) { m_name = flag; }
    AstScope*	scopep() const { return m_scopep; }
    void	scopep(AstScope* nodep) { m_scopep = nodep; }
    string	rtnTypeVoid() const { return ((m_rtnType=="") ? "void" : m_rtnType); }
    bool	dontCombine() const { return m_dontCombine || funcType()!=AstCFuncType::NORMAL; }
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
    //
    // If adding node accessors, see below
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
	: AstNodeStmt(oldp->fileline()) {
	m_funcp = funcp;
	m_hiername = oldp->hiername();
    }
    virtual ~AstCCall() {}
    virtual AstType type() const { return AstType::CCALL;}
    virtual AstNode* clone() { return new AstCCall(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
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
    virtual bool isSplittable() const { return false; }	// SPECIAL: $display has 'visual' ordering
    virtual bool isOutputter() const { return true; }
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
public:
    AstCReturn(FileLine* fl, AstNode* lhsp)
	: AstNodeStmt(fl) {
	setOp1p(lhsp);
    }
    virtual ~AstCReturn() {}
    virtual AstType type() const { return AstType::CRETURN;}
    virtual AstNode* clone() { return new AstCReturn(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual int instrCount()	const { return widthInstrs(); }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode*) const { return true; }
    //
    AstNode*	lhsp() const { return op1p(); }
};

struct AstCInclude : public AstNode {
    // C++ use of another class
    // Parents:  MODULE
    // Children: None
private:
    AstModule*	m_modp;
public:
    AstCInclude(FileLine* fl, AstModule* modp)
	: AstNode(fl) {
	m_modp = modp;
    }
    virtual ~AstCInclude() {}
    virtual AstType type() const { return AstType::CINCLUDE;}
    virtual AstNode* clone() { return new AstCInclude(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    virtual bool broken() const { return (m_modp && !m_modp->brokeExists()); }
    virtual void cloneRelink() { if (m_modp && m_modp->clonep()) {
	m_modp = m_modp->clonep()->castModule();
    }}
    AstModule*	modp() const { return m_modp; }
};

struct AstCMath : public AstNodeMath {
    // Emit C textual math function (like AstUCFunc)
    AstCMath(FileLine* fl, AstNode* exprsp)
	: AstNodeMath(fl) {
	addOp1p(exprsp);
	widthSignedFrom(exprsp);
    }
    AstCMath(FileLine* fl, const string& textStmt, int setwidth)
	: AstNodeMath(fl) {
	addNOp1p(new AstText(fl, textStmt));
	if (setwidth) { width(setwidth,setwidth); }
    }
    virtual ~AstCMath() {}
    virtual AstType type() const { return AstType::CMATH;}
    virtual AstNode* clone() { return new AstCMath(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    AstNode*	bodysp()	const { return op1p()->castNode(); }	// op1= expressions to print
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual bool cleanOut() { return true; }
    virtual string emitVerilog() { V3ERROR_NA; return ""; }  // Implemented specially
    virtual string emitC() { V3ERROR_NA; return ""; }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
};


struct AstCStmt : public AstNodeStmt {
    // Emit C statement
    AstCStmt(FileLine* fl, AstNode* exprsp)
	: AstNodeStmt(fl) {
	addNOp1p(exprsp);
    }
    AstCStmt(FileLine* fl, const string& textStmt)
	: AstNodeStmt(fl) {
	addNOp1p(new AstText(fl, textStmt));
    }
    virtual ~AstCStmt() {}
    virtual AstType type() const { return AstType::CSTMT;}
    virtual AstNode* clone() { return new AstCStmt(*this); }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    AstNode*	bodysp()	const { return op1p()->castNode(); }	// op1= expressions to print
    virtual bool isGateOptimizable() const { return false; }
    virtual bool isPredictOptimizable() const { return false; }
    virtual V3Hash sameHash() const { return V3Hash(); }
    virtual bool same(AstNode* samep) const { return true; }
};

//######################################################################
// Top

struct AstNetlist : public AstNode {
    // All modules are under this single top node.
    // Parents:   none
    // Children:  MODULEs & CFILEs
    AstNetlist() : AstNode(new FileLine("AstRoot",0)) {}
    virtual ~AstNetlist() {}
    virtual AstType type() const { return AstType::NETLIST;}
    virtual AstNode* clone() { v3fatalSrc("Can't clone top-level netlist\n"); return NULL; }
    virtual void accept(AstNVisitor& v, AstNUser* vup=NULL) { v.visit(this,vup); }
    AstModule*	modulesp() 	const { return op1p()->castModule();}	// op1 = List of modules
    AstModule*  topModulep() const { return op1p()->castModule(); }	// * = Top module in hierarchy (first one added, for now)
    void addModulep(AstModule* modulep) { addOp1p(modulep); }
    AstCFile*	filesp() 	const { return op2p()->castCFile();}	// op2 = List of files
    void addFilesp(AstCFile* filep) { addOp2p(filep); }
};

//######################################################################

#endif // Guard
