//*************************************************************************
// DESCRIPTION: Verilator: Ast node structures
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

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <fstream>
#include <iomanip>
#include <vector>
#include <algorithm>

#include "V3Ast.h"
#include "V3File.h"
#include "V3Global.h"

//======================================================================
// Special methods

// We need these here, because the classes they point to aren't defined when we declare the class
bool AstNodeVarRef::broken() const { return ((m_varScopep && !m_varScopep->brokeExists())
					     || (m_varp && !m_varp->brokeExists())); }

void AstNodeVarRef::cloneRelink() {
    if (m_varp && m_varp->clonep()) { m_varp = m_varp->clonep()->castVar(); }
}

int AstNodeSel::bitConst() const {
    AstConst* constp=bitp()->castConst(); return (constp?constp->toSInt():0);
}

int AstBasicDType::widthAlignBytes() const {
    if (width()<=8) return 1;
    else if (width()<=16) return 2;
    else if (isQuad()) return 8;
    else return 4;
}

int AstBasicDType::widthTotalBytes() const {
    if (width()<=8) return 1;
    else if (width()<=16) return 2;
    else if (isQuad()) return 8;
    else return widthWords()*(VL_WORDSIZE/8);
}

bool AstVar::isSigPublic() const {
    return (m_sigPublic || (v3Global.opt.allPublic() && !isTemp() && !isGenVar()));
}

bool AstVar::isScQuad() const {
    return (isSc() && isQuad() && !isScBv());
}

bool AstVar::isScBv() const {
    return ((isSc() && width() >= v3Global.opt.pinsBv()) || m_attrScBv);
}

void AstVar::combineType(AstVarType type) {
    if (type == AstVarType::SUPPLY0) type = AstVarType::WIRE;
    if (type == AstVarType::SUPPLY1) type = AstVarType::WIRE;
    m_varType=type; 	// For debugging prints only
    // These flags get combined with the existing settings of the flags.
    if (type==AstVarType::INPUT || type==AstVarType::INOUT)
	m_input = true;
    if (type==AstVarType::OUTPUT || type==AstVarType::INOUT)
	m_output = true;
    if (type==AstVarType::INOUT || type==AstVarType::TRIWIRE)
	m_tristate = true;
}

string AstVar::verilogKwd() const {
    if (isInout()) {
	return "inout";
    } else if (isInput()) {
	return "input";
    } else if (isOutput()) {
	return "output";
    } else if (isTristate()) {
	return "tri";
    } else if (varType()==AstVarType::WIRE) {
	return "wire";
    } else {
	return dtypep()->name();
    }
}

string AstVar::vlArgType(bool named, bool forReturn) const {
    if (forReturn) named=false;
    if (forReturn) v3fatalSrc("verilator internal data is never passed as return, but as first argument");
    string arg;
    if (isWide() && isInOnly()) arg += "const ";
    AstBasicDType* bdtypep = basicp();
    bool strtype = bdtypep && bdtypep->keyword()==AstBasicDTypeKwd::STRING;
    if (bdtypep && bdtypep->keyword()==AstBasicDTypeKwd::CHARPTR) {
	arg += "const char*";
    } else if (bdtypep && bdtypep->keyword()==AstBasicDTypeKwd::SCOPEPTR) {
	arg += "const VerilatedScope*";
    } else if (bdtypep && bdtypep->keyword()==AstBasicDTypeKwd::DOUBLE) {
	arg += "double";
    } else if (bdtypep && bdtypep->keyword()==AstBasicDTypeKwd::FLOAT) {
	arg += "float";
    } else if (strtype) {
	if (isInOnly()) arg += "const ";
	arg += "string";
    } else if (widthMin() <= 8) {
	arg += "CData";
    } else if (widthMin() <= 16) {
	arg += "SData";
    } else if (widthMin() <= VL_WORDSIZE) {
	arg += "IData";
    } else if (isQuad()) {
	arg += "QData";
    } else if (isWide()) {
	arg += "WData";  // []'s added later
    }
    if (isWide() && !strtype) {
	arg += " (& "+name();
	arg += ")["+cvtToStr(widthWords())+"]";
    } else {
	if (isOutput() || (strtype && isInput())) arg += "&";
	if (named) arg += " "+name();
    }
    return arg;
}

string AstVar::vlEnumType() const {
    string arg;
    AstBasicDType* bdtypep = basicp();
    bool strtype = bdtypep && bdtypep->keyword()==AstBasicDTypeKwd::STRING;
    if (bdtypep && bdtypep->keyword()==AstBasicDTypeKwd::CHARPTR) {
	return "VLVT_PTR";
    } else if (bdtypep && bdtypep->keyword()==AstBasicDTypeKwd::SCOPEPTR) {
	return "VLVT_PTR";
    } else if (strtype) {
	arg += "VLVT_STRING";
    } else if (widthMin() <= 8) {
	arg += "VLVT_UINT8";
    } else if (widthMin() <= 16) {
	arg += "VLVT_UINT16";
    } else if (widthMin() <= VL_WORDSIZE) {
	arg += "VLVT_UINT32";
    } else if (isQuad()) {
	arg += "VLVT_UINT64";
    } else if (isWide()) {
	arg += "VLVT_WDATA";
    }
    // else return "VLVT_UNKNOWN"
    return arg;
}

string AstVar::vlEnumDir() const {
    if (isInout()) {
	return "VLVD_INOUT";
    } else if (isInOnly()) {
	return "VLVD_IN";
    } else if (isOutOnly()) {
	return "VLVD_OUT";
    } else {
	return "VLVD_NODIR";
    }
}

string AstVar::cPubArgType(bool named, bool forReturn) const {
    if (forReturn) named=false;
    string arg;
    if (isWide() && isInOnly()) arg += "const ";
    if (widthMin() == 1) {
	arg += "bool";
    } else if (widthMin() <= VL_WORDSIZE) {
	arg += "uint32_t";
    } else if (isWide()) {
	arg += "uint32_t";  // []'s added later
    } else {
	arg += "vluint64_t";
    }
    if (isWide()) {
	if (forReturn) v3error("Unsupported: Public functions with >64 bit outputs; make an output of a public task instead");
	arg += " (& "+name();
	arg += ")["+cvtToStr(widthWords())+"]";
    } else {
	if (isOutput() && !forReturn) arg += "&";
	if (named) arg += " "+name();
    }
    return arg;
}

string AstVar::dpiArgType(bool named, bool forReturn) const {
    if (forReturn) named=false;
    string arg;
    if (!basicp()) arg = "UNKNOWN";
    if (basicp()->isBitLogic()) {
	if (widthMin() == 1) {
	    arg = "unsigned char";
	    if (!forReturn && isOutput()) arg += "*";
	} else {
	    if (forReturn) {
		arg = "svBitVecVal";
	    } else if (isInOnly()) {
		arg = "const svBitVecVal*";
	    } else {
		arg = "svBitVecVal*";
	    }
	}
    } else {
	arg = basicp()->keyword().dpiType();
	if (!forReturn && isOutput()) arg += "*";
    }
    if (named) arg += " "+name();
    return arg;
}

string AstVar::scType() const {
    if (isScBv()) {
	return (string("sc_bv<")+cvtToStr(widthMin())+"> ");  // Keep the space so don't get >>
    } else if (widthMin() == 1) {
	return "bool";
    } else if (widthMin() <= VL_WORDSIZE) {
	if (widthMin() <= 8 && v3Global.opt.pinsUint8()) {
	    return "uint8_t";
	} else if (widthMin() <= 16 && v3Global.opt.pinsUint8()) {
	    return "uint16_t";
	} else {
	    return "uint32_t";
	}
    } else {
	return "vluint64_t";
    }
}

AstNodeDType* AstNodeDType::dtypeDimensionp(int dimension) {
    // dimension passed from AstArraySel::dimension
    // Dimension 0 means the VAR itself, 1 is the closest SEL to the AstVar,
    // which is the lowest in the dtype list.
    //     ref order:   a[1][2][3][4]
    //     Created as:  reg [4] a [1][2][3];
    //        *or*      reg a [1][2][3][4];
    //     		// The bit select is optional; used only if "leftover" []'s
    //	   SEL:	        SEL4(SEL3(SEL2(SEL1(VARREF0 a))))
    //	   DECL:	VAR a (ARRAYSEL0 (ARRAYSEL1 (ARRAYSEL2 (DT RANGE3))))
    //	      *or*	VAR a (ARRAYSEL0 (ARRAYSEL1 (ARRAYSEL2 (ARRAYSEL3 (DT))))
    //	   SEL1 needs to select from entire variable which is a pointer to ARRAYSEL0
    int dim = 0;
    for (AstNodeDType* dtypep=this; dtypep; ) {
	dtypep = dtypep->skipRefp();  // Skip AstRefDType/AstTypedef, or return same node
	if (AstArrayDType* adtypep = dtypep->castArrayDType()) {
	    if ((dim++)==dimension) {
		return dtypep;
	    }
	    dtypep = adtypep->dtypep();
	    continue;
	}
	else if (AstBasicDType* adtypep = dtypep->castBasicDType()) {
	    // AstBasicDType - nothing below, return null
	    if (adtypep->isRanged()) {
		if ((dim++) == dimension) {
		    return adtypep;
		}
	    }
	    return NULL;
	}
	// Node no ->next in loop; use continue where necessary
	break;
    }
    return NULL;
}

uint32_t AstNodeDType::arrayElements() {
    uint32_t entries=1;
    for (AstNodeDType* dtypep=this; dtypep; ) {
	dtypep = dtypep->skipRefp();  // Skip AstRefDType/AstTypedef, or return same node
	if (AstArrayDType* adtypep = dtypep->castArrayDType()) {
	    entries *= adtypep->elementsConst();
	    dtypep = adtypep->dtypep();
	}
	else {
	    // AstBasicDType - nothing below, 1
	    break;
	}
    }
    return entries;
}

pair<uint32_t,uint32_t> AstNodeDType::dimensions() {
    // How many array dimensions (packed,unpacked) does this Var have?
    uint32_t packed = 0;
    uint32_t unpacked = 0;
    for (AstNodeDType* dtypep=this; dtypep; ) {
	dtypep = dtypep->skipRefp();  // Skip AstRefDType/AstTypedef, or return same node
	if (AstArrayDType* adtypep = dtypep->castArrayDType()) {
	    if (adtypep->isPacked()) packed += 1;
	    else unpacked += 1;
	    dtypep = adtypep->dtypep();
	}
	else {
	    // AstBasicDType - nothing below, 1
	    break;
	}
    }
    return make_pair(packed, unpacked);
}

// Special operators
int AstArraySel::dimension(AstNode* nodep) {
    // How many dimensions is this reference from the base variable?
    // nodep is typically the fromp() of a select; thus the first select
    // is selecting from the entire variable type - effectively dimension 0.
    // Dimension passed to AstVar::dtypeDimensionp; see comments there
    int dim = 0;
    while (nodep) {
	if (nodep->castNodeSel()) { dim++; nodep=nodep->castNodeSel()->fromp(); continue; }
	if (nodep->castNodePreSel()) { dim++; nodep=nodep->castNodePreSel()->fromp(); continue; }
	break;
    }
    return dim;
}
AstNode* AstArraySel::baseFromp(AstNode* nodep) {	///< What is the base variable (or const) this dereferences?
    // Else AstArraySel etc; search for the base
    while (nodep) {
	if (nodep->castArraySel()) { nodep=nodep->castArraySel()->fromp(); continue; }
	else if (nodep->castSel()) { nodep=nodep->castSel()->fromp(); continue; }
	// AstNodeSelPre stashes the associated variable under a ATTROF so it isn't constified
	else if (nodep->castAttrOf()) { nodep=nodep->castAttrOf()->fromp(); continue; }
	else if (nodep->castNodePreSel()) {
	    if (nodep->castNodePreSel()->attrp()) {
		nodep=nodep->castNodePreSel()->attrp();
	    } else {
		nodep=nodep->castNodePreSel()->lhsp();
	    }
	    continue;
	}
	else break;
    }
    return nodep;
}

bool AstScope::broken() const {
    return ((m_aboveScopep && !m_aboveScopep->brokeExists())
	    || (m_aboveCellp && !m_aboveCellp->brokeExists())
	    || !m_modp || !m_modp->brokeExists());
}

void AstScope::cloneRelink() {
    if (m_aboveScopep && m_aboveScopep->clonep()) m_aboveScopep->clonep()->castScope();
    if (m_aboveCellp && m_aboveCellp->clonep()) m_aboveCellp->clonep()->castCell();
    if (m_modp && ((AstNode*)m_modp)->clonep()) ((AstNode*)m_modp)->clonep()->castNodeModule();
}

string AstScope::nameDotless() const {
    string out = shortName();
    string::size_type pos;
    while ((pos=out.find(".")) != string::npos) {
	out.replace(pos, 1, "__");
    }
    return out;
}

string AstScopeName::scopePrettyName() const {
    string out;
    for (AstText* textp=scopeAttrp(); textp; textp=textp->nextp()->castText()) {
	out += textp->text();
    }
    // TOP will be replaced by top->name()
    if (out.substr(0,10) == "__DOT__TOP") out.replace(0,10,"");
    if (out.substr(0,7) == "__DOT__") out.replace(0,7,"");
    if (out.substr(0,1) == ".") out.replace(0,1,"");
    return AstNode::prettyName(out);
}

string AstScopeName::scopeSymName() const {
    string out;
    for (AstText* textp=scopeAttrp(); textp; textp=textp->nextp()->castText()) {
	out += textp->text();
    }
    if (out.substr(0,10) == "__DOT__TOP") out.replace(0,10,"");
    if (out.substr(0,7) == "__DOT__") out.replace(0,7,"");
    if (out.substr(0,1) == ".") out.replace(0,1,"");
    string::size_type pos;
    while ((pos=out.find(".")) != string::npos) {
	out.replace(pos, 1, "__");
    }
    while ((pos=out.find("__DOT__")) != string::npos) {
	out.replace(pos, 7, "__");
    }
    return out;
}

bool AstSenTree::hasClocked() {
    if (!sensesp()) this->v3fatalSrc("SENTREE without any SENITEMs under it");
    for (AstNodeSenItem* senp = sensesp(); senp; senp=senp->nextp()->castNodeSenItem()) {
	if (senp->isClocked()) return true;
    }
    return false;
}
bool AstSenTree::hasSettle() {
    if (!sensesp()) this->v3fatalSrc("SENTREE without any SENITEMs under it");
    for (AstNodeSenItem* senp = sensesp(); senp; senp=senp->nextp()->castNodeSenItem()) {
	if (senp->isSettle()) return true;
    }
    return false;
}
bool AstSenTree::hasInitial() {
    if (!sensesp()) this->v3fatalSrc("SENTREE without any SENITEMs under it");
    for (AstNodeSenItem* senp = sensesp(); senp; senp=senp->nextp()->castNodeSenItem()) {
	if (senp->isInitial()) return true;
    }
    return false;
}
bool AstSenTree::hasCombo() {
    if (!sensesp()) this->v3fatalSrc("SENTREE without any SENITEMs under it");
    for (AstNodeSenItem* senp = sensesp(); senp; senp=senp->nextp()->castNodeSenItem()) {
	if (senp->isCombo()) return true;
    }
    return false;
}

//======================================================================
// Special walking tree inserters

void AstNode::addBeforeStmt(AstNode* newp, AstNode*) {
    if (!backp()) newp->v3fatalSrc("Can't find current statement to addBeforeStmt");
    // Look up; virtual call will find where to put it
    this->backp()->addBeforeStmt(newp, this);
}
void AstNode::addNextStmt(AstNode* newp, AstNode*) {
    if (!backp()) newp->v3fatalSrc("Can't find current statement to addBeforeStmt");
    // Look up; virtual call will find where to put it
    this->backp()->addNextStmt(newp, this);
}

void AstNodeStmt::addBeforeStmt(AstNode* newp, AstNode*) {
    // Insert newp before current node
    this->addHereThisAsNext(newp);
}
void AstNodeStmt::addNextStmt(AstNode* newp, AstNode*) {
    // Insert newp after current node
    this->addNextHere(newp);
}

void AstWhile::addBeforeStmt(AstNode* newp, AstNode* belowp) {
    // Special, as statements need to be put in different places
    // Belowp is how we came to recurse up to this point
    // Preconditions insert first just before themselves (the normal rule for other statement types)
    if (belowp == precondsp()) {
	// Must have been first statement in precondsp list, so newp is new first statement
	belowp->addHereThisAsNext(newp);
    } else if (belowp == condp()) {
	// Goes before condition, IE in preconditions
	addPrecondsp(newp);
    } else if (belowp == bodysp()) {
	// Was first statement in body, so new front
	belowp->addHereThisAsNext(newp);
    } else {
	belowp->v3fatalSrc("Doesn't look like this was really under the while");
    }
}
void AstWhile::addNextStmt(AstNode* newp, AstNode* belowp) {
    // Special, as statements need to be put in different places
    // Belowp is how we came to recurse up to this point
    // Preconditions insert first just before themselves (the normal rule for other statement types)
    if (belowp == precondsp()) {
	// Next in precond list
	belowp->addNextHere(newp);
    } else if (belowp == condp()) {
	// Becomes first statement in body, body may have been empty
	if (bodysp()) {
	    bodysp()->addHereThisAsNext(newp);
	} else {
	    addBodysp(newp);
	}
    } else if (belowp == bodysp()) {
	// Next statement in body
	belowp->addNextHere(newp);
    } else {
	belowp->v3fatalSrc("Doesn't look like this was really under the while");
    }
}

//======================================================================
// Per-type Debugging

void AstNode::dump(ostream& str) {
    str<<typeName()<<" "<<(void*)this
	//<<" "<<(void*)this->m_backp
       <<" <e"<<dec<<editCount()
       <<((editCount()>=editCountLast())?"#>":">")
       <<" {"<<fileline()->filenameLetters()<<dec<<fileline()->lineno()<<"}"
       <<" "<<(isSigned()?"s":"")
       <<(isDouble()?"d":"")
       <<"w"<<(widthSized()?"":"u")<<width();
    if (!widthSized()) str<<"/"<<widthMin();
    if (name()!="") str<<"  "<<AstNode::quoteName(name());
}

void AstArrayDType::dump(ostream& str) {
    this->AstNodeDType::dump(str);
    if (isPacked()) str<<" [PACKED]";
}
void AstArraySel::dump(ostream& str) {
    this->AstNode::dump(str);
    str<<" [start:"<<start()<<"] [length:"<<length()<<"]";
}
void AstAttrOf::dump(ostream& str) {
    this->AstNode::dump(str);
    str<<" ["<<attrType().ascii()<<"]";
}
void AstBasicDType::dump(ostream& str) {
    this->AstNodeDType::dump(str);
    str<<" kwd="<<keyword().ascii();
    if (isRanged() && !rangep()) str<<" range=["<<msb()<<":"<<lsb()<<"]";
    if (implicit()) str<<" [IMPLICIT]";
}
void AstCCast::dump(ostream& str) {
    this->AstNode::dump(str);
    str<<" sz"<<size();
}
void AstCell::dump(ostream& str) {
    this->AstNode::dump(str);
    if (modp()) { str<<" -> "; modp()->dump(str); }
    else { str<<" ->UNLINKED:"<<modName(); }
}
void AstCellInline::dump(ostream& str) {
    this->AstNode::dump(str);
    str<<" -> "<<origModName();
}
void AstDisplay::dump(ostream& str) {
    this->AstNode::dump(str);
    //str<<" "<<displayType().ascii();
}
void AstJumpGo::dump(ostream& str) {
    this->AstNode::dump(str);
    str<<" -> ";
    if (labelp()) { labelp()->dump(str); }
    else { str<<"%Error:UNLINKED"; }
}
void AstEnumItemRef::dump(ostream& str) {
    this->AstNode::dump(str);
    str<<" -> ";
    if (itemp()) { itemp()->dump(str); }
    else { str<<"UNLINKED"; }
}
void AstPin::dump(ostream& str) {
    this->AstNode::dump(str);
    if (modVarp()) { str<<" -> "; modVarp()->dump(str); }
    else { str<<" ->UNLINKED"; }
    if (svImplicit()) str<<" [.SV]";
}
void AstRange::dump(ostream& str) {
    this->AstNode::dump(str);
    if (littleEndian()) str<<" [LITTLE]";
}
void AstRefDType::dump(ostream& str) {
    this->AstNodeDType::dump(str);
    if (defp()) { str<<" -> "; defp()->dump(str); }
    else { str<<" -> UNLINKED"; }
}
void AstVarXRef::dump(ostream& str) {
    this->AstNode::dump(str);
    if (lvalue()) str<<" [LV] => ";
    else          str<<" [RV] <- ";
    str<<dotted()<<". - ";
    if (inlinedDots()!="") str<<" flat.="<<inlinedDots()<<" - ";
    if (varScopep()) { varScopep()->dump(str); }
    else if (varp()) { varp()->dump(str); }
    else { str<<"UNLINKED"; }
}
void AstNodeDType::dump(ostream& str) {
    this->AstNode::dump(str);
}
void AstNodeModule::dump(ostream& str) {
    this->AstNode::dump(str);
    str<<"  L"<<level();
    if (modPublic()) str<<" [P]";
    if (inLibrary()) str<<" [LIB]";
}
void AstPackageImport::dump(ostream& str) {
    this->AstNode::dump(str);
    str<<" -> "<<packagep();
}
void AstVarScope::dump(ostream& str) {
    this->AstNode::dump(str);
    if (isCircular()) str<<" [CIRC]";
    if (varp()) { str<<" -> "; varp()->dump(str); }
    else { str<<" ->UNLINKED"; }
}
void AstVarRef::dump(ostream& str) {
    this->AstNode::dump(str);
    if (lvalue()) str<<" [LV] => ";
    else          str<<" [RV] <- ";
    if (varScopep()) { varScopep()->dump(str); }
    else if (varp()) { varp()->dump(str); }
    else { str<<"UNLINKED"; }
}
void AstVar::dump(ostream& str) {
    this->AstNode::dump(str);
    if (isSc()) str<<" [SC]";
    if (isPrimaryIO()) str<<(isInout()?" [PIO]":(isInput()?" [PI]":" [PO]"));
    else {
	if (isInout()) str<<" [IO]";
	else if (isInput()) str<<" [I]";
	else if (isOutput()) str<<" [O]";
    }
    if (isConst()) str<<" [CONST]";
    if (isUsedClock()) str<<" [CLK]";
    if (isSigPublic()) str<<" [P]";
    if (isUsedLoopIdx()) str<<" [LOOP]"; 
    if (attrClockEn()) str<<" [aCLKEN]";
    if (attrIsolateAssign()) str<<" [aISO]";
    if (attrFileDescr()) str<<" [aFD]";
    if (isFuncReturn()) str<<" [FUNCRTN]";
    else if (isFuncLocal()) str<<" [FUNC]";
    str<<" "<<varType();
}
void AstSenTree::dump(ostream& str) {
    this->AstNode::dump(str);
    if (isMulti()) str<<" [MULTI]";
}
void AstSenItem::dump(ostream& str) {
    this->AstNode::dump(str);
    str<<" ["<<edgeType().ascii()<<"]";
}
void AstParseRef::dump(ostream& str) {
    this->AstNode::dump(str);
    str<<" ["<<expect().ascii()<<"]";
}
void AstActive::dump(ostream& str) {
    this->AstNode::dump(str);
    str<<" => ";
    if (sensesp()) { sensesp()->dump(str); }
    else { str<<"UNLINKED"; }
}
void AstNodeFTaskRef::dump(ostream& str) {
    this->AstNode::dump(str);
    str<<" -> ";
    if (dotted()!="") { str<<dotted()<<". - "; }
    if (taskp()) { taskp()->dump(str); }
    else { str<<"UNLINKED"; }
}
void AstNodeFTask::dump(ostream& str) {
    this->AstNode::dump(str);
    if (taskPublic()) str<<" [PUBLIC]";
    if (prototype()) str<<" [PROTOTYPE]";
    if (dpiImport()) str<<" [DPII]";
    if (dpiExport()) str<<" [DPIX]";
    if ((dpiImport() || dpiExport()) && cname()!=name()) str<<" [c="<<cname()<<"]";
}
void AstBegin::dump(ostream& str) {
    this->AstNode::dump(str);
    if (unnamed()) str<<" [UNNAMED]";
    if (hidden()) str<<" [HIDDEN]";
}
void AstCoverDecl::dump(ostream& str) {
    this->AstNode::dump(str);
    if (this->dataDeclNullp()) {
	str<<" -> ";
	this->dataDeclNullp()->dump(str);
    } else {
	if (binNum()) { str<<" bin"<<dec<<binNum(); }
    }
}
void AstCoverInc::dump(ostream& str) {
    this->AstNode::dump(str);
    str<<" -> ";
    if (declp()) { declp()->dump(str); }
    else { str<<"%Error:UNLINKED"; }
}
void AstTraceInc::dump(ostream& str) {
    this->AstNode::dump(str);
    str<<" -> ";
    if (declp()) { declp()->dump(str); }
    else { str<<"%Error:UNLINKED"; }
}
void AstNodeText::dump(ostream& str) {
    this->AstNode::dump(str);
    string out = text();
    string::size_type pos;
    if ((pos = out.find("\n")) != string::npos) {
	out.erase(pos,out.length()-pos);
	out += "...";
    }
    str<<" \""<<out<<"\"";
}

void AstCFile::dump(ostream& str) {
    this->AstNode::dump(str);
    if (source()) str<<" [SRC]";
    if (slow()) str<<" [SLOW]";
}
void AstCCall::dump(ostream& str) {
    this->AstNode::dump(str);
    if (funcp()) {
	str<<" "<<funcp()->name()<<" => ";
	funcp()->dump(str);
    }
}
void AstCFunc::dump(ostream& str) {
    this->AstNode::dump(str);
    if (slow()) str<<" [SLOW]";
    if (pure()) str<<" [PURE]";
    if (dpiImport()) str<<" [DPII]";
    if (dpiExport()) str<<" [DPIX]";
    if (dpiExportWrapper()) str<<" [DPIXWR]";
}
