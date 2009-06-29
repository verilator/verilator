//*************************************************************************
// DESCRIPTION: Verilator: Ast node structures
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2009 by Wilson Snyder.  This program is free software; you can
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

bool AstVar::isSigPublic() const {
    return (m_sigPublic || (v3Global.opt.allPublic() && !isTemp() && !isGenVar()));
}

bool AstVar::isScQuad() const {
    return (isSc() && isQuad() && !isScBv());
}

bool AstVar::isScBv() const {
    return (isSc() && width() >= v3Global.opt.pinsBv());
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

int AstVar::widthAlignBytes() const {
    if (width()<=8) return 1;
    else if (width()<=16) return 2;
    else if (isSc() ? isScQuad() : isQuad()) return 8;
    else return 4;
}

int AstVar::widthTotalBytes() const {
    if (width()<=8) return 1;
    else if (width()<=16) return 2;
    else if (isSc() ? isScQuad() : isQuad()) return 8;
    else return widthWords()*(VL_WORDSIZE/8);
}

string AstVar::verilogKwd() const {
    if (isInout()) {
	return "inout";
    } else if (isInput()) {
	return "input";
    } else if (isOutput()) {
	return "output";
    } else if (isInteger()) {
	return "integer";
    } else if (isTristate()) {
	return "tri";
    } else if (varType()==AstVarType::WIRE) {
	return "wire";
    } else {
	return "reg";
    }
}

string AstVar::cType() const {
    if (widthMin() == 1) {
	return "bool";
    } else if (widthMin() <= VL_WORDSIZE) {
	return "uint32_t";
    } else if (isWide()) {
	return "uint32_t";  // []'s added later
    } else {
	return "uint64_t";
    }
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
	return "uint64_t";
    }
}

AstRange* AstVar::arrayp(int dimension) const {
    for (AstRange* arrayp=this->arraysp(); arrayp; arrayp = arrayp->nextp()->castRange()) {
	if ((dimension--)==0) return arrayp;
    }
    return NULL;
}

uint32_t AstVar::arrayElements() const {
    uint32_t entries=1;
    for (AstRange* arrayp=this->arraysp(); arrayp; arrayp = arrayp->nextp()->castRange()) {
	entries *= arrayp->elementsConst();
    }
    return entries;
}

bool AstScope::broken() const {
    return ((m_aboveScopep && !m_aboveScopep->brokeExists())
	    || (m_aboveCellp && !m_aboveCellp->brokeExists())
	    || !m_modp || !m_modp->brokeExists());
}

void AstScope::cloneRelink() {
    if (m_aboveScopep && m_aboveScopep->clonep()) m_aboveScopep->clonep()->castScope();
    if (m_aboveCellp && m_aboveCellp->clonep()) m_aboveCellp->clonep()->castCell();
    if (m_modp && ((AstNode*)m_modp)->clonep()) ((AstNode*)m_modp)->clonep()->castModule();
}

string AstScope::nameDotless() const {
    string dotless = shortName();
    string::size_type pos;
    while ((pos=dotless.find(".")) != string::npos) {
	dotless.replace(pos, 1, "__");
    }
    return dotless;
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
// Per-type Debugging

void AstNode::dump(ostream& os) {
    os<<typeName()<<" "<<(void*)this
	//<<" "<<(void*)this->m_backp
      <<" <e"<<dec<<editCount()
      <<((editCount()>=editCountLast())?"#>":">")
      <<" {"<<dec<<fileline()->lineno()<<"}"
      <<" "<<(isSigned()?"s":"")
      <<"w"<<(widthSized()?"":"u")<<width();
    if (!widthSized()) os<<"/"<<widthMin();
    if (name()!="") os<<"  "<<name();
}

void AstAttrOf::dump(ostream& str) {
    this->AstNode::dump(str);
    str<<" ["<<attrType().ascii()<<"]";
}
void AstCast::dump(ostream& str) {
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
void AstPin::dump(ostream& str) {
    this->AstNode::dump(str);
    if (modVarp()) { str<<" -> "; modVarp()->dump(str); }
    else { str<<" ->UNLINKED"; }
    if (svImplicit()) str<<" [.SV]";
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
void AstModule::dump(ostream& str) {
    this->AstNode::dump(str);
    str<<"  L"<<level();
    if (modPublic()) str<<" [P]";
    if (inLibrary()) str<<" [LIB]";
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
    if (isUsedClock()) str<<" [C]";
    if (isSigPublic()) str<<" [P]";
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
}
