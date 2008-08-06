//*************************************************************************
// DESCRIPTION: Verilator: Ast node structures
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
    AstConst* constp=bitp()->castConst(); return (constp?constp->asInt():0);
}

bool AstVar::isSigPublic() const {
    return (m_sigPublic || (v3Global.opt.allPublic() && !isTemp()));
}

bool AstVar::isScQuad() const {
    return (isSc()&&isQuad()&&v3Global.opt.pins64());
}

bool AstVar::isScWide() const {
    return (isWide() || isSc()&&isQuad()&&!v3Global.opt.pins64());
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
    } else if (isScWide()) {
	return "uint32_t";  // []'s added later
    } else {
	return "uint64_t";
    }
}

string AstVar::scType() const {
    if (widthMin() == 1) {
	return "bool";
    } else if (widthMin() <= VL_WORDSIZE) {
	return "uint32_t";
    } else if (isScWide()) {
	return (string("sc_bv<")+cvtToStr(widthMin())+"> ");  // Keep the space so don't get >>
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

struct AstSenItemCmp {
    inline bool operator () (const AstSenItem* lhsp, const AstSenItem* rhsp) const {
	// Looks visually better if we keep sorted by name
	if (lhsp->edgeType() < rhsp->edgeType()) return true;
	if (lhsp->edgeType() > rhsp->edgeType()) return false;
	if (!lhsp->varrefp() &&  rhsp->varrefp()) return true;
	if ( lhsp->varrefp() && !rhsp->varrefp()) return false;
	if (lhsp->varrefp() && rhsp->varrefp()) {
	    if (lhsp->varrefp()->name() < rhsp->varrefp()->name()) return true;
	    if (lhsp->varrefp()->name() > rhsp->varrefp()->name()) return false;
	    // But might be same name with different scopes
	    if (lhsp->varrefp()->varScopep() < rhsp->varrefp()->varScopep()) return true;
	    if (lhsp->varrefp()->varScopep() > rhsp->varrefp()->varScopep()) return false;
	}
	return false;
    }
};

void AstSenTree::sortSenses() {
    // Sort the sensitivity names so "posedge a or b" and "posedge b or a" end up together.
    // Also, remove duplicate assignments, and fold POS&NEGs into ANYEDGEs
    //cout<<endl; this->dumpTree(cout,"ssin: ");
    AstSenItem* nextp;
    // Make things a little faster; check first if we need a sort
    for (AstSenItem* senp = sensesp(); senp; senp=senp->nextp()->castSenItem()) {
	nextp=senp->nextp()->castSenItem();
	AstSenItemCmp cmp;
	if (nextp && !cmp(senp, nextp)) {
	    // Something's out of order, sort it
	    senp = NULL;
	    vector<AstSenItem*> vec;
	    for (AstSenItem* senp = sensesp(); senp; senp=senp->nextp()->castSenItem()) {
		vec.push_back(senp);
	    }
	    sort(vec.begin(), vec.end(), AstSenItemCmp());
	    for (vector<AstSenItem*>::iterator it=vec.begin(); it!=vec.end(); ++it) {
		(*it)->unlinkFrBack();
	    }
	    for (vector<AstSenItem*>::iterator it=vec.begin(); it!=vec.end(); ++it) {
		this->addSensesp(*it);
	    }
	    break;
	}
    }

    // Pass2, remove dup edges
    for (AstSenItem* senp = sensesp(); senp; senp=nextp) {
	nextp=senp->nextp()->castSenItem();
	AstSenItem* cmpp = nextp;
	if (cmpp
	    && ((senp->varrefp() && cmpp->varrefp() && senp->varrefp()->sameTree(cmpp->varrefp()))
		|| (!senp->varrefp() && !cmpp->varrefp()))) {
	    // We've sorted in the order ANY, BOTH, POS, NEG, so we don't need to try opposite orders
	    if ((   senp->edgeType()==AstEdgeType::ANYEDGE)    // ANY  or {BOTH|POS|NEG} -> ANY
		|| (senp->edgeType()==AstEdgeType::BOTHEDGE)   // BOTH or {POS|NEG} -> BOTH
		|| (senp->edgeType()==AstEdgeType::POSEDGE     // POS  or NEG -> BOTH
		    && cmpp->edgeType()==AstEdgeType::NEGEDGE)
		|| (senp->edgeType()==cmpp->edgeType())		// Identical edges
		) {
		// Fix edge of old node
		if (senp->edgeType()==AstEdgeType::POSEDGE
		    && cmpp->edgeType()==AstEdgeType::NEGEDGE)
		    senp->edgeType(AstEdgeType::BOTHEDGE);
		// Remove redundant node
		cmpp->unlinkFrBack()->deleteTree(); cmpp=NULL;
		// Try to collapse again
		nextp=senp;
	    }
	}
    }

    // Pass3, remove nevers
    if (sensesp()->nextp()) {   // Else only one never, can't remove it
	for (AstSenItem* senp = sensesp(); senp; senp=nextp) {
	    nextp=senp->nextp()->castSenItem();
	    if (senp->isNever()) {
		senp->unlinkFrBack()->deleteTree(); senp=NULL;
	    }
	}
    }
    //this->dumpTree(cout,"ssou: ");
}

bool AstSenTree::hasClocked() {
    if (!sensesp()) this->v3fatalSrc("SENTREE without any SENITEMs under it");
    for (AstSenItem* senp = sensesp(); senp; senp=senp->nextp()->castSenItem()) {
	if (senp->isClocked()) return true;
    }
    return false;
}
bool AstSenTree::hasSettle() {
    if (!sensesp()) this->v3fatalSrc("SENTREE without any SENITEMs under it");
    for (AstSenItem* senp = sensesp(); senp; senp=senp->nextp()->castSenItem()) {
	if (senp->isSettle()) return true;
    }
    return false;
}
bool AstSenTree::hasInitial() {
    if (!sensesp()) this->v3fatalSrc("SENTREE without any SENITEMs under it");
    for (AstSenItem* senp = sensesp(); senp; senp=senp->nextp()->castSenItem()) {
	if (senp->isInitial()) return true;
    }
    return false;
}
bool AstSenTree::hasCombo() {
    if (!sensesp()) this->v3fatalSrc("SENTREE without any SENITEMs under it");
    for (AstSenItem* senp = sensesp(); senp; senp=senp->nextp()->castSenItem()) {
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
void AstCast::dump(ostream& str) {
    this->AstNode::dump(str);
    str<<" sz"<<size();
}
void AstCell::dump(ostream& str) {
    this->AstNode::dump(str);
    if (modp()) { str<<" -> "; modp()->dump(str); }
    else { str<<" ->UNLINKED:"<<modName(); }
    if (pinStar()) str<<" [.*]";
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
