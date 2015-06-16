// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Ast node structures
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
const char* AstIfaceRefDType::broken() const {
    BROKEN_RTN(m_ifacep && !m_ifacep->brokeExists());
    BROKEN_RTN(m_cellp && !m_cellp->brokeExists());
    BROKEN_RTN(m_modportp && !m_modportp->brokeExists());
    return NULL;
}

AstIface* AstIfaceRefDType::ifaceViaCellp() const {
    return ((m_cellp && m_cellp->modp()) ? m_cellp->modp()->castIface() : m_ifacep);
}

const char* AstNodeVarRef::broken() const {
    BROKEN_RTN(m_varScopep && !m_varScopep->brokeExists());
    BROKEN_RTN(m_varp && !m_varp->brokeExists());
    return NULL;
}

void AstNodeVarRef::cloneRelink() {
    if (m_varp && m_varp->clonep()) { m_varp = m_varp->clonep()->castVar(); }
}

int AstNodeSel::bitConst() const {
    AstConst* constp=bitp()->castConst(); return (constp?constp->toSInt():0);
}

void AstNodeClassDType::repairMemberCache() {
    clearCache();
    for (AstMemberDType* itemp = membersp(); itemp; itemp=itemp->nextp()->castMemberDType()) {
	if (m_members.find(itemp->name())!=m_members.end()) { itemp->v3error("Duplicate declaration of member name: "<<itemp->prettyName()); }
	else m_members.insert(make_pair(itemp->name(), itemp));
    }
}

const char* AstNodeClassDType::broken() const {
    set<AstMemberDType*> exists;
    for (AstMemberDType* itemp = membersp(); itemp; itemp=itemp->nextp()->castMemberDType()) {
	exists.insert(itemp);
    }
    for (MemberNameMap::const_iterator it=m_members.begin(); it!=m_members.end(); ++it) {
	if (VL_UNLIKELY(exists.find(it->second) == exists.end())) {
	    this->v3error("Internal: Structure member broken: "<<it->first);
	    return "member broken";
	}
    }
    return NULL;
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

int AstNodeClassDType::widthTotalBytes() const {
    if (width()<=8) return 1;
    else if (width()<=16) return 2;
    else if (isQuad()) return 8;
    else return widthWords()*(VL_WORDSIZE/8);
}

int AstNodeClassDType::widthAlignBytes() const {
    // Could do max across members but that would be slow,
    // instead intuit based on total structure size
    if (width()<=8) return 1;
    else if (width()<=16) return 2;
    else if (width()<=32) return 4;
    else return 8;
}

AstNodeBiop* AstEq::newTyped(FileLine* fl, AstNode* lhsp, AstNode* rhsp) {
    if (lhsp->isDouble() && rhsp->isDouble()) {
	return new AstEqD(fl, lhsp, rhsp);
    } else {
	return new AstEq(fl, lhsp, rhsp);
    }
}

AstNodeBiop* AstGte::newTyped(FileLine* fl, AstNode* lhsp, AstNode* rhsp) {
    if (lhsp->isDouble() && rhsp->isDouble()) {
	return new AstGteD(fl, lhsp, rhsp);
    } else if (lhsp->isSigned() && rhsp->isSigned()) {
	return new AstGteS(fl, lhsp, rhsp);
    } else {
	return new AstGte(fl, lhsp, rhsp);
    }
}

AstNodeBiop* AstLte::newTyped(FileLine* fl, AstNode* lhsp, AstNode* rhsp) {
    if (lhsp->isDouble() && rhsp->isDouble()) {
	return new AstLteD(fl, lhsp, rhsp);
    } else if (lhsp->isSigned() && rhsp->isSigned()) {
	return new AstLteS(fl, lhsp, rhsp);
    } else {
	return new AstLte(fl, lhsp, rhsp);
    }
}


bool AstVar::isSigPublic() const {
    return (m_sigPublic || (v3Global.opt.allPublic() && !isTemp() && !isGenVar()));
}

bool AstVar::isScQuad() const {
    return (isSc() && isQuad() && !isScBv() && !isScBigUint());
}

bool AstVar::isScBv() const {
    return ((isSc() && width() >= v3Global.opt.pinsBv()) || m_attrScBv);
}

bool AstVar::isScUint() const {
    return ((isSc() && v3Global.opt.pinsScUint() && width() >= 2 && width() <= 64) && !isScBv());
}

bool AstVar::isScBigUint() const {
    return ((isSc() && v3Global.opt.pinsScBigUint() && width() >= 65 && width() <= 512) && !isScBv());
}

void AstVar::combineType(AstVarType type) {
    // These flags get combined with the existing settings of the flags.
    // We don't test varType for certain types, instead set flags since
    // when we combine wires cross-hierarchy we need a union of all characteristics.
    if (type == AstVarType::SUPPLY0) type = AstVarType::WIRE;
    if (type == AstVarType::SUPPLY1) type = AstVarType::WIRE;
    m_varType=type; 	// For debugging prints only
    // These flags get combined with the existing settings of the flags.
    if (type==AstVarType::INPUT || type==AstVarType::INOUT)
	m_input = true;
    if (type==AstVarType::OUTPUT || type==AstVarType::INOUT) {
	m_output = true;
	m_declOutput = true;
    }
    if (type==AstVarType::INOUT || type==AstVarType::TRIWIRE
	|| type==AstVarType::TRI0 || type==AstVarType::TRI1)
	m_tristate = true;
    if (type==AstVarType::TRI0)
	m_isPulldown = true;
    if (type==AstVarType::TRI1)
	m_isPullup = true;
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

string AstVar::vlArgType(bool named, bool forReturn, bool forFunc) const {
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
	if (forFunc && (isOutput() || (strtype && isInput()))) arg += "&";
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
	if (basicp()->keyword().isDpiUnsignable() && !basicp()->isSigned()) {
	    arg = "unsigned "+arg;
	}
	if (!forReturn && isOutput()) arg += "*";
    }
    if (named) arg += " "+name();
    return arg;
}

string AstVar::scType() const {
    if (isScBigUint()) {
	return (string("sc_biguint<")+cvtToStr(widthMin())+"> ");  // Keep the space so don't get >>
    } else if (isScUint()) {
	return (string("sc_uint<")+cvtToStr(widthMin())+"> ");  // Keep the space so don't get >>
    } else if (isScBv()) {
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

AstVar* AstVar::scVarRecurse(AstNode* nodep) {
    // See if this is a SC assignment; if so return that type
    // Historically sc variables are identified by a variable
    // attribute. TODO it would better be a data type attribute.
    if (AstVar* anodep = nodep->castVar()) {
	if (anodep->isSc()) return anodep;
	else return NULL;
    }
    else if (nodep->castVarRef()) {
	if (nodep->castVarRef()->varp()->isSc()) return nodep->castVarRef()->varp();
	else return NULL;
    }
    else if (nodep->castArraySel()) {
	if (nodep->op1p()) if (AstVar* p = scVarRecurse(nodep->op1p())) return p;
	if (nodep->op2p()) if (AstVar* p = scVarRecurse(nodep->op2p())) return p;
	if (nodep->op3p()) if (AstVar* p = scVarRecurse(nodep->op3p())) return p;
	if (nodep->op4p()) if (AstVar* p = scVarRecurse(nodep->op4p())) return p;
    }
    return NULL;
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
    // TODO this function should be removed in favor of recursing the dtype(),
    // as that allows for more complicated data types.
    int dim = 0;
    for (AstNodeDType* dtypep=this; dtypep; ) {
	dtypep = dtypep->skipRefp();  // Skip AstRefDType/AstTypedef, or return same node
	if (AstNodeArrayDType* adtypep = dtypep->castNodeArrayDType()) {
	    if ((dim++)==dimension) {
		return dtypep;
	    }
	    dtypep = adtypep->subDTypep();
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
	else if (AstNodeClassDType* adtypep = dtypep->castNodeClassDType()) {
	    if (adtypep->packed()) {
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

uint32_t AstNodeDType::arrayUnpackedElements() {
    uint32_t entries=1;
    for (AstNodeDType* dtypep=this; dtypep; ) {
	dtypep = dtypep->skipRefp();  // Skip AstRefDType/AstTypedef, or return same node
	if (AstUnpackArrayDType* adtypep = dtypep->castUnpackArrayDType()) {
	    entries *= adtypep->elementsConst();
	    dtypep = adtypep->subDTypep();
	}
	else {
	    // AstBasicDType - nothing below, 1
	    break;
	}
    }
    return entries;
}

pair<uint32_t,uint32_t> AstNodeDType::dimensions(bool includeBasic) {
    // How many array dimensions (packed,unpacked) does this Var have?
    uint32_t packed = 0;
    uint32_t unpacked = 0;
    for (AstNodeDType* dtypep=this; dtypep; ) {
	dtypep = dtypep->skipRefp();  // Skip AstRefDType/AstTypedef, or return same node
	if (AstNodeArrayDType* adtypep = dtypep->castNodeArrayDType()) {
	    if (adtypep->castPackArrayDType()) packed++;
	    else unpacked++;
	    dtypep = adtypep->subDTypep();
	    continue;
	}
	else if (AstBasicDType* adtypep = dtypep->castBasicDType()) {
	    if (includeBasic && adtypep->isRanged()) packed++;
	}
	break;
    }
    return make_pair(packed, unpacked);
}

int AstNodeDType::widthPow2() const {
    // I.e.  width 30 returns 32, width 32 returns 32.
    uint32_t width = this->width();
    for (int p2=30; p2>=0; p2--) {
	if (width > (1UL<<p2)) return (1UL<<(p2+1));
    }
    return 1;
}

AstNode* AstArraySel::baseFromp(AstNode* nodep) {	///< What is the base variable (or const) this dereferences?
    // Else AstArraySel etc; search for the base
    while (nodep) {
	if (nodep->castArraySel()) { nodep=nodep->castArraySel()->fromp(); continue; }
	else if (nodep->castSel()) { nodep=nodep->castSel()->fromp(); continue; }
	// AstNodeSelPre stashes the associated variable under an ATTROF of AstAttrType::VAR_BASE/MEMBER_BASE so it isn't constified
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

const char* AstScope::broken() const {
    BROKEN_RTN(m_aboveScopep && !m_aboveScopep->brokeExists());
    BROKEN_RTN(m_aboveCellp && !m_aboveCellp->brokeExists());
    BROKEN_RTN(!m_modp);
    BROKEN_RTN(m_modp && !m_modp->brokeExists());
    return NULL;
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

string AstScopeName::scopePrettyNameFormatter(AstText* scopeTextp) const {
    string out;
    for (AstText* textp=scopeTextp; textp; textp=textp->nextp()->castText()) {
	out += textp->text();
    }
    // TOP will be replaced by top->name()
    if (out.substr(0,10) == "__DOT__TOP") out.replace(0,10,"");
    if (out.substr(0,7) == "__DOT__") out.replace(0,7,"");
    if (out.substr(0,1) == ".") out.replace(0,1,"");
    return AstNode::prettyName(out);
}

string AstScopeName::scopeNameFormatter(AstText* scopeTextp) const {
    string out;
    for (AstText* textp=scopeTextp; textp; textp=textp->nextp()->castText()) {
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

void AstTypeTable::clearCache() {
    // When we mass-change widthMin in V3WidthCommit, we need to correct the table.
    // Just clear out the maps; the search functions will be used to rebuild the map
    for (int i=0; i<(int)(AstBasicDTypeKwd::_ENUM_MAX); ++i) {
	m_basicps[i] = NULL;
    }
    for (int isbit=0; isbit<_IDX0_MAX; ++isbit) {
	for (int numer=0; numer<AstNumeric::_ENUM_MAX; ++numer) {
	    LogicMap& mapr = m_logicMap[isbit][numer];
	    mapr.clear();
	}
    }
    m_detailedMap.clear();
    // Clear generic()'s so dead detection will work
    for (AstNode* nodep = typesp(); nodep; nodep=nodep->nextp()) {
	if (AstBasicDType* bdtypep = nodep->castBasicDType()) {
	    bdtypep->generic(false);
	}
    }
}

void AstTypeTable::repairCache() {
    // After we mass-change widthMin in V3WidthCommit, we need to correct the table.
    clearCache();
    for (AstNode* nodep = typesp(); nodep; nodep=nodep->nextp()) {
	if (AstBasicDType* bdtypep = nodep->castBasicDType()) {
	    (void)findInsertSameDType(bdtypep);
	}
    }
}

AstBasicDType* AstTypeTable::findBasicDType(FileLine* fl, AstBasicDTypeKwd kwd) {
    if (m_basicps[kwd]) return m_basicps[kwd];
    //
    AstBasicDType* new1p = new AstBasicDType(fl, kwd);
    // Because the detailed map doesn't update this map,
    // check the detailed map for this same node
    // Also adds this new node to the detailed map
    AstBasicDType* newp = findInsertSameDType(new1p);
    if (newp != new1p) new1p->deleteTree();
    else addTypesp(newp);
    //
    m_basicps[kwd] = newp;
    return newp;
}

AstBasicDType* AstTypeTable::findLogicBitDType(FileLine* fl, AstBasicDTypeKwd kwd,
					       int width, int widthMin, AstNumeric numeric) {
    int idx = IDX0_LOGIC;
    if (kwd == AstBasicDTypeKwd::LOGIC) idx = IDX0_LOGIC;
    else if (kwd == AstBasicDTypeKwd::BIT) idx = IDX0_BIT;
    else fl->v3fatalSrc("Bad kwd for findLogicBitDType");
    pair<int,int> widths = make_pair(width,widthMin);
    LogicMap& mapr = m_logicMap[idx][(int)numeric];
    LogicMap::const_iterator it = mapr.find(widths);
    if (it != mapr.end()) return it->second;
    //
    AstBasicDType* new1p = new AstBasicDType(fl, kwd, numeric, width, widthMin);
    // Because the detailed map doesn't update this map,
    // check the detailed map for this same node, and if found update this map
    // Also adds this new node to the detailed map
    AstBasicDType* newp = findInsertSameDType(new1p);
    if (newp != new1p) new1p->deleteTree();
    else addTypesp(newp);
    //
    mapr.insert(make_pair(widths,newp));
    return newp;
}

AstBasicDType* AstTypeTable::findLogicBitDType(FileLine* fl, AstBasicDTypeKwd kwd,
					       VNumRange range, int widthMin, AstNumeric numeric) {
    AstBasicDType* new1p = new AstBasicDType(fl, kwd, numeric, range, widthMin);
    AstBasicDType* newp = findInsertSameDType(new1p);
    if (newp != new1p) new1p->deleteTree();
    else addTypesp(newp);
    return newp;
}

AstBasicDType* AstTypeTable::findInsertSameDType(AstBasicDType* nodep) {
    VBasicTypeKey key (nodep->width(), nodep->widthMin(), nodep->numeric(),
		       nodep->keyword(), nodep->nrange());
    DetailedMap& mapr = m_detailedMap;
    DetailedMap::const_iterator it = mapr.find(key);
    if (it != mapr.end()) return it->second;
    mapr.insert(make_pair(key,nodep));
    nodep->generic(true);
    // No addTypesp; the upper function that called new() is responsible for adding
    return nodep;
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
       <<" {"<<fileline()->filenameLetters()<<dec<<fileline()->lineno()<<"}";
    if (user1p()) str<<" u1="<<(void*)user1p();
    if (user2p()) str<<" u2="<<(void*)user2p();
    if (user3p()) str<<" u3="<<(void*)user3p();
    if (user4p()) str<<" u4="<<(void*)user4p();
    if (user5p()) str<<" u5="<<(void*)user5p();
    if (hasDType()) {
	if (dtypep()==this) str<<" @dt="<<"this@";
	else str<<" @dt="<<(void*)dtypep()<<"@";  // Final @ so less likely to by accident think it's nodep
	if (AstNodeDType* dtp = dtypep()) {
	    dtp->dumpSmall(str);
	}
    } else { // V3Broken will throw an error
	if (dtypep()) str<<" %Error-dtype-exp=null,got="<<(void*)dtypep();
    }
    if (name()!="") {
	if (castConst()) str<<"  "<<name();  // Already quoted
	else str<<"  "<<V3Number::quoteNameControls(name());
    }
}

void AstAlways::dump(ostream& str) {
    this->AstNode::dump(str);
    if (keyword() != VAlwaysKwd::ALWAYS) str<<" ["<<keyword().ascii()<<"]";
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
    if (isRanged() && !rangep()) str<<" range=["<<left()<<":"<<right()<<"]";
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
void AstEnumItemRef::dump(ostream& str) {
    this->AstNode::dump(str);
    str<<" -> ";
    if (itemp()) { itemp()->dump(str); }
    else { str<<"UNLINKED"; }
}
void AstIfaceRefDType::dump(ostream& str) {
    this->AstNode::dump(str);
    if (cellName()!="") { str<<" cell="<<cellName(); }
    if (ifaceName()!="") { str<<" if="<<ifaceName(); }
    if (modportName()!="") { str<<" mp="<<modportName(); }
    if (cellp()) { str<<" -> "; cellp()->dump(str); }
    else if (ifacep()) { str<<" -> "; ifacep()->dump(str); }
    else { str<<" -> UNLINKED"; }
}
void AstIfaceRefDType::dumpSmall(ostream& str) {
    this->AstNodeDType::dumpSmall(str);
    str<<"iface";
}
void AstJumpGo::dump(ostream& str) {
    this->AstNode::dump(str);
    str<<" -> ";
    if (labelp()) { labelp()->dump(str); }
    else { str<<"%Error:UNLINKED"; }
}
void AstModportFTaskRef::dump(ostream& str) {
    this->AstNode::dump(str);
    if (isExport()) str<<" EXPORT";
    if (isImport()) str<<" IMPORT";
    if (ftaskp()) { str<<" -> "; ftaskp()->dump(str); }
    else { str<<" -> UNLINKED"; }
}
void AstModportVarRef::dump(ostream& str) {
    this->AstNode::dump(str);
    str<<" "<<varType();
    if (varp()) { str<<" -> "; varp()->dump(str); }
    else { str<<" -> UNLINKED"; }
}
void AstPin::dump(ostream& str) {
    this->AstNode::dump(str);
    if (modVarp()) { str<<" -> "; modVarp()->dump(str); }
    else { str<<" ->UNLINKED"; }
    if (svImplicit()) str<<" [.SV]";
}
void AstTypedef::dump(ostream& str) {
    this->AstNode::dump(str);
    if (attrPublic()) str<<" [PUBLIC]";
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
void AstNodeClassDType::dump(ostream& str) {
    this->AstNode::dump(str);
    if (packed()) str<<" [PACKED]";
}
void AstNodeDType::dump(ostream& str) {
    this->AstNode::dump(str);
    if (generic()) str<<" [GENERIC]";
    if (AstNodeDType* dtp = virtRefDTypep()) {
	str<<" refdt="<<(void*)(dtp);
	dtp->dumpSmall(str);
    }
}
void AstNodeDType::dumpSmall(ostream& str) {
    str<<"("
       <<(generic()?"G/":"")
       <<((isSigned()&&!isDouble())?"s":"")
       <<(isNosign()?"n":"")
       <<(isDouble()?"d":"")
       <<(isString()?"str":"");
    if (!isDouble() && !isString()) {
	str<<"w"<<(widthSized()?"":"u")<<width();
    }
    if (!widthSized()) str<<"/"<<widthMin();
    str<<")";
}
void AstNodeArrayDType::dumpSmall(ostream& str) {
    this->AstNodeDType::dumpSmall(str);
    if (castPackArrayDType()) str<<"p"; else str<<"u";
    str<<declRange();
}
void AstNodeArrayDType::dump(ostream& str) {
    this->AstNodeDType::dump(str);
    str<<" "<<declRange();
}
void AstNodeModule::dump(ostream& str) {
    this->AstNode::dump(str);
    str<<"  L"<<level();
    if (modPublic()) str<<" [P]";
    if (inLibrary()) str<<" [LIB]";
    if (dead()) str<<" [DEAD]";
}
void AstPackageImport::dump(ostream& str) {
    this->AstNode::dump(str);
    str<<" -> "<<packagep();
}
void AstSel::dump(ostream& str) {
    this->AstNode::dump(str);
    if (declRange().ranged()) {
	str<<" decl"<<declRange()<<"]";
	if (declElWidth()!=1) str<<"/"<<declElWidth();
    }
}
void AstTypeTable::dump(ostream& str) {
    this->AstNode::dump(str);
    for (int i=0; i<(int)(AstBasicDTypeKwd::_ENUM_MAX); ++i) {
	if (AstBasicDType* subnodep=m_basicps[i]) {
	    str<<endl;  // Newline from caller, so newline first
	    str<<"\t\t"<<setw(8)<<AstBasicDTypeKwd(i).ascii();
	    str<<"  -> ";
	    subnodep->dump(str);
	}
    }
    for (int isbit=0; isbit<2; ++isbit) {
	for (int issigned=0; issigned<AstNumeric::_ENUM_MAX; ++issigned) {
	    LogicMap& mapr = m_logicMap[isbit][issigned];
	    for (LogicMap::const_iterator it = mapr.begin(); it != mapr.end(); ++it) {
		AstBasicDType* dtypep = it->second;
		str<<endl;  // Newline from caller, so newline first
		stringstream nsstr;
		nsstr<<(isbit?"bw":"lw")
		     <<it->first.first<<"/"<<it->first.second;
		str<<"\t\t"<<setw(8)<<nsstr.str();
		if (issigned) str<<" s"; else str<<" u";
		str<<"  ->  ";
		dtypep->dump(str);
	    }
	}
    }
    {
	DetailedMap& mapr = m_detailedMap;
	for (DetailedMap::const_iterator it = mapr.begin(); it != mapr.end(); ++it) {
	    AstBasicDType* dtypep = it->second;
	    str<<endl;  // Newline from caller, so newline first
	    str<<"\t\tdetailed  ->  ";
	    dtypep->dump(str);
	}
    }
    // Note get newline from caller too.
}

void AstVarScope::dump(ostream& str) {
    this->AstNode::dump(str);
    if (isCircular()) str<<" [CIRC]";
    if (varp()) { str<<" -> "; varp()->dump(str); }
    else { str<<" ->UNLINKED"; }
}
void AstVarXRef::dump(ostream& str) {
    this->AstNode::dump(str);
    if (packagep()) { str<<" pkg="<<(void*)packagep(); }
    if (lvalue()) str<<" [LV] => ";
    else          str<<" [RV] <- ";
    str<<dotted()<<". - ";
    if (inlinedDots()!="") str<<" inline.="<<inlinedDots()<<" - ";
    if (varScopep()) { varScopep()->dump(str); }
    else if (varp()) { varp()->dump(str); }
    else { str<<"UNLINKED"; }
}
void AstVarRef::dump(ostream& str) {
    this->AstNode::dump(str);
    if (packagep()) { str<<" pkg="<<(void*)packagep(); }
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
    if (isPullup()) str<<" [PULLUP]";
    if (isPulldown()) str<<" [PULLDOWN]";
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
void AstPackageRef::dump(ostream& str) {
    this->AstNode::dump(str);
    if (packagep()) { str<<" pkg="<<(void*)packagep(); }
    str<<" -> ";
    if (packagep()) { packagep()->dump(str); }
    else { str<<"UNLINKED"; }
}
void AstDot::dump(ostream& str) {
    this->AstNode::dump(str);
}
void AstActive::dump(ostream& str) {
    this->AstNode::dump(str);
    str<<" => ";
    if (sensesp()) { sensesp()->dump(str); }
    else { str<<"UNLINKED"; }
}
void AstNodeFTaskRef::dump(ostream& str) {
    this->AstNode::dump(str);
    if (packagep()) { str<<" pkg="<<(void*)packagep(); }
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
    if (generate()) str<<" [GEN]";
    if (genforp()) str<<" [GENFOR]";
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
