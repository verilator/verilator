// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Ast node structures
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3File.h"
#include "V3Global.h"
#include "V3Graph.h"
#include "V3PartitionGraph.h"  // Just for mtask dumping
#include "V3EmitCBase.h"

#include <cstdarg>
#include <iomanip>
#include <vector>

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
    return ((m_cellp && m_cellp->modp()) ? VN_CAST(m_cellp->modp(), Iface) : m_ifacep);
}

const char* AstNodeVarRef::broken() const {
    BROKEN_RTN(m_varScopep && !m_varScopep->brokeExists());
    BROKEN_RTN(m_varp && !m_varp->brokeExists());
    return NULL;
}

void AstNodeVarRef::cloneRelink() {
    if (m_varp && m_varp->clonep()) { m_varp = m_varp->clonep(); }
}

string AstNodeVarRef::hiernameProtect() const {
    return VIdProtect::protectWordsIf(hiername(), protect());
}

int AstNodeSel::bitConst() const {
    AstConst* constp = VN_CAST(bitp(), Const);
    return (constp ? constp->toSInt() : 0);
}

void AstNodeUOrStructDType::repairMemberCache() {
    clearCache();
    for (AstMemberDType* itemp = membersp(); itemp; itemp = VN_CAST(itemp->nextp(), MemberDType)) {
        if (m_members.find(itemp->name()) != m_members.end()) {
            itemp->v3error("Duplicate declaration of member name: " << itemp->prettyNameQ());
        } else {
            m_members.insert(make_pair(itemp->name(), itemp));
        }
    }
}

const char* AstNodeUOrStructDType::broken() const {
    vl_unordered_set<AstMemberDType*> exists;
    for (AstMemberDType* itemp = membersp(); itemp; itemp = VN_CAST(itemp->nextp(), MemberDType)) {
        exists.insert(itemp);
    }
    for (MemberNameMap::const_iterator it = m_members.begin(); it != m_members.end(); ++it) {
        if (VL_UNCOVERABLE(exists.find(it->second) == exists.end())) {
            this->v3error("Internal: Structure member broken: " << it->first);
            return "member broken";
        }
    }
    return NULL;
}

void AstNodeCCall::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (funcp()) {
        str << " " << funcp()->name() << " => ";
        funcp()->dump(str);
    } else {
        str << " " << name();
    }
}
void AstNodeCCall::cloneRelink() {
    if (m_funcp && m_funcp->clonep()) { m_funcp = m_funcp->clonep(); }
}
const char* AstNodeCCall::broken() const {
    BROKEN_RTN(m_funcp && !m_funcp->brokeExists());
    return NULL;
}
bool AstNodeCCall::isPure() const { return funcp()->pure(); }
string AstNodeCCall::hiernameProtect() const {
    return VIdProtect::protectWordsIf(hiername(), protect());
}

void AstNodeCond::numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs,
                                const V3Number& ths) {
    if (lhs.isNeqZero()) {
        out.opAssign(rhs);
    } else {
        out.opAssign(ths);
    }
}

int AstBasicDType::widthAlignBytes() const {
    if (width() <= 8) {
        return 1;
    } else if (width() <= 16) {
        return 2;
    } else if (isQuad()) {
        return 8;
    } else {
        return 4;
    }
}

int AstBasicDType::widthTotalBytes() const {
    if (width() <= 8) {
        return 1;
    } else if (width() <= 16) {
        return 2;
    } else if (isQuad()) {
        return 8;
    } else {
        return widthWords() * (VL_EDATASIZE / 8);
    }
}

int AstNodeUOrStructDType::widthTotalBytes() const {
    if (width() <= 8) {
        return 1;
    } else if (width() <= 16) {
        return 2;
    } else if (isQuad()) {
        return 8;
    } else {
        return widthWords() * (VL_EDATASIZE / 8);
    }
}

int AstNodeUOrStructDType::widthAlignBytes() const {
    // Could do max across members but that would be slow,
    // instead intuit based on total structure size
    if (width() <= 8) {
        return 1;
    } else if (width() <= 16) {
        return 2;
    } else if (width() <= 32) {
        return 4;
    } else {
        return 8;
    }
}

AstNodeBiop* AstEq::newTyped(FileLine* fl, AstNode* lhsp, AstNode* rhsp) {
    if (lhsp->isString() && rhsp->isString()) {
        return new AstEqN(fl, lhsp, rhsp);
    } else if (lhsp->isDouble() && rhsp->isDouble()) {
        return new AstEqD(fl, lhsp, rhsp);
    } else {
        return new AstEq(fl, lhsp, rhsp);
    }
}

AstNodeBiop* AstGte::newTyped(FileLine* fl, AstNode* lhsp, AstNode* rhsp) {
    if (lhsp->isString() && rhsp->isString()) {
        return new AstGteN(fl, lhsp, rhsp);
    } else if (lhsp->isDouble() && rhsp->isDouble()) {
        return new AstGteD(fl, lhsp, rhsp);
    } else if (lhsp->isSigned() && rhsp->isSigned()) {
        return new AstGteS(fl, lhsp, rhsp);
    } else {
        return new AstGte(fl, lhsp, rhsp);
    }
}

AstNodeBiop* AstLte::newTyped(FileLine* fl, AstNode* lhsp, AstNode* rhsp) {
    if (lhsp->isString() && rhsp->isString()) {
        return new AstLteN(fl, lhsp, rhsp);
    } else if (lhsp->isDouble() && rhsp->isDouble()) {
        return new AstLteD(fl, lhsp, rhsp);
    } else if (lhsp->isSigned() && rhsp->isSigned()) {
        return new AstLteS(fl, lhsp, rhsp);
    } else {
        return new AstLte(fl, lhsp, rhsp);
    }
}

AstNodeBiop* AstEqWild::newTyped(FileLine* fl, AstNode* lhsp, AstNode* rhsp) {
    if (lhsp->isString() && rhsp->isString()) {
        return new AstEqN(fl, lhsp, rhsp);
    } else if (lhsp->isDouble() && rhsp->isDouble()) {
        return new AstEqD(fl, lhsp, rhsp);
    } else {
        return new AstEqWild(fl, lhsp, rhsp);
    }
}

AstExecGraph::AstExecGraph(FileLine* fileline)
    : AstNode(AstType::atExecGraph, fileline) {
    m_depGraphp = new V3Graph;
}
AstExecGraph::~AstExecGraph() { VL_DO_DANGLING(delete m_depGraphp, m_depGraphp); }

AstNode* AstInsideRange::newAndFromInside(AstNode* exprp, AstNode* lhsp, AstNode* rhsp) {
    AstNode* ap = new AstGte(fileline(), exprp->cloneTree(true), lhsp);
    AstNode* bp = new AstLte(fileline(), exprp->cloneTree(true), rhsp);
    ap->fileline()->modifyWarnOff(V3ErrorCode::UNSIGNED, true);
    bp->fileline()->modifyWarnOff(V3ErrorCode::CMPCONST, true);
    AstNode* newp = new AstAnd(fileline(), ap, bp);
    return newp;
}

void AstNetlist::timeprecisionMerge(FileLine*, const VTimescale& value) {
    VTimescale prec = v3Global.opt.timeComputePrec(value);
    if (prec.isNone() || prec == m_timeprecision) {
    } else if (m_timeprecision.isNone()) {
        m_timeprecision = prec;
    } else if (prec < m_timeprecision) {
        m_timeprecision = prec;
    }
}

bool AstVar::isSigPublic() const {
    return (m_sigPublic || (v3Global.opt.allPublic() && !isTemp() && !isGenVar()));
}
bool AstVar::isScQuad() const { return (isSc() && isQuad() && !isScBv() && !isScBigUint()); }
bool AstVar::isScBv() const {
    return ((isSc() && width() >= v3Global.opt.pinsBv()) || m_attrScBv);
}
bool AstVar::isScUint() const {
    return ((isSc() && v3Global.opt.pinsScUint() && width() >= 2 && width() <= 64) && !isScBv());
}
bool AstVar::isScBigUint() const {
    return ((isSc() && v3Global.opt.pinsScBigUint() && width() >= 65 && width() <= 512)
            && !isScBv());
}

void AstVar::combineType(AstVarType type) {
    // These flags get combined with the existing settings of the flags.
    // We don't test varType for certain types, instead set flags since
    // when we combine wires cross-hierarchy we need a union of all characteristics.
    m_varType = type;
    // These flags get combined with the existing settings of the flags.
    if (type == AstVarType::TRIWIRE || type == AstVarType::TRI0 || type == AstVarType::TRI1) {
        m_tristate = true;
    }
    if (type == AstVarType::TRI0) m_isPulldown = true;
    if (type == AstVarType::TRI1) m_isPullup = true;
}

string AstVar::verilogKwd() const {
    if (isIO()) {
        return direction().verilogKwd();
    } else if (isTristate()) {
        return "tri";
    } else if (varType() == AstVarType::WIRE) {
        return "wire";
    } else if (varType() == AstVarType::WREAL) {
        return "wreal";
    } else if (varType() == AstVarType::IFACEREF) {
        return "ifaceref";
    } else {
        return dtypep()->name();
    }
}

class AstVar::VlArgTypeRecursed {
public:
    string m_oref;  // To output, reference part before name, "&"
    string m_osuffix;  // To output, suffixed after name, "[3]"
    string m_oprefix;  // To output, prefixed before name, "Foo_t"
    void clear() {
        m_oref.clear();
        m_osuffix.clear();
        m_oprefix.clear();
    }
    string refParen(const string& name) {
        return m_oref.empty() ? name : "(" + m_oref + " " + name + ")";
    }
};

string AstVar::vlArgType(bool named, bool forReturn, bool forFunc, const string& namespc) const {
    UASSERT_OBJ(!forReturn, this,
                "Internal data is never passed as return, but as first argument");
    string ostatic;
    if (isStatic() && namespc.empty()) ostatic = "static ";

    VlArgTypeRecursed info = vlArgTypeRecurse(forFunc, dtypep(), false);

    string oname;
    if (named) {
        oname += " ";
        if (!namespc.empty()) oname += namespc + "::";
        oname += VIdProtect::protectIf(name(), protect());
    }
    return ostatic + info.m_oprefix + info.refParen(oname) + info.m_osuffix;
}

AstVar::VlArgTypeRecursed AstVar::vlArgTypeRecurse(bool forFunc, const AstNodeDType* dtypep,
                                                   bool arrayed) const {
    dtypep = dtypep->skipRefp();
    if (const AstAssocArrayDType* adtypep = VN_CAST_CONST(dtypep, AssocArrayDType)) {
        VlArgTypeRecursed key = vlArgTypeRecurse(forFunc, adtypep->keyDTypep(), true);
        VlArgTypeRecursed sub = vlArgTypeRecurse(forFunc, adtypep->subDTypep(), true);
        string out = "VlAssocArray<";
        out += key.m_oprefix;
        if (!key.m_osuffix.empty() || !key.m_oref.empty()) {
            out += " " + key.m_osuffix + key.m_oref;
        }
        out += ", ";
        out += sub.m_oprefix;
        if (!sub.m_osuffix.empty() || !sub.m_oref.empty()) {
            out += " " + sub.m_osuffix + sub.m_oref;
        }
        out += "> ";
        VlArgTypeRecursed info;
        info.m_oprefix = out;
        return info;
    } else if (const AstDynArrayDType* adtypep = VN_CAST_CONST(dtypep, DynArrayDType)) {
        VlArgTypeRecursed sub = vlArgTypeRecurse(forFunc, adtypep->subDTypep(), true);
        string out = "VlQueue<";
        out += sub.m_oprefix;
        if (!sub.m_osuffix.empty() || !sub.m_oref.empty()) {
            out += " " + sub.m_osuffix + sub.m_oref;
        }
        out += "> ";
        VlArgTypeRecursed info;
        info.m_oprefix = out;
        return info;
    } else if (const AstQueueDType* adtypep = VN_CAST_CONST(dtypep, QueueDType)) {
        VlArgTypeRecursed sub = vlArgTypeRecurse(forFunc, adtypep->subDTypep(), true);
        VlArgTypeRecursed info;
        string out = "VlQueue<" + sub.m_oprefix;
        if (!sub.m_osuffix.empty() || !sub.m_oref.empty()) {
            out += " " + sub.m_osuffix + sub.m_oref;
        }
        // + 1 below as VlQueue uses 0 to mean unlimited, 1 to mean size() max is 1
        if (adtypep->boundp()) out += ", " + cvtToStr(adtypep->boundConst() + 1);
        out += "> ";
        info.m_oprefix = out;
        return info;
    } else if (const AstClassRefDType* adtypep = VN_CAST_CONST(dtypep, ClassRefDType)) {
        VlArgTypeRecursed info;
        info.m_oprefix = "VlClassRef<" + EmitCBaseVisitor::prefixNameProtect(adtypep) + ">";
        return info;
    } else if (const AstUnpackArrayDType* adtypep = VN_CAST_CONST(dtypep, UnpackArrayDType)) {
        VlArgTypeRecursed info = vlArgTypeRecurse(forFunc, adtypep->subDTypep(), arrayed);
        info.m_osuffix = "[" + cvtToStr(adtypep->declRange().elements()) + "]" + info.m_osuffix;
        return info;
    } else if (const AstBasicDType* bdtypep = dtypep->basicp()) {
        string otype;
        string oarray;
        bool strtype = bdtypep->keyword() == AstBasicDTypeKwd::STRING;
        string bitvec;
        if (!bdtypep->isOpaque() && !v3Global.opt.protectIds()) {
            // We don't print msb()/lsb() as multidim packed would require recursion,
            // and may confuse users as C++ data is stored always with bit 0 used
            bitvec += "/*" + cvtToStr(dtypep->width() - 1) + ":0*/";
        }
        if ((forFunc && isReadOnly()) || bdtypep->keyword() == AstBasicDTypeKwd::CHARPTR
            || bdtypep->keyword() == AstBasicDTypeKwd::SCOPEPTR)
            otype += "const ";
        if (bdtypep->keyword() == AstBasicDTypeKwd::CHARPTR) {
            otype += "char*";
        } else if (bdtypep->keyword() == AstBasicDTypeKwd::SCOPEPTR) {
            otype += "VerilatedScope*";
        } else if (bdtypep->keyword() == AstBasicDTypeKwd::DOUBLE) {
            otype += "double";
        } else if (bdtypep->keyword() == AstBasicDTypeKwd::FLOAT) {
            otype += "float";
        } else if (strtype) {
            otype += "std::string";
        } else if (dtypep->widthMin() <= 8) {  // Handle unpacked arrays; not bdtypep->width
            otype += "CData" + bitvec;
        } else if (dtypep->widthMin() <= 16) {
            otype += "SData" + bitvec;
        } else if (dtypep->widthMin() <= VL_IDATASIZE) {
            otype += "IData" + bitvec;
        } else if (dtypep->isQuad()) {
            otype += "QData" + bitvec;
        } else if (dtypep->isWide()) {
            if (arrayed) {
                otype += "VlWide<" + cvtToStr(dtypep->widthWords()) + "> ";
            } else {
                otype += "WData" + bitvec;  // []'s added later
                oarray += "[" + cvtToStr(dtypep->widthWords()) + "]";
            }
        }

        string oref;
        if (isDpiOpenArray()
            || (forFunc
                && (isWritable() || direction() == VDirection::REF
                    || direction() == VDirection::CONSTREF || (strtype && isNonOutput())))) {
            oref = "&";
        }

        VlArgTypeRecursed info;
        info.m_oprefix = otype;
        info.m_osuffix = oarray;
        info.m_oref = oref;
        // UINFO(9, "vlArgRec "<<"oprefix="<<info.m_oprefix<<" osuffix="<<info.m_osuffix
        //      <<" oref="<<info.m_oref<<" "<<dtypep);
        return info;
    } else {
        v3fatalSrc("Unknown data type in var type emitter: " << dtypep->prettyName());
    }
}

string AstVar::vlEnumType() const {
    string arg;
    AstBasicDType* bdtypep = basicp();
    bool strtype = bdtypep && bdtypep->keyword() == AstBasicDTypeKwd::STRING;
    if (bdtypep && bdtypep->keyword() == AstBasicDTypeKwd::CHARPTR) {
        return "VLVT_PTR";
    } else if (bdtypep && bdtypep->keyword() == AstBasicDTypeKwd::SCOPEPTR) {
        return "VLVT_PTR";
    } else if (strtype) {
        arg += "VLVT_STRING";
    } else if (widthMin() <= 8) {
        arg += "VLVT_UINT8";
    } else if (widthMin() <= 16) {
        arg += "VLVT_UINT16";
    } else if (widthMin() <= VL_IDATASIZE) {
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
    string out;
    if (isInoutish()) {
        out = "VLVD_INOUT";
    } else if (isWritable()) {
        out = "VLVD_OUT";
    } else if (isNonOutput()) {
        out = "VLVD_IN";
    } else {
        out = "VLVD_NODIR";
    }
    //
    if (isSigUserRWPublic()) {
        out += "|VLVF_PUB_RW";
    } else if (isSigUserRdPublic()) {
        out += "|VLVF_PUB_RD";
    }
    //
    if (AstBasicDType* bdtypep = basicp()) {
        if (bdtypep->keyword().isDpiCLayout()) out += "|VLVF_DPI_CLAY";
    }
    return out;
}

string AstVar::vlPropInit() const {
    string out;
    out = vlEnumType();  // VLVT_UINT32 etc
    out += ", " + vlEnumDir();  // VLVD_IN etc
    if (AstBasicDType* bdtypep = basicp()) {
        out += ", VerilatedVarProps::Packed()";
        out += ", " + cvtToStr(bdtypep->left()) + ", " + cvtToStr(bdtypep->right());
    }
    bool first = true;
    for (AstNodeDType* dtp = dtypep(); dtp;) {
        dtp = dtp->skipRefp();  // Skip AstRefDType/AstTypedef, or return same node
        if (AstNodeArrayDType* adtypep = VN_CAST(dtp, NodeArrayDType)) {
            if (first) {
                out += ", VerilatedVarProps::Unpacked()";
                first = false;
            }
            out += ", " + cvtToStr(adtypep->declRange().left()) + ", "
                   + cvtToStr(adtypep->declRange().right());
            dtp = adtypep->subDTypep();
        } else {
            break;  // AstBasicDType - nothing below
        }
    }
    return out;
}

string AstVar::cPubArgType(bool named, bool forReturn) const {
    if (forReturn) named = false;
    string arg;
    if (isWide() && isReadOnly()) arg += "const ";
    if (widthMin() == 1) {
        arg += "bool";
    } else if (widthMin() <= VL_IDATASIZE) {
        arg += "uint32_t";
    } else if (widthMin() <= VL_QUADSIZE) {
        arg += "vluint64_t";
    } else {
        arg += "uint32_t";  // []'s added later
    }
    if (isWide()) {
        if (forReturn) {
            v3error("Unsupported: Public functions with >64 bit outputs; "
                    "make an output of a public task instead");
        }
        arg += " (& " + name();
        arg += ")[" + cvtToStr(widthWords()) + "]";
    } else {
        if (!forReturn && (isWritable() || direction().isRefOrConstRef())) arg += "&";
        if (named) arg += " " + name();
    }
    return arg;
}

string AstVar::dpiArgType(bool named, bool forReturn) const {
    if (forReturn) named = false;
    string arg;
    if (isDpiOpenArray()) {
        arg = "const svOpenArrayHandle";
    } else if (!basicp()) {
        arg = "UNKNOWN";
    } else if (basicp()->isDpiBitVec()) {
        if (forReturn) {
            arg = "svBitVecVal";
        } else if (isReadOnly()) {
            arg = "const svBitVecVal*";
        } else {
            arg = "svBitVecVal*";
        }
    } else if (basicp()->isDpiLogicVec()) {
        if (forReturn) {
            arg = "svLogicVecVal";
        } else if (isReadOnly()) {
            arg = "const svLogicVecVal*";
        } else {
            arg = "svLogicVecVal*";
        }
    } else {
        arg = basicp()->keyword().dpiType();
        if (basicp()->keyword().isDpiUnsignable() && !basicp()->isSigned()) {
            arg = "unsigned " + arg;
        }
        if (!forReturn && isWritable()) arg += "*";
    }
    if (named) arg += " " + name();
    return arg;
}

string AstVar::scType() const {
    if (isScBigUint()) {
        return (string("sc_biguint<") + cvtToStr(widthMin())
                + "> ");  // Keep the space so don't get >>
    } else if (isScUint()) {
        return (string("sc_uint<") + cvtToStr(widthMin())
                + "> ");  // Keep the space so don't get >>
    } else if (isScBv()) {
        return (string("sc_bv<") + cvtToStr(widthMin()) + "> ");  // Keep the space so don't get >>
    } else if (widthMin() == 1) {
        return "bool";
    } else if (widthMin() <= VL_IDATASIZE) {
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
    if (AstVar* anodep = VN_CAST(nodep, Var)) {
        if (anodep->isSc()) {
            return anodep;
        } else {
            return NULL;
        }
    } else if (VN_IS(nodep, VarRef)) {
        if (VN_CAST(nodep, VarRef)->varp()->isSc()) {
            return VN_CAST(nodep, VarRef)->varp();
        } else {
            return NULL;
        }
    } else if (VN_IS(nodep, ArraySel)) {
        if (nodep->op1p()) {
            if (AstVar* p = scVarRecurse(nodep->op1p())) return p;
        }
        if (nodep->op2p()) {
            if (AstVar* p = scVarRecurse(nodep->op2p())) return p;
        }
        if (nodep->op3p()) {
            if (AstVar* p = scVarRecurse(nodep->op3p())) return p;
        }
        if (nodep->op4p()) {
            if (AstVar* p = scVarRecurse(nodep->op4p())) return p;
        }
    }
    return NULL;
}

string AstVar::mtasksString() const {
    std::ostringstream os;
    os << "all: ";
    for (MTaskIdSet::const_iterator it = m_mtaskIds.begin(); it != m_mtaskIds.end(); ++it) {
        os << *it << " ";
    }
    return os.str();
}

AstNodeDType* AstNodeDType::dtypeDimensionp(int dimension) {
    // dimension passed from AstArraySel::dimension
    // Dimension 0 means the VAR itself, 1 is the closest SEL to the AstVar,
    // which is the lowest in the dtype list.
    //     ref order:   a[1][2][3][4]
    //     Created as:  reg [4] a [1][2][3];
    //        *or*      reg a [1][2][3][4];
    //                  // The bit select is optional; used only if "leftover" []'s
    //     SEL:         SEL4(SEL3(SEL2(SEL1(VARREF0 a))))
    //     DECL:        VAR a (ARRAYSEL0 (ARRAYSEL1 (ARRAYSEL2 (DT RANGE3))))
    //        *or*      VAR a (ARRAYSEL0 (ARRAYSEL1 (ARRAYSEL2 (ARRAYSEL3 (DT))))
    //     SEL1 needs to select from entire variable which is a pointer to ARRAYSEL0
    // TODO this function should be removed in favor of recursing the dtype(),
    // as that allows for more complicated data types.
    int dim = 0;
    for (AstNodeDType* dtypep = this; dtypep;) {
        dtypep = dtypep->skipRefp();  // Skip AstRefDType/AstTypedef, or return same node
        if (AstNodeArrayDType* adtypep = VN_CAST(dtypep, NodeArrayDType)) {
            if ((dim++) == dimension) return dtypep;
            dtypep = adtypep->subDTypep();
            continue;
        } else if (AstBasicDType* adtypep = VN_CAST(dtypep, BasicDType)) {
            // AstBasicDType - nothing below, return null
            if (adtypep->isRanged()) {
                if ((dim++) == dimension) return adtypep;
            }
            return NULL;
        } else if (AstNodeUOrStructDType* adtypep = VN_CAST(dtypep, NodeUOrStructDType)) {
            if (adtypep->packed()) {
                if ((dim++) == dimension) return adtypep;
            }
            return NULL;
        }
        // Node no ->next in loop; use continue where necessary
        break;
    }
    return NULL;
}

uint32_t AstNodeDType::arrayUnpackedElements() {
    uint32_t entries = 1;
    for (AstNodeDType* dtypep = this; dtypep;) {
        dtypep = dtypep->skipRefp();  // Skip AstRefDType/AstTypedef, or return same node
        if (AstUnpackArrayDType* adtypep = VN_CAST(dtypep, UnpackArrayDType)) {
            entries *= adtypep->elementsConst();
            dtypep = adtypep->subDTypep();
        } else {
            // AstBasicDType - nothing below, 1
            break;
        }
    }
    return entries;
}

std::pair<uint32_t, uint32_t> AstNodeDType::dimensions(bool includeBasic) {
    // How many array dimensions (packed,unpacked) does this Var have?
    uint32_t packed = 0;
    uint32_t unpacked = 0;
    for (AstNodeDType* dtypep = this; dtypep;) {
        dtypep = dtypep->skipRefp();  // Skip AstRefDType/AstTypedef, or return same node
        if (const AstNodeArrayDType* adtypep = VN_CAST(dtypep, NodeArrayDType)) {
            if (VN_IS(adtypep, PackArrayDType)) {
                ++packed;
            } else {
                ++unpacked;
            }
            dtypep = adtypep->subDTypep();
            continue;
        } else if (const AstQueueDType* qdtypep = VN_CAST(dtypep, QueueDType)) {
            unpacked++;
            dtypep = qdtypep->subDTypep();
            continue;
        } else if (const AstBasicDType* adtypep = VN_CAST(dtypep, BasicDType)) {
            if (includeBasic && (adtypep->isRanged() || adtypep->isString())) packed++;
        } else if (VN_IS(dtypep, StructDType)) {
            packed++;
        }
        break;
    }
    return make_pair(packed, unpacked);
}

int AstNodeDType::widthPow2() const {
    // I.e.  width 30 returns 32, width 32 returns 32.
    uint32_t width = this->width();
    for (int p2 = 30; p2 >= 0; p2--) {
        if (width > (1UL << p2)) return (1UL << (p2 + 1));
    }
    return 1;
}

/// What is the base variable (or const) this dereferences?
AstNode* AstArraySel::baseFromp(AstNode* nodep) {
    // Else AstArraySel etc; search for the base
    while (nodep) {
        if (VN_IS(nodep, ArraySel)) {
            nodep = VN_CAST(nodep, ArraySel)->fromp();
            continue;
        } else if (VN_IS(nodep, Sel)) {
            nodep = VN_CAST(nodep, Sel)->fromp();
            continue;
        }
        // AstNodeSelPre stashes the associated variable under an ATTROF
        // of AstAttrType::VAR_BASE/MEMBER_BASE so it isn't constified
        else if (VN_IS(nodep, AttrOf)) {
            nodep = VN_CAST(nodep, AttrOf)->fromp();
            continue;
        } else if (VN_IS(nodep, NodePreSel)) {
            if (VN_CAST(nodep, NodePreSel)->attrp()) {
                nodep = VN_CAST(nodep, NodePreSel)->attrp();
            } else {
                nodep = VN_CAST(nodep, NodePreSel)->lhsp();
            }
            continue;
        } else {
            break;
        }
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
    if (m_aboveScopep && m_aboveScopep->clonep()) m_aboveScopep->clonep();
    if (m_aboveCellp && m_aboveCellp->clonep()) m_aboveCellp->clonep();
    if (m_modp && static_cast<AstNode*>(m_modp)->clonep()) {
        static_cast<AstNode*>(m_modp)->clonep();
    }
}

string AstScope::nameDotless() const {
    string out = shortName();
    string::size_type pos;
    while ((pos = out.find('.')) != string::npos) out.replace(pos, 1, "__");
    return out;
}

string AstScopeName::scopePrettyNameFormatter(AstText* scopeTextp) const {
    string out;
    for (AstText* textp = scopeTextp; textp; textp = VN_CAST(textp->nextp(), Text)) {
        out += textp->text();
    }
    // TOP will be replaced by top->name()
    if (out.substr(0, 10) == "__DOT__TOP") out.replace(0, 10, "");
    if (out.substr(0, 7) == "__DOT__") out.replace(0, 7, "");
    if (out.substr(0, 1) == ".") out.replace(0, 1, "");
    return AstNode::prettyName(out);
}

string AstScopeName::scopeNameFormatter(AstText* scopeTextp) const {
    string out;
    for (AstText* textp = scopeTextp; textp; textp = VN_CAST(textp->nextp(), Text)) {
        out += textp->text();
    }
    if (out.substr(0, 10) == "__DOT__TOP") out.replace(0, 10, "");
    if (out.substr(0, 7) == "__DOT__") out.replace(0, 7, "");
    if (out.substr(0, 1) == ".") out.replace(0, 1, "");
    string::size_type pos;
    while ((pos = out.find('.')) != string::npos) out.replace(pos, 1, "__");
    while ((pos = out.find("__DOT__")) != string::npos) out.replace(pos, 7, "__");
    return out;
}

bool AstSenTree::hasClocked() const {
    UASSERT_OBJ(sensesp(), this, "SENTREE without any SENITEMs under it");
    for (AstNodeSenItem* senp = sensesp(); senp; senp = VN_CAST(senp->nextp(), NodeSenItem)) {
        if (senp->isClocked()) return true;
    }
    return false;
}
bool AstSenTree::hasSettle() const {
    UASSERT_OBJ(sensesp(), this, "SENTREE without any SENITEMs under it");
    for (AstNodeSenItem* senp = sensesp(); senp; senp = VN_CAST(senp->nextp(), NodeSenItem)) {
        if (senp->isSettle()) return true;
    }
    return false;
}
bool AstSenTree::hasInitial() const {
    UASSERT_OBJ(sensesp(), this, "SENTREE without any SENITEMs under it");
    for (AstNodeSenItem* senp = sensesp(); senp; senp = VN_CAST(senp->nextp(), NodeSenItem)) {
        if (senp->isInitial()) return true;
    }
    return false;
}
bool AstSenTree::hasCombo() const {
    UASSERT_OBJ(sensesp(), this, "SENTREE without any SENITEMs under it");
    for (AstNodeSenItem* senp = sensesp(); senp; senp = VN_CAST(senp->nextp(), NodeSenItem)) {
        if (senp->isCombo()) return true;
    }
    return false;
}

void AstTypeTable::clearCache() {
    // When we mass-change widthMin in V3WidthCommit, we need to correct the table.
    // Just clear out the maps; the search functions will be used to rebuild the map
    for (int i = 0; i < static_cast<int>(AstBasicDTypeKwd::_ENUM_MAX); ++i) {
        m_basicps[i] = NULL;
    }
    m_detailedMap.clear();
    // Clear generic()'s so dead detection will work
    for (AstNode* nodep = typesp(); nodep; nodep = nodep->nextp()) {
        if (AstBasicDType* bdtypep = VN_CAST(nodep, BasicDType)) bdtypep->generic(false);
    }
}

void AstTypeTable::repairCache() {
    // After we mass-change widthMin in V3WidthCommit, we need to correct the table.
    clearCache();
    for (AstNode* nodep = typesp(); nodep; nodep = nodep->nextp()) {
        if (AstBasicDType* bdtypep = VN_CAST(nodep, BasicDType)) {
            (void)findInsertSameDType(bdtypep);
        }
    }
}

AstVoidDType* AstTypeTable::findVoidDType(FileLine* fl) {
    if (VL_UNLIKELY(!m_voidp)) {
        AstVoidDType* newp = new AstVoidDType(fl);
        addTypesp(newp);
        m_voidp = newp;
    }
    return m_voidp;
}

AstBasicDType* AstTypeTable::findBasicDType(FileLine* fl, AstBasicDTypeKwd kwd) {
    if (m_basicps[kwd]) return m_basicps[kwd];
    //
    AstBasicDType* new1p = new AstBasicDType(fl, kwd);
    // Because the detailed map doesn't update this map,
    // check the detailed map for this same node
    // Also adds this new node to the detailed map
    AstBasicDType* newp = findInsertSameDType(new1p);
    if (newp != new1p) {
        VL_DO_DANGLING(new1p->deleteTree(), new1p);
    } else {
        addTypesp(newp);
    }
    //
    m_basicps[kwd] = newp;
    return newp;
}

AstBasicDType* AstTypeTable::findLogicBitDType(FileLine* fl, AstBasicDTypeKwd kwd, int width,
                                               int widthMin, VSigning numeric) {
    AstBasicDType* new1p = new AstBasicDType(fl, kwd, numeric, width, widthMin);
    AstBasicDType* newp = findInsertSameDType(new1p);
    if (newp != new1p) {
        VL_DO_DANGLING(new1p->deleteTree(), new1p);
    } else {
        addTypesp(newp);
    }
    return newp;
}

AstBasicDType* AstTypeTable::findLogicBitDType(FileLine* fl, AstBasicDTypeKwd kwd, VNumRange range,
                                               int widthMin, VSigning numeric) {
    AstBasicDType* new1p = new AstBasicDType(fl, kwd, numeric, range, widthMin);
    AstBasicDType* newp = findInsertSameDType(new1p);
    if (newp != new1p) {
        VL_DO_DANGLING(new1p->deleteTree(), new1p);
    } else {
        addTypesp(newp);
    }
    return newp;
}

AstBasicDType* AstTypeTable::findInsertSameDType(AstBasicDType* nodep) {
    VBasicTypeKey key(nodep->width(), nodep->widthMin(), nodep->numeric(), nodep->keyword(),
                      nodep->nrange());
    DetailedMap& mapr = m_detailedMap;
    DetailedMap::const_iterator it = mapr.find(key);
    if (it != mapr.end()) return it->second;
    mapr.insert(make_pair(key, nodep));
    nodep->generic(true);
    // No addTypesp; the upper function that called new() is responsible for adding
    return nodep;
}

//======================================================================
// Special walking tree inserters

void AstNode::addBeforeStmt(AstNode* newp, AstNode*) {
    UASSERT_OBJ(backp(), newp, "Can't find current statement to addBeforeStmt");
    // Look up; virtual call will find where to put it
    this->backp()->addBeforeStmt(newp, this);
}
void AstNode::addNextStmt(AstNode* newp, AstNode*) {
    UASSERT_OBJ(backp(), newp, "Can't find current statement to addNextStmt");
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
    // Preconditions insert first just before themselves (the normal rule
    // for other statement types)
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
    // Preconditions insert first just before themselves (the normal rule
    // for other statement types)
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

void AstNode::dump(std::ostream& str) const {
    str << typeName() << " "
        << cvtToHex(this)
        //<<" "<<cvtToHex(this)->m_backp
        << " <e" << std::dec << editCount() << ((editCount() >= editCountLast()) ? "#>" : ">")
        << " {" << fileline()->filenameLetters() << std::dec << fileline()->lastLineno() << "}";
    if (user1p()) str << " u1=" << cvtToHex(user1p());
    if (user2p()) str << " u2=" << cvtToHex(user2p());
    if (user3p()) str << " u3=" << cvtToHex(user3p());
    if (user4p()) str << " u4=" << cvtToHex(user4p());
    if (user5p()) str << " u5=" << cvtToHex(user5p());
    if (hasDType()) {
        // Final @ so less likely to by accident read it as a nodep
        if (dtypep() == this) {
            str << " @dt=this@";
        } else {
            str << " @dt=" << cvtToHex(dtypep()) << "@";
        }
        if (AstNodeDType* dtp = dtypep()) { dtp->dumpSmall(str); }
    } else {  // V3Broken will throw an error
        if (dtypep()) str << " %Error-dtype-exp=null,got=" << cvtToHex(dtypep());
    }
    if (name() != "") {
        if (VN_IS(this, Const)) {
            str << "  " << name();  // Already quoted
        } else {
            str << "  " << V3OutFormatter::quoteNameControls(name());
        }
    }
}

void AstAlways::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (keyword() != VAlwaysKwd::ALWAYS) str << " [" << keyword().ascii() << "]";
}

void AstAttrOf::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    str << " [" << attrType().ascii() << "]";
}
void AstBasicDType::dump(std::ostream& str) const {
    this->AstNodeDType::dump(str);
    str << " kwd=" << keyword().ascii();
    if (isRanged() && !rangep()) str << " range=[" << left() << ":" << right() << "]";
}
string AstBasicDType::prettyDTypeName() const {
    std::ostringstream os;
    os << keyword().ascii();
    if (isRanged() && !rangep() && keyword().width() <= 1) {
        os << "[" << left() << ":" << right() << "]";
    }
    return os.str();
}
void AstCCast::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    str << " sz" << size();
}
void AstCell::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (recursive()) str << " [RECURSIVE]";
    if (modp()) {
        str << " -> ";
        modp()->dump(str);
    } else {
        str << " ->UNLINKED:" << modName();
    }
}
void AstCellInline::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    str << " -> " << origModName();
}
const char* AstClassPackage::broken() const {
    BROKEN_BASE_RTN(AstNodeModule::broken());
    BROKEN_RTN(m_classp && !m_classp->brokeExists());
    return NULL;
}
void AstClass::insertCache(AstNode* nodep) {
    if (VN_IS(nodep, Var) || VN_IS(nodep, NodeFTask) || VN_IS(nodep, EnumItemRef)) {
        if (m_members.find(nodep->name()) != m_members.end()) {
            nodep->v3error("Duplicate declaration of member name: " << nodep->prettyNameQ());
        } else {
            m_members.insert(make_pair(nodep->name(), nodep));
        }
    }
}
void AstClass::repairCache() {
    clearCache();
    for (AstNode* itemp = membersp(); itemp; itemp = itemp->nextp()) { insertCache(itemp); }
}
void AstClass::dump(std::ostream& str) const { this->AstNode::dump(str); }
AstClass* AstClassExtends::classp() const {
    AstClassRefDType* refp = VN_CAST(dtypep(), ClassRefDType);
    UASSERT_OBJ(refp, this, "class extends non-ref");
    return refp->classp();
}
void AstClassRefDType::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (classp()) {
        str << " -> ";
        classp()->dump(str);
    } else {
        str << " -> UNLINKED";
    }
}
void AstClassRefDType::dumpSmall(std::ostream& str) const {
    this->AstNodeDType::dumpSmall(str);
    str << "class:" << name();
}
void AstNodeCoverOrAssert::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (immediate()) str << " [IMMEDIATE]";
}
void AstDisplay::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    // str<<" "<<displayType().ascii();
}
void AstEnumItemRef::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    str << " -> ";
    if (itemp()) {
        itemp()->dump(str);
    } else {
        str << "UNLINKED";
    }
}
void AstIfaceRefDType::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (cellName() != "") { str << " cell=" << cellName(); }
    if (ifaceName() != "") { str << " if=" << ifaceName(); }
    if (modportName() != "") { str << " mp=" << modportName(); }
    if (cellp()) {
        str << " -> ";
        cellp()->dump(str);
    } else if (ifacep()) {
        str << " -> ";
        ifacep()->dump(str);
    } else {
        str << " -> UNLINKED";
    }
}
void AstIfaceRefDType::dumpSmall(std::ostream& str) const {
    this->AstNodeDType::dumpSmall(str);
    str << "iface";
}
void AstInitArray::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    int n = 0;
    const AstInitArray::KeyItemMap& mapr = map();
    for (AstInitArray::KeyItemMap::const_iterator it = mapr.begin(); it != mapr.end(); ++it) {
        if (n++ > 5) {
            str << " ...";
            break;
        }
        str << " [" << it->first << "]=" << (void*)it->second;
    }
}
void AstJumpGo::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    str << " -> ";
    if (labelp()) {
        labelp()->dump(str);
    } else {
        str << "%Error:UNLINKED";
    }
}
void AstMemberSel::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    str << " -> ";
    if (varp()) {
        varp()->dump(str);
    } else {
        str << "%Error:UNLINKED";
    }
}
void AstMethodCall::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (isStatement()) str << " [STMT]";
    str << " -> ";
    if (taskp()) {
        taskp()->dump(str);
    } else {
        str << " -> UNLINKED";
    }
}
void AstModportFTaskRef::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (isExport()) str << " EXPORT";
    if (isImport()) str << " IMPORT";
    if (ftaskp()) {
        str << " -> ";
        ftaskp()->dump(str);
    } else {
        str << " -> UNLINKED";
    }
}
void AstModportVarRef::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (direction().isAny()) str << " " << direction();
    if (varp()) {
        str << " -> ";
        varp()->dump(str);
    } else {
        str << " -> UNLINKED";
    }
}
void AstPin::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (modVarp()) {
        str << " -> ";
        modVarp()->dump(str);
    } else {
        str << " ->UNLINKED";
    }
    if (svImplicit()) str << " [.SV]";
}
void AstPrintTimeScale::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    str << " " << timeunit();
}
void AstTime::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    str << " " << timeunit();
}
void AstTimeD::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    str << " " << timeunit();
}
void AstTimeImport::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    str << " " << timeunit();
}
void AstTypedef::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (attrPublic()) str << " [PUBLIC]";
}
void AstRange::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (littleEndian()) str << " [LITTLE]";
}
void AstRefDType::dump(std::ostream& str) const {
    this->AstNodeDType::dump(str);
    if (defp()) {
        static bool s_recursing = false;
        if (!s_recursing) {  // Prevent infinite dump if circular typedefs
            s_recursing = true;
            str << " -> ";
            defp()->dump(str);
            s_recursing = false;
        }
    } else {
        str << " -> UNLINKED";
    }
}
void AstNodeUOrStructDType::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (packed()) str << " [PACKED]";
    if (isFourstate()) str << " [4STATE]";
}
void AstNodeDType::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (generic()) str << " [GENERIC]";
    if (AstNodeDType* dtp = virtRefDTypep()) {
        str << " refdt=" << cvtToHex(dtp);
        dtp->dumpSmall(str);
    }
}
void AstNodeDType::dumpSmall(std::ostream& str) const {
    str << "(" << (generic() ? "G/" : "") << ((isSigned() && !isDouble()) ? "s" : "")
        << (isNosign() ? "n" : "") << (isDouble() ? "d" : "") << (isString() ? "str" : "");
    if (!isDouble() && !isString()) { str << "w" << (widthSized() ? "" : "u") << width(); }
    if (!widthSized()) str << "/" << widthMin();
    str << ")";
}
void AstNodeArrayDType::dumpSmall(std::ostream& str) const {
    this->AstNodeDType::dumpSmall(str);
    if (VN_IS(this, PackArrayDType)) {
        str << "p";
    } else {
        str << "u";
    }
    str << declRange();
}
void AstNodeArrayDType::dump(std::ostream& str) const {
    this->AstNodeDType::dump(str);
    str << " " << declRange();
}
string AstPackArrayDType::prettyDTypeName() const {
    std::ostringstream os;
    os << subDTypep()->prettyDTypeName() << declRange();
    return os.str();
}
string AstUnpackArrayDType::prettyDTypeName() const {
    std::ostringstream os;
    string ranges = cvtToStr(declRange());
    // Unfortunately we need a single $ for the first unpacked, and all
    // dimensions shown in "reverse" order
    AstNodeDType* subp = subDTypep()->skipRefp();
    while (AstUnpackArrayDType* adtypep = VN_CAST(subp, UnpackArrayDType)) {
        ranges += cvtToStr(adtypep->declRange());
        subp = adtypep->subDTypep()->skipRefp();
    }
    os << subp->prettyDTypeName() << "$" << ranges;
    return os.str();
}
void AstNetlist::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    str << " [" << timeunit() << "/" << timeprecision() << "]";
}
void AstNodeModule::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    str << "  L" << level();
    if (modPublic()) str << " [P]";
    if (inLibrary()) str << " [LIB]";
    if (dead()) str << " [DEAD]";
    if (recursiveClone()) {
        str << " [RECURSIVE-CLONE]";
    } else if (recursive()) {
        str << " [RECURSIVE]";
    }
    str << " [" << timeunit() << "]";
}
void AstPackageExport::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    str << " -> " << packagep();
}
void AstPackageImport::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    str << " -> " << packagep();
}
void AstSel::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (declRange().ranged()) {
        str << " decl" << declRange() << "]";
        if (declElWidth() != 1) str << "/" << declElWidth();
    }
}
void AstSliceSel::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (declRange().ranged()) str << " decl" << declRange();
}
void AstMTaskBody::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    str << " ";
    m_execMTaskp->dump(str);
}
void AstTypeTable::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    for (int i = 0; i < static_cast<int>(AstBasicDTypeKwd::_ENUM_MAX); ++i) {
        if (AstBasicDType* subnodep = m_basicps[i]) {
            str << endl;  // Newline from caller, so newline first
            str << "\t\t" << std::setw(8) << AstBasicDTypeKwd(i).ascii();
            str << "  -> ";
            subnodep->dump(str);
        }
    }
    {
        const DetailedMap& mapr = m_detailedMap;
        for (DetailedMap::const_iterator it = mapr.begin(); it != mapr.end(); ++it) {
            AstBasicDType* dtypep = it->second;
            str << endl;  // Newline from caller, so newline first
            str << "\t\tdetailed  ->  ";
            dtypep->dump(str);
        }
    }
    // Note get newline from caller too.
}
void AstAssocArrayDType::dumpSmall(std::ostream& str) const {
    this->AstNodeDType::dumpSmall(str);
    str << "[assoc-" << (void*)keyDTypep() << "]";
}
string AstAssocArrayDType::prettyDTypeName() const {
    return subDTypep()->prettyDTypeName() + "[" + keyDTypep()->prettyDTypeName() + "]";
}
void AstDynArrayDType::dumpSmall(std::ostream& str) const {
    this->AstNodeDType::dumpSmall(str);
    str << "[]";
}
string AstDynArrayDType::prettyDTypeName() const { return subDTypep()->prettyDTypeName() + "[]"; }
void AstQueueDType::dumpSmall(std::ostream& str) const {
    this->AstNodeDType::dumpSmall(str);
    str << "[queue]";
}
string AstQueueDType::prettyDTypeName() const {
    string str = subDTypep()->prettyDTypeName() + "[$";
    if (boundConst()) str += ":" + cvtToStr(boundConst());
    return str + "]";
}
void AstUnsizedArrayDType::dumpSmall(std::ostream& str) const {
    this->AstNodeDType::dumpSmall(str);
    str << "[]";
}
void AstVoidDType::dumpSmall(std::ostream& str) const {
    this->AstNodeDType::dumpSmall(str);
    str << "void";
}
void AstVarScope::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (isCircular()) str << " [CIRC]";
    if (varp()) {
        str << " -> ";
        varp()->dump(str);
    } else {
        str << " ->UNLINKED";
    }
}
void AstVarXRef::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (packagep()) { str << " pkg=" << cvtToHex(packagep()); }
    if (lvalue()) {
        str << " [LV] => ";
    } else {
        str << " [RV] <- ";
    }
    str << ".=" << dotted() << " ";
    if (inlinedDots() != "") str << " inline.=" << inlinedDots() << " - ";
    if (varScopep()) {
        varScopep()->dump(str);
    } else if (varp()) {
        varp()->dump(str);
    } else {
        str << "UNLINKED";
    }
}
void AstVarRef::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (packagep()) { str << " pkg=" << cvtToHex(packagep()); }
    if (lvalue()) {
        str << " [LV] => ";
    } else {
        str << " [RV] <- ";
    }
    if (varScopep()) {
        varScopep()->dump(str);
    } else if (varp()) {
        varp()->dump(str);
    } else {
        str << "UNLINKED";
    }
}
void AstVar::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (isSc()) str << " [SC]";
    if (isPrimaryIO()) str << (isInoutish() ? " [PIO]" : (isWritable() ? " [PO]" : " [PI]"));
    if (isIO()) str << " " << direction().ascii();
    if (isConst()) str << " [CONST]";
    if (isPullup()) str << " [PULLUP]";
    if (isPulldown()) str << " [PULLDOWN]";
    if (isUsedClock()) str << " [CLK]";
    if (isSigPublic()) str << " [P]";
    if (isUsedLoopIdx()) str << " [LOOP]";
    if (attrClockEn()) str << " [aCLKEN]";
    if (attrIsolateAssign()) str << " [aISO]";
    if (attrFileDescr()) str << " [aFD]";
    if (isFuncReturn()) {
        str << " [FUNCRTN]";
    } else if (isFuncLocal()) {
        str << " [FUNC]";
    }
    if (isDpiOpenArray()) str << " [DPIOPENA]";
    if (!attrClocker().unknown()) str << " [" << attrClocker().ascii() << "] ";
    if (!lifetime().isNone()) str << " [" << lifetime().ascii() << "] ";
    str << " " << varType();
}
void AstSenTree::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (isMulti()) str << " [MULTI]";
}
void AstSenItem::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    str << " [" << edgeType().ascii() << "]";
}
void AstParseRef::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    str << " [" << expect().ascii() << "]";
}
void AstPackageRef::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (packagep()) { str << " pkg=" << cvtToHex(packagep()); }
    str << " -> ";
    if (packagep()) {
        packagep()->dump(str);
    } else {
        str << "UNLINKED";
    }
}
void AstDot::dump(std::ostream& str) const { this->AstNode::dump(str); }
void AstActive::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    str << " => ";
    if (sensesp()) {
        sensesp()->dump(str);
    } else {
        str << "UNLINKED";
    }
}
void AstNodeFTaskRef::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (packagep()) { str << " pkg=" << cvtToHex(packagep()); }
    str << " -> ";
    if (dotted() != "") { str << ".=" << dotted() << " "; }
    if (taskp()) {
        taskp()->dump(str);
    } else {
        str << "UNLINKED";
    }
}
void AstNodeFTask::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (classMethod()) str << " [METHOD]";
    if (taskPublic()) str << " [PUBLIC]";
    if (prototype()) str << " [PROTOTYPE]";
    if (dpiImport()) str << " [DPII]";
    if (dpiExport()) str << " [DPIX]";
    if (dpiOpenChild()) str << " [DPIOPENCHILD]";
    if (dpiOpenParent()) str << " [DPIOPENPARENT]";
    if ((dpiImport() || dpiExport()) && cname() != name()) str << " [c=" << cname() << "]";
}
void AstNodeBlock::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (unnamed()) str << " [UNNAMED]";
}
void AstBegin::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (generate()) str << " [GEN]";
    if (genforp()) str << " [GENFOR]";
    if (implied()) str << " [IMPLIED]";
}
void AstCoverDecl::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (this->dataDeclNullp()) {
        str << " -> ";
        this->dataDeclNullp()->dump(str);
    } else {
        if (binNum()) { str << " bin" << std::dec << binNum(); }
    }
}
void AstCoverInc::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    str << " -> ";
    if (declp()) {
        declp()->dump(str);
    } else {
        str << "%Error:UNLINKED";
    }
}
void AstFork::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (!joinType().join()) str << " [" << joinType() << "]";
}
void AstTraceInc::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    str << " -> ";
    if (declp()) {
        declp()->dump(str);
    } else {
        str << "%Error:UNLINKED";
    }
}
void AstNodeText::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    string out = text();
    string::size_type pos;
    if ((pos = out.find('\n')) != string::npos) {
        out.erase(pos, out.length() - pos);
        out += "...";
    }
    str << " \"" << out << "\"";
}

void AstVFile::dump(std::ostream& str) const { this->AstNode::dump(str); }

void AstCFile::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (source()) str << " [SRC]";
    if (slow()) str << " [SLOW]";
}
void AstCFunc::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    if (slow()) str << " [SLOW]";
    if (pure()) str << " [PURE]";
    if (isStatic().unknown()) {
        str << " [STATICU]";
    } else if (isStatic().trueUnknown()) {
        str << " [STATIC]";
    }
    if (dpiImport()) str << " [DPII]";
    if (dpiExport()) str << " [DPIX]";
    if (dpiExportWrapper()) str << " [DPIXWR]";
    if (isConstructor()) str << " [CTOR]";
    if (isDestructor()) str << " [DTOR]";
    if (isVirtual()) str << " [VIRT]";
}
void AstCUse::dump(std::ostream& str) const {
    this->AstNode::dump(str);
    str << " [" << useType() << "]";
}
