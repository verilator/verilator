// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break variables into separate words to avoid UNOPTFLAT
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2019 by Wilson Snyder.  This program is free software; you can
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
// V3SplitVar divides a variable into multiple variables to avoid UNOPTFLAT warning
// and get better perfomance.
// Variables to be split must be marked by /*verilator split_var*/ pragma.
// There are sveral kinds of data types that may cause the warning.
// 1) Unpacked arrays
// 2) Packed arrays
// 3) Unpacked structs
// 4) Packed structs
// 5) Bitfields within a signal. (Especially Verilog code predating structs/2D arrays.)
// 2-5 above are treated as bitfields in verilator.
//
// What this pass does looks as below.
//
// <pre>
// logic [1:0] unpcked_array_var[0:3]; /*verilator split_var*/
// always_comb begin
//    unpacked_array_var[1] = unpacked_array_var[0]; // UNOPTFLAT warning
//    unpacked_array_var[2] = unpacked_array_var[1];
//    unpacked_array_var[3] = unpacked_array_var[2];
// end
// logic [3:0] packed_var; /*verilator split_var*/
// always_comb begin
//    if (some_cond) begin
//        packed_var = 4'b0;
//    end else begin
//        packed_var[3]   = some_input0;
//        packed_var[2:0] = some_input1;
//    end
// end
// </pre>
//
// is converted to
//
// <pre>
// logic [1:0] unpcked_array_var0;
// logic [1:0] unpcked_array_var1;
// logic [1:0] unpcked_array_var2;
// logic [1:0] unpcked_array_var3;
// always_comb begin
//    unpacked_array_var1 = unpacked_array_var0;
//    unpacked_array_var2 = unpacked_array_var1;
//    unpacked_array_var3 = unpacked_array_var2;
// end
// logic       packed_var__BRA__3__KET__;
// logic [2:0] packed_var__BRA__2_0__KET__;
// always_comb begin
//    if (some_cond) begin
//        {packed_var__BRA__3__KET__, packed_var__BRA__2_0__KET__} = 4'b0;
//    end else begin
//        packed_var__BRA__3__KET__   = some_input0;
//        packed_var__BRA__2_0__KET__ = some_input1;
//    end
// end
// </pre>
//
//
// Limitations: (planned to be resolved)
// - Unpacked array must be accessed via AstArraySel.
//      e.g. unpacked_array[3]   : supported
//           unpacked_array[0:1] : not supported because AstSliceSel is used
//           unpacked_array      : not supported
//   to allow such access, concatenate op node to build unpacked array is necessary on AST.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Const.h"
#include "V3Global.h"
#include "V3SplitVar.h"
#include "V3Stats.h"

#include <algorithm>  // sort
#include <vector>
#include VL_INCLUDE_UNORDERED_MAP
#include VL_INCLUDE_UNORDERED_SET

static AstConst* constifyIfNot(AstNode* nodep) {
    AstConst* constp = VN_CAST(nodep, Const);
    if (!constp) {
        UINFO(4, nodep << " is expected to be constant, but not\n");
        AstNode* const constified = V3Const::constifyEdit(nodep);
        UINFO(4, "After constified:" << constified << '\n');
        constp = VN_CAST(constified, Const);
    }
    return constp;
}

//######################################################################
// Split Unpacked Variables

class SplitUnpackedVarVisitor : public AstNVisitor {
    AstNodeModule* m_modp;  // current module
    AstVar* m_lastVarp;     // the most recently declared variable
    int m_numSplit;         // total number of split variable
    bool m_firstRun;        // true for the first pass
    // key:variable to be split. value:location where the variable is referenced.
    vl_unordered_map<AstVar*, std::vector<AstArraySel*> > m_refs;

    virtual void visit(AstNode* nodep) VL_OVERRIDE { iterateChildren(nodep); }
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        UASSERT_OBJ(m_modp == NULL, m_modp, "Nested module declration");
        m_modp = nodep;
        m_lastVarp = NULL;
        iterateChildren(nodep);
        split();
        m_modp = NULL;
    }
    virtual void visit(AstVar* nodep) VL_OVERRIDE { m_lastVarp = nodep; }
    virtual void visit(AstPragma* pragmap) VL_OVERRIDE {
        if (pragmap->pragType() != AstPragmaType::SPLIT_VAR) return;  // nothing to do
        bool keepPragma = false;
        if (!m_lastVarp) {
            pragmap->v3warn(SPLITVAR, "Stray pragma of split_var is detected.");
        } else if (!canSplit(m_lastVarp)) {
            // maybe packed variable which will be split later.
            keepPragma = true;  // SplitPackedVarVisitor will read this pragma again later.
        } else {  // finally find a good candidate
            UINFO(4, m_lastVarp->name() << " is added to candidate list.\n");
            m_refs.insert(std::make_pair(m_lastVarp, std::vector<AstArraySel*>()));
        }
        if (!keepPragma) {
            m_lastVarp = NULL;
            pragmap->unlinkFrBack()->deleteTree(); VL_DANGLING(pragmap); // consume the pragma here anyway.
        }
    }
    virtual void visit(AstVarRef* nodep) VL_OVERRIDE {
        AstVar* const varp = nodep->varp();
        if (m_refs.find(varp) == m_refs.end()) return;  // variable without split_var pragma

        if (m_firstRun)
            nodep->v3warn(SPLITVAR,
                          "Variable " << varp->prettyNameQ()
                                      << " will not be split because the entire unpacked array is referred."
                                         " Such access is not supported yet.\n");
        m_refs.erase(varp);
    }
    virtual void visit(AstArraySel* nodep) VL_OVERRIDE {
        AstVarRef* const vrefp = VN_CAST(nodep->fromp(), VarRef);
        if (!vrefp) {
            iterateChildren(nodep);
            return;
        }

        AstVar* const varp = vrefp->varp();
        if (m_refs.find(varp) == m_refs.end()) return;  // variable without split_var pragma

        AstConst* const indexp = constifyIfNot(nodep->bitp());

        if (indexp) {  // OK
            m_refs[varp].push_back(nodep);
        } else {
            if (m_firstRun)
                nodep->bitp()->v3warn(SPLITVAR,
                                      "Variable " << vrefp->prettyNameQ()
                                                  << " will not be split because index cannot be determined statically.");
            m_refs.erase(varp);
        }
    }
    virtual void visit(AstSliceSel* nodep) VL_OVERRIDE {
        AstVarRef* const vrefp = VN_CAST(nodep->fromp(), VarRef);
        if (!vrefp) return;

        AstVar* const varp = vrefp->varp();
        if (m_refs.find(varp) == m_refs.end()) return;  // variable without split_var pragma
        if (m_firstRun)
            nodep->v3warn(SPLITVAR,
                          "Variable " << vrefp->prettyNameQ()
                                      << " will not be split because slicing an unpacked array is not supported yet.");
        m_refs.erase(varp);
    }
    // The actual splitting operation is done in this function.
    void split() {
        for (vl_unordered_map<AstVar*, std::vector<AstArraySel*> >::iterator it = m_refs.begin(),
                                                                             it_end = m_refs.end();
             it != it_end; ++it) {
            UINFO(3, "In module " << m_modp->name() << " var " << it->first->prettyNameQ()
                                  << " which has "
                                  << it->second.size() << " refs will be split.\n");
            AstVar* varp = it->first;
            AstNode* insertp = varp;
            AstUnpackArrayDType* const dtypep = VN_CAST(varp->dtypep(), UnpackArrayDType);
            std::vector<AstVar*> vars;
            // Add the split variables
            AstConst* const lsbp = constifyIfNot(dtypep->rangep()->lsbp());
            AstConst* const msbp = constifyIfNot(dtypep->rangep()->msbp());
            UASSERT_OBJ(lsbp, dtypep->rangep()->lsbp(), "must be constant");
            UASSERT_OBJ(msbp, dtypep->rangep()->msbp(), "must be constant");
            const vlsint32_t lsb = lsbp->toSInt(), msb = msbp->toSInt();
            UASSERT_OBJ(lsb <= msb, dtypep->rangep(), "lsb must not greater than msb");
            for (vlsint32_t i = 0; i <= msb - lsb; ++i) {
                const std::string name = varp->name() + "__BRA__" + cvtToStr(i) + "__KET__";
                AstVar* const newp = new AstVar(varp->fileline(), varp->varType(), name, dtypep->subDTypep());
                insertp->addNextHere(newp);
                if (newp->width() == 1) {  // no need to try splitting
                    insertp = newp;
                } else {
                    newp->addNextHere(insertp = new AstPragma(varp->fileline(), AstPragmaType::SPLIT_VAR));
                }
                vars.push_back(newp);
            }

            // refer the split variable
            for (size_t i = 0; i < it->second.size(); ++i) {
                AstArraySel* selp = it->second[i];
                AstVarRef* const vrefp = VN_CAST(selp->fromp(), VarRef);
                AstConst* const indexp = VN_CAST(selp->bitp(), Const);
                UASSERT_OBJ(vrefp && indexp, selp, "already checked");
                const uint32_t idx = indexp->toUInt();
                // V3Width:width() removes VAR_BASE attribute and make index 0-origin.
                AstVarRef* const new_vref = new AstVarRef(selp->fileline(), vars.at(idx), vrefp->lvalue());
                selp->replaceWith(new_vref); selp->deleteTree(); VL_DANGLING(selp);
            }
            varp->unlinkFrBack()->deleteTree(); VL_DANGLING(varp);
            ++m_numSplit;
        }
        m_refs.clear();  // done
    }

public:
    SplitUnpackedVarVisitor(AstNetlist* nodep, bool firstRun)
        : m_modp(NULL)
        , m_lastVarp(NULL)
        , m_numSplit(0)
        , m_firstRun(firstRun) {
        iterate(nodep);
    }
    ~SplitUnpackedVarVisitor() {
        UASSERT(m_refs.empty(), "Don't forget to call split()");
        if (m_firstRun)
            V3Stats::addStat("SplitVar, Split Unpacked Array", m_numSplit);
    }
    int numSplit() const { return m_numSplit; }
    VL_DEBUG_FUNC;  // Declare debug()

    // Check if the passed variable can be split.
    // Even if this function returns true, the variable may not be split
    // because the access to the variable cannot be determined statically.
    static bool canSplit(const AstVar* nodep) {
        if (AstNodeDType* dtypep = nodep->subDTypep()) {
            const std::pair<uint32_t, uint32_t> dim = nodep->dtypep()->dimensions(false);
            // Traced or public variable cannot be split.
            // at least one unpacked dimension must exist
            return dim.second >= 1 && !nodep->isSigPublic() && !nodep->isTrace();
        }
        return false;
    }
};

//######################################################################
//  Split packed variables

// Split variable
class SplitNewVar {
    int m_lsb;  // lsb in the original bitvector
    int m_bitwidth;
    AstVar* m_varp;  // the LSB of this variable is always 0, not m_lsb
public:
    SplitNewVar(int lsb, int bitwidth, AstVar* varp = NULL)
        : m_lsb(lsb)
        , m_bitwidth(bitwidth)
        , m_varp(varp) {}
    int lsb() const { return m_lsb; }
    int msb() const { return m_lsb + m_bitwidth - 1; }
    int bitwidth() const { return m_bitwidth; }
    void varp(AstVar* vp) {
        UASSERT_OBJ(!m_varp, m_varp, "must be NULL");
        m_varp = vp;
    }
    AstVar* varp() const { return m_varp; }

    struct Match {
        bool operator()(int bit, const SplitNewVar& a) const {
            return bit < a.m_lsb + a.m_bitwidth;
        }
    };
};

// How a variable is used
class PackedVarRef {
public:
    // one Entry instance for an AstVarRef instance
    class Entry {
        AstNode* m_nodep;  // either AstSel or AstVarRef is expected.
        int m_lsb;
        int m_bitwidth;

    public:
        Entry(AstSel* selp, int lsb, int bitwidth)
            : m_nodep(selp)
            , m_lsb(lsb)
            , m_bitwidth(bitwidth) {}
        Entry(AstVarRef* refp, int lsb, int bitwidth)
            : m_nodep(refp)
            , m_lsb(lsb)
            , m_bitwidth(bitwidth) {}
        AstNode* nodep() const { return m_nodep; }
        int lsb() const { return m_lsb; }
        int msb() const { return m_lsb + m_bitwidth - 1; }
        int bitwidth() const { return m_bitwidth; }
        void replaceNodeWith(AstNode* nodep) {
            m_nodep->replaceWith(nodep);
            m_nodep->deleteTree();
            VL_DANGLING(m_nodep);
        }
    };
private:
    struct SortByFirst {
        bool operator()(const std::pair<int, bool>& a, const std::pair<int, bool>& b) const {
            if (a.first == b.first) return a.second < b.second;
            return a.first < b.first;
        }
    };
    std::vector<Entry> m_lhs, m_rhs;

public:
    typedef std::vector<Entry>::iterator iterator;
    typedef std::vector<Entry>::const_iterator const_iterator;
    std::vector<Entry>& lhs() { return m_lhs; }
    std::vector<Entry>& rhs() { return m_rhs; }
    void append(const Entry& e, bool lvalue) {
        if (lvalue)
            m_lhs.push_back(e);
        else
            m_rhs.push_back(e);
    }
    // make a plan for variables after split
    std::vector<SplitNewVar> splitPlan() const {
        std::vector<SplitNewVar> plan;

        std::vector<std::pair<int, bool> > points;  // <bit location, is end>
        points.reserve(m_lhs.size() * 2);  // 2 points will be added per one Entry
        for (const_iterator it = m_lhs.begin(), itend = m_lhs.end(); it != itend; ++it) {
            points.push_back(std::make_pair(it->lsb(), false));     // start of a region
            points.push_back(std::make_pair(it->msb() + 1, true));  // end of a region
        }
        std::sort(points.begin(), points.end(), SortByFirst());

        // scan the sorted points and sub bitfields
        int refcount = 0;
        for (size_t i = 0; i + 1 < points.size(); ++i) {
            const int bitwidth = points[i + 1].first - points[i].first;
            if (points[i].second)
                --refcount;  // end of a region
            else
                ++refcount;  // start of a region
            UASSERT(refcount >= 0, "refcounut must not be negative");
            if (bitwidth == 0 || refcount == 0) continue;  // vacant region
            plan.push_back(SplitNewVar(points[i].first, bitwidth));
        }

        return plan;
    }
};

class SplitPackedVarVisitor : public AstNVisitor {
    AstNetlist* m_netp;
    AstNodeModule* m_modp;  // current module (just for log)
    AstVar* m_lastVarp;     // the most recently declared variable
    int m_numSplit;         // total number of split variable
    bool m_isLhs;           // true when traversing LHS of assignment
    // key:variable to be split. value:location where the variable is referenced.
    vl_unordered_map<AstVar*, PackedVarRef> m_refs;
    virtual void visit(AstNode* nodep) VL_OVERRIDE { iterateChildren(nodep); }
    virtual void visit(AstAssign* nodep) VL_OVERRIDE {
        UASSERT_OBJ(m_isLhs == false, nodep, "unexpected nested assign");
        m_isLhs = true;
        iterate(nodep->lhsp());
        m_isLhs = false;
        iterate(nodep->rhsp());
    }
    virtual void visit(AstAssignW* nodep) VL_OVERRIDE {
        UASSERT_OBJ(m_isLhs == false, nodep, "unexpected nested assign");
        m_isLhs = true;
        iterate(nodep->lhsp());
        m_isLhs = false;
        iterate(nodep->rhsp());
    }
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        UASSERT_OBJ(m_modp == NULL, m_modp, "Nested module declration");
        m_modp = nodep;
        m_lastVarp = NULL;
        UINFO(3, "Start analyzing module " << nodep->prettyName() << '\n');
        iterateChildren(nodep);
        split();
        m_modp = NULL;
    }
    virtual void visit(AstVar* nodep) VL_OVERRIDE { m_lastVarp = nodep; }
    virtual void visit(AstPragma* pragmap) VL_OVERRIDE {
        if (pragmap->pragType() != AstPragmaType::SPLIT_VAR) return;  // nothing to do
        UASSERT_OBJ(m_lastVarp, pragmap,
                    "Stray pragma must have been consumed in SplitUnpackedVarVisitor");
        if (!canSplit(m_lastVarp, true)) {
            pragmap->v3warn(SPLITVAR,
                            "Pragma split_var is specified on a variable whose type is not supported. "
                            "Packed portion must be an aggregate type of bit or logic.");
        } else {  // finally find a good candidate
            UINFO(3, m_lastVarp->prettyNameQ() << " is added to candidate list.\n");
            m_refs.insert(std::make_pair(m_lastVarp, PackedVarRef()));
        }
        m_lastVarp = NULL;
        pragmap->unlinkFrBack()->deleteTree();  // consume the pragma here anyway.
    }
    virtual void visit(AstVarRef* nodep) VL_OVERRIDE {
        AstVar* const varp = nodep->varp();
        if (m_refs.find(varp) == m_refs.end()) return;  // variable without split_var pragma
        PackedVarRef& refs = m_refs[varp];
        UASSERT_OBJ(nodep->lvalue() == m_isLhs, nodep,
                    (m_isLhs ? 'l' : 'r') << "value is expected");
        refs.append(PackedVarRef::Entry(nodep, 0, varp->width()), m_isLhs);
    }
    virtual void visit(AstSel* nodep) VL_OVERRIDE {
        AstVarRef* const vrefp = VN_CAST(nodep->fromp(), VarRef);
        if (!vrefp) return;

        AstVar* const varp = vrefp->varp();
        if (m_refs.find(varp) == m_refs.end()) return;  // variable without split_var pragma

        AstConst* const consts[2] = {constifyIfNot(nodep->lsbp()), constifyIfNot(nodep->widthp())};

        if (consts[0] && consts[1]) {  // OK
            PackedVarRef& refs = m_refs[varp];
            refs.append(PackedVarRef::Entry(nodep, consts[0]->toSInt(), consts[1]->toUInt()), m_isLhs);
        } else {
            nodep->v3warn(SPLITVAR,
                          "Variable " << vrefp->prettyNameQ() << " will not be split"
                          " because bit range cannot be determined statically.");
            m_refs.erase(varp);
        }
    }
    // extract necessary bit range from a newly created variable to meet ref
    static AstNode* extractBits(const PackedVarRef::Entry& ref, const SplitNewVar& var, bool lvalue) {
        AstVarRef* const refp = new AstVarRef(ref.nodep()->fileline(), var.varp(), lvalue);
        if (ref.lsb() <= var.lsb() && var.msb() <= ref.msb()) {  // use the entire bits
            return refp;
        } else {  // use slice
            const int lsb = std::max(ref.lsb(), var.lsb());
            const int msb = std::min(ref.msb(), var.msb());
            const int bitwidth = msb + 1 - lsb;
            UINFO(4, var.varp()->prettyNameQ() << "[" << msb << ":" << lsb << "] used for "
                                               << ref.nodep()->prettyNameQ() << '\n');
            // LSB of varp is always 0. "lsb - var.lsb()" means this. see also SplitNewVar
            AstSel* const selp = new AstSel(ref.nodep()->fileline(), refp, lsb - var.lsb(), bitwidth);
            return selp;
        }
    }
    // The actual splitting operation is done in this function.
    void split() {
        for (vl_unordered_map<AstVar*, PackedVarRef>::iterator it = m_refs.begin(),
                                                               it_end = m_refs.end();
             it != it_end; ++it) {
            AstVar* const varp = it->first;
            UINFO(3, "In module " << m_modp->name() << " var " << varp->prettyNameQ()
                                  << " which has " << it->second.lhs().size() << " lhs refs and "
                                  << it->second.rhs().size() << " rhs refs will be split.\n");
            typedef std::vector<SplitNewVar> NewVars;  // sorted by its lsb
            NewVars vars = it->second.splitPlan();
            if (vars.empty())
                continue;
            // Add the split variables
            for (size_t i = 0; i < vars.size(); ++i) {
                const int lsb = vars[i].lsb();
                const int msb = vars[i].msb();
                const std::string name = varp->name() + "__BRA__" + cvtToStr(msb) + '_' + cvtToStr(lsb) + "__KET__";

                AstBasicDType* dtypep;
                switch (varp->subDTypep()->basicp()->keyword().m_e) {
                case AstBasicDTypeKwd::BIT:
                    dtypep = new AstBasicDType(varp->subDTypep()->fileline(), VFlagBitPacked(), msb - lsb + 1);
                    break;
                case AstBasicDTypeKwd::LOGIC:
                    dtypep = new AstBasicDType(varp->subDTypep()->fileline(), VFlagLogicPacked(), msb - lsb + 1);
                    break;
                default:
                    UASSERT_OBJ(false, varp->subDTypep()->basicp(), "Only bit and logic are allowed");
                }
                vars[i].varp(new AstVar(varp->fileline(), varp->varType(), name, dtypep));
                m_netp->typeTablep()->addTypesp(dtypep);
                varp->addNextHere(vars[i].varp());
                UINFO(4, vars[i].varp()->prettyNameQ() << " is added for " << varp->prettyNameQ() << '\n');
            }

            for (int lvalue = 0; lvalue <= 1; ++lvalue) {  // refer the new split variables
                std::vector<PackedVarRef::Entry>& refs = lvalue ? it->second.lhs() : it->second.rhs();
                for (PackedVarRef::iterator refit = refs.begin(), refitend = refs.end();
                     refit != refitend; ++refit) {
                    NewVars::const_iterator varit = std::upper_bound(vars.begin(), vars.end(), refit->lsb(),
                                                                     SplitNewVar::Match());
                    UASSERT_OBJ(varit != vars.end(), refit->nodep(), "Not found");
                    UASSERT(!(varit->msb() < refit->lsb() || refit->msb() < varit->lsb()), "wrong search result");
                    AstNode* prev = extractBits(*refit, *varit, lvalue);
                    for (int residue = refit->msb() - varit->msb(); residue > 0; residue -= varit->bitwidth()) {
                        ++varit;
                        UASSERT_OBJ(varit != vars.end(), refit->nodep(), "not enough split variables");
                        AstNode* const bitsp = extractBits(*refit, *varit, lvalue);
                        prev = new AstConcat(refit->nodep()->fileline(), bitsp, prev);
                    }
                    refit->replaceNodeWith(prev);
                    UASSERT_OBJ(varit->msb() >= refit->msb(), varit->varp(), "Out of range");
                }
            }
            ++m_numSplit;
        }
        m_refs.clear();  // done
    }

public:
    explicit SplitPackedVarVisitor(AstNetlist* nodep)
        : m_netp(nodep)
        , m_modp(NULL)
        , m_lastVarp(NULL)
        , m_numSplit(0)
        , m_isLhs(false) {
        iterate(nodep);
    }
    ~SplitPackedVarVisitor() {
        UASSERT(m_refs.empty(), "Don't forget to call split()");
        V3Stats::addStat("SplitVar, Split Packed variables", m_numSplit);
    }

    // Check if the passed variable can be split.
    // Even if this function returns true, the variable may not be split
    // when the access to the variable cannot be determined statically.
    static bool canSplit(const AstVar* nodep, bool checkUnpacked) {
        if (AstBasicDType* const basicp = nodep->dtypep()->basicp()) {
            // floating point, string are not supported
            const std::pair<uint32_t, uint32_t> dim = nodep->dtypep()->dimensions(false);
            // unpacked array will be split in  SplitUnpackedVarVisitor() beforehand.
            return (!checkUnpacked || dim.second == 0) && nodep->dtypep()->widthMin() > 1 &&
                basicp->isBitLogic() && !nodep->isSigPublic() && !nodep->isTrace();
        }
        return false;
    }
    VL_DEBUG_FUNC;  // Declare debug()
};

//######################################################################
// Split class functions
void V3SplitVar::splitUnpackedVariable(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    // SplitUnpackedVarVisitor collapses one-dimension per one scan. so repeat until nothing to do.
    for (int trial = 0, done = 0; done == 0 ; ++trial) {
        {
            SplitUnpackedVarVisitor visitor(nodep, trial == 0);
            UINFO(3, visitor.numSplit() << " variables are split in trial " << trial << '\n');
            if (visitor.numSplit() == 0) done = 1;  // nothing to do anymore
        }  // Destruct before checking
        V3Global::dumpCheckGlobalTree("split_var", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
    }
}

void V3SplitVar::splitPackedVariable(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    {
        SplitPackedVarVisitor visitor(nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("split_var", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}

bool V3SplitVar::canSplitVar(const AstVar* varp) {
    return SplitUnpackedVarVisitor::canSplit(varp) || SplitPackedVarVisitor::canSplit(varp, false);
}
