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
// Find a variable with pragma

// the following code
//     logic [7:0] var0 = 8'b0; /* verilator split_var*/
// generates AST like:
//
//    1:2: VAR  var0 VAR
//    1:2: INITIAL
//    1:2:1: ASSIGN
//    1:2:1:1: CONST
//    1:2:1:2: VARREF var0 [LV]
//    1:2: PRAGMA  <= PRAGMA comes after the initial VARREF
//
// To catch all VARREF, 2-pass scan is used.
// 1st scan:Just collect VAR and PRAGMA
// 2nd scan:Actual splitting

class ScanPragmaVisitor : public AstNVisitor {
    AstVar* m_lastVarp;  // the most recently declared variable
    std::vector<std::pair<AstPragma*, AstVar*> > m_vars;
    virtual void visit(AstNode* nodep) VL_OVERRIDE { iterateChildren(nodep); }
    virtual void visit(AstModule* nodep) VL_OVERRIDE {
        UASSERT_OBJ(nodep == NULL, nodep, "This class must be used within a module");
    }
    virtual void visit(AstVar* nodep) VL_OVERRIDE { m_lastVarp = nodep; }
    virtual void visit(AstPragma* pragmap) VL_OVERRIDE {
        if (pragmap->pragType() != AstPragmaType::SPLIT_VAR) return;  // nothing to do
        // when m_lastVarp == NULL, the pragma is stray pragma.
        m_vars.push_back(std::make_pair(pragmap, m_lastVarp));
        m_lastVarp = NULL;
    }
    ScanPragmaVisitor()
        : m_lastVarp(NULL) {}

public:
    static std::vector<std::pair<AstPragma*, AstVar*> > scan(AstNodeModule* modp) {
        ScanPragmaVisitor v;
        v.iterateChildren(modp);
        return v.m_vars;
    }
};

//######################################################################
// Split Unpacked Variables

class SplitUnpackedVarVisitor : public AstNVisitor {
    AstNodeModule* m_modp;  // current module
    int m_numSplit;   // total number of split variable
    bool m_firstRun;  // true for the first pass
    // key:variable to be split. value:location where the variable is referenced.
    vl_unordered_map<AstVar*, std::vector<AstArraySel*> > m_refs;

    virtual void visit(AstNode* nodep) VL_OVERRIDE { iterateChildren(nodep); }
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        UASSERT_OBJ(m_modp == NULL, m_modp, "Nested module declration");
        m_modp = nodep;
        std::vector<std::pair<AstPragma*, AstVar*> > vars = ScanPragmaVisitor::scan(nodep);
        for (size_t i = 0; i < vars.size(); ++i) {
            AstPragma* const pragmap = vars[i].first;
            AstVar* const varp = vars[i].second;
            if (pragmap->pragType() != AstPragmaType::SPLIT_VAR) continue;  // nothing to do
            bool keepPragma = false;
            if (!varp) {
                pragmap->v3warn(SPLITVAR, "Stray pragma of split_var is detected.");
            } else if (!canSplit(varp)) {
                // maybe packed variable which will be split later.
                keepPragma = true;  // SplitPackedVarVisitor will read this pragma again later.
            } else {  // finally find a good candidate
                UINFO(4, varp->name() << " is added to candidate list.\n");
                m_refs.insert(std::make_pair(varp, std::vector<AstArraySel*>()));
            }
            if (!keepPragma) {
                pragmap->unlinkFrBack()->deleteTree();
                VL_DANGLING(vars[i].first);
            }
        }
        iterateChildren(nodep);
        split();
        m_modp = NULL;
    }
    virtual void visit(AstVarRef* nodep) VL_OVERRIDE {
        AstVar* const varp = nodep->varp();
        if (m_refs.find(varp) == m_refs.end()) return;  // variable without split_var pragma

        if (m_firstRun)
            nodep->v3warn(
                SPLITVAR,
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
                nodep->bitp()->v3warn(
                    SPLITVAR,
                    "Variable "
                        << vrefp->prettyNameQ()
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
            nodep->v3warn(SPLITVAR, "Variable " << vrefp->prettyNameQ()
                                                << " will not be split because slicing an "
                                                   "unpacked array is not supported yet.");
        m_refs.erase(varp);
    }
    // The actual splitting operation is done in this function.
    void split() {
        for (vl_unordered_map<AstVar*, std::vector<AstArraySel*> >::iterator it = m_refs.begin(),
                                                                             it_end = m_refs.end();
             it != it_end; ++it) {
            UINFO(3, "In module " << m_modp->name() << " var " << it->first->prettyNameQ()
                                  << " which has " << it->second.size()
                                  << " refs will be split.\n");
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
                // const std::string name = varp->name() + "__BRA__" + AstNode::encodeNumber(i + lsb) + "__KET__";
                // unpacked array is traced as var(idx).
                const std::string name = varp->name() + AstNode::encodeName('(' + cvtToStr(i + lsb) + ')');
                AstVar* const newp = new AstVar(varp->fileline(), varp->varType(), name, dtypep->subDTypep());
                newp->trace(varp->isTrace());
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
                selp->replaceWith(new_vref);
                selp->deleteTree();
                VL_DANGLING(selp);
            }
            varp->unlinkFrBack()->deleteTree();
            VL_DANGLING(varp);
            ++m_numSplit;
        }
        m_refs.clear();  // done
    }

public:
    SplitUnpackedVarVisitor(AstNetlist* nodep, bool firstRun)
        : m_modp(NULL)
        , m_numSplit(0)
        , m_firstRun(firstRun) {
        iterate(nodep);
    }
    ~SplitUnpackedVarVisitor() {
        UASSERT(m_refs.empty(), "Don't forget to call split()");
        if (m_firstRun) V3Stats::addStat("SplitVar, Split Unpacked Array", m_numSplit);
    }
    int numSplit() const { return m_numSplit; }
    VL_DEBUG_FUNC;  // Declare debug()

    // Check if the passed variable can be split.
    // Even if this function returns true, the variable may not be split
    // because the access to the variable cannot be determined statically.
    static bool canSplit(const AstVar* nodep) {
        const std::pair<uint32_t, uint32_t> dim = nodep->dtypep()->dimensions(false);
        // Public variable cannot be split.
        // at least one unpacked dimension must exist
        return dim.second >= 1 && !nodep->isSigPublic();
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
    AstBasicDType* m_basicp;  // cache the ptr since varp->dtypep()->basicp() is expensive

public:
    typedef std::vector<Entry>::iterator iterator;
    typedef std::vector<Entry>::const_iterator const_iterator;
    std::vector<Entry>& lhs() { return m_lhs; }
    std::vector<Entry>& rhs() { return m_rhs; }
    explicit PackedVarRef(AstVar* varp)
        : m_basicp(varp->dtypep()->basicp()) {}
    void append(const Entry& e, bool lvalue) {
        if (lvalue)
            m_lhs.push_back(e);
        else
            m_rhs.push_back(e);
    }
    const AstBasicDType* basicp() const { return m_basicp; }
    // make a plan for variables after split
    // when skipUnused==true, split variable for unread bits will not be created.
    std::vector<SplitNewVar> splitPlan(bool skipUnused) const {
        std::vector<SplitNewVar> plan;
        std::vector<std::pair<int, bool> > points;  // <bit location, is end>
        points.reserve(m_lhs.size() * 2 + 2);  // 2 points will be added per one Entry
        for (const_iterator it = m_lhs.begin(), itend = m_lhs.end(); it != itend; ++it) {
            points.push_back(std::make_pair(it->lsb(), false));     // start of a region
            points.push_back(std::make_pair(it->msb() + 1, true));  // end of a region
        }
        if (skipUnused && !m_rhs.empty()) {  // range to be read must be kept, so add points here
            int lsb = m_basicp->msb() + 1, msb = m_basicp->lsb() - 1;
            for (size_t i = 0; i < m_rhs.size(); ++i) {
                lsb = std::min(lsb, m_rhs[i].lsb());
                msb = std::max(msb, m_rhs[i].msb());
            }
            UASSERT_OBJ(lsb <= msb, m_basicp, "lsb:" << lsb << " msb:" << msb << " are wrong");
            points.push_back(std::make_pair(lsb, false));
            points.push_back(std::make_pair(msb + 1, true));
        }
        if (!skipUnused) {  // all bits are necessary
            points.push_back(std::make_pair(m_basicp->lsb(), false));
            points.push_back(std::make_pair(m_basicp->msb() + 1, true));
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
        UINFO(3, "Start analyzing module " << nodep->prettyName() << '\n');
        std::vector<std::pair<AstPragma*, AstVar*> > vars = ScanPragmaVisitor::scan(nodep);
        for (size_t i = 0; i < vars.size(); ++i) {
            AstPragma* const pragmap = vars[i].first;
            AstVar* const varp = vars[i].second;
            if (pragmap->pragType() != AstPragmaType::SPLIT_VAR) continue;  // nothing to do
            UASSERT_OBJ(varp, pragmap,
                        "Stray pragma must have been consumed in SplitUnpackedVarVisitor");
            if (!canSplit(varp, true)) {
                pragmap->v3warn(SPLITVAR,
                                "Pragma split_var is specified on a variable whose type is "
                                "unsupported or public. "
                                "Packed portion must be an aggregate type of bit or logic.");
            } else {  // finally find a good candidate
                UINFO(3, varp->prettyNameQ() << " is added to candidate list.\n");
                m_refs.insert(std::make_pair(varp, PackedVarRef(varp)));
            }
            pragmap->unlinkFrBack()->deleteTree();  // consume the pragma here anyway.
            VL_DANGLING(vars[i].first);
        }
        iterateChildren(nodep);
        split();
        m_modp = NULL;
    }
    virtual void visit(AstVarRef* nodep) VL_OVERRIDE {
        AstVar* const varp = nodep->varp();
        vl_unordered_map<AstVar*, PackedVarRef>::iterator refit = m_refs.find(varp);
        if (refit == m_refs.end()) return;  // variable without split_var pragma
        UASSERT_OBJ(nodep->lvalue() == m_isLhs, nodep,
                    (m_isLhs ? 'l' : 'r') << "value is expected");
        const AstBasicDType* const basicp = refit->second.basicp();
        refit->second.append(PackedVarRef::Entry(nodep, basicp->lsb(), basicp->width()), m_isLhs);
    }
    virtual void visit(AstSel* nodep) VL_OVERRIDE {
        AstVarRef* const vrefp = VN_CAST(nodep->fromp(), VarRef);
        if (!vrefp) return;

        AstVar* const varp = vrefp->varp();
        vl_unordered_map<AstVar*, PackedVarRef>::iterator refit = m_refs.find(varp);
        if (refit == m_refs.end()) return;  // variable without split_var pragma

        AstConst* const consts[2] = {constifyIfNot(nodep->lsbp()), constifyIfNot(nodep->widthp())};

        if (consts[0] && consts[1]) {  // OK
            refit->second.append(
                PackedVarRef::Entry(nodep, consts[0]->toSInt() + refit->second.basicp()->lsb(),
                                    consts[1]->toUInt()),
                m_isLhs);
        } else {
            nodep->v3warn(SPLITVAR, "Variable "
                                        << vrefp->prettyNameQ()
                                        << " will not be split"
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
            AstVar* varp = it->first;
            const AstBasicDType* const basicp = it->second.basicp();
            UINFO(3, "In module " << m_modp->name() << " var " << varp->prettyNameQ()
                                  << " which has " << it->second.lhs().size() << " lhs refs and "
                                  << it->second.rhs().size() << " rhs refs will be split.\n");
            typedef std::vector<SplitNewVar> NewVars;  // sorted by its lsb
            NewVars vars = it->second.splitPlan(!varp->isTrace());  // if traced, all bit must be kept
            if (vars.empty()) continue;
            // Add the split variables
            for (size_t i = 0; i < vars.size(); ++i) {
                SplitNewVar& var = vars[i];
                int left = var.msb(), right = var.lsb();
                if (basicp->littleEndian()) std::swap(left, right);
                const std::string name = varp->name() + "__BRA__" + AstNode::encodeNumber(left)
                                         + AstNode::encodeName(":") + AstNode::encodeNumber(right)
                                         + "__KET__";

                AstBasicDType* dtypep;
                switch (basicp->keyword().m_e) {
                case AstBasicDTypeKwd::BIT:
                    dtypep = new AstBasicDType(varp->subDTypep()->fileline(), VFlagBitPacked(), var.bitwidth());
                    break;
                case AstBasicDTypeKwd::LOGIC:
                    dtypep = new AstBasicDType(varp->subDTypep()->fileline(), VFlagLogicPacked(), var.bitwidth());
                    break;
                default: UASSERT_OBJ(false, basicp, "Only bit and logic are allowed");
                }
                dtypep->rangep(new AstRange(varp->fileline(), var.msb(), var.lsb()));
                dtypep->rangep()->littleEndian(basicp->littleEndian());
                var.varp(new AstVar(varp->fileline(), varp->varType(), name, dtypep));
                // var.varp()->trace(varp->isTrace());  // enable this line to trace split variable directly
                m_netp->typeTablep()->addTypesp(dtypep);
                varp->addNextHere(var.varp());
                UINFO(4, var.varp()->prettyNameQ()
                             << " is added for " << varp->prettyNameQ() << '\n');
            }

            for (int lvalue = 0; lvalue <= 1; ++lvalue) {  // refer the new split variables
                std::vector<PackedVarRef::Entry>& refs = lvalue ? it->second.lhs() : it->second.rhs();
                for (PackedVarRef::iterator refit = refs.begin(), refitend = refs.end();
                     refit != refitend; ++refit) {
                    NewVars::const_iterator varit = std::upper_bound(
                        vars.begin(), vars.end(), refit->lsb(), SplitNewVar::Match());
                    UASSERT_OBJ(varit != vars.end(), refit->nodep(), "Not found");
                    UASSERT(!(varit->msb() < refit->lsb() || refit->msb() < varit->lsb()), "wrong search result");
                    AstNode* prev = extractBits(*refit, *varit, lvalue);
                    for (int residue = refit->msb() - varit->msb(); residue > 0;
                         residue -= varit->bitwidth()) {
                        ++varit;
                        UASSERT_OBJ(varit != vars.end(), refit->nodep(), "not enough split variables");
                        AstNode* const bitsp = extractBits(*refit, *varit, lvalue);
                        prev = new AstConcat(refit->nodep()->fileline(), bitsp, prev);
                    }
                    refit->replaceNodeWith(prev);
                    UASSERT_OBJ(varit->msb() >= refit->msb(), varit->varp(), "Out of range");
                }
            }
            if (vars.size() == 1) {
                vars.front().varp()->trace(varp->isTrace());
            } else if (varp->isTrace()) {
                // Let's create a dedicated variable for trace which is concat of split variables
                AstVar* const traceVar = new AstVar(varp->fileline(), varp->varType(), varp->name(), varp->dtypep());
                traceVar->trace(true);
                varp->addNextHere(traceVar);
                AstNode* rhs = new AstVarRef(vars.front().varp()->fileline(), vars.front().varp(), false);
                for (size_t i = 1; i < vars.size(); ++i) {
                    rhs = new AstConcat(varp->fileline(),
                                        new AstVarRef(varp->fileline(), vars[i].varp(), false),
                                        rhs);
                }
                AstAssignW* assignp = new AstAssignW(varp->fileline(), new AstVarRef(varp->fileline(), traceVar, true), rhs);
                traceVar->addNextHere(assignp);
            }
            varp->unlinkFrBack()->deleteTree();
            VL_DANGLING(varp);
            ++m_numSplit;
        }
        m_refs.clear();  // done
    }

public:
    explicit SplitPackedVarVisitor(AstNetlist* nodep)
        : m_netp(nodep)
        , m_modp(NULL)
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
            return (!checkUnpacked || dim.second == 0) && nodep->dtypep()->widthMin() > 1
                   && basicp->isBitLogic() && !nodep->isSigPublic();
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
    for (int trial = 0, done = 0; done == 0; ++trial) {
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
