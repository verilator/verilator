// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break variables into separate words to avoid UNOPTFLAT
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2021 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3SplitVar divides a variable into multiple variables to avoid UNOPTFLAT warning
// and get better perfomance.
// Variables to be split must be marked by /*verilator split_var*/ metacomment.
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
//     // Original
//     logic [1:0] unpcked_array_var[0:1] /*verilator split_var*/;
//     always_comb begin
//        unpacked_array_var[1][0] =  unpacked_array_var[0][0]; // UNOPTFLAT warning
//        unpacked_array_var[1][1] = ~unpacked_array_var[0][1]; // UNOPTFLAT warning
//     end
//     logic [3:0] packed_var /*verilator split_var*/;
//     always_comb begin
//        if (some_cond) begin
//            packed_var = 4'b0;
//        end else begin
//            packed_var[3]   = some_input0;
//            packed_var[2:0] = some_input1;
//        end
//     end
//
// is initially converted to
//
//     // Intermediate
//     logic [1:0] unpcked_array_var0 /*verilator split_var*/;
//     logic [1:0] unpcked_array_var1 /*verilator split_var*/;
//     always_comb begin
//        unpacked_array_var1[0] =  unpacked_array_var0[0];
//        unpacked_array_var1[1] = ~unpacked_array_var0[1];
//     end
//     logic [3:0] packed_var /*verilator split_var*/;
//     always_comb begin
//        if (some_cond) begin
//            packed_var = 4'b0;
//        end else begin
//            packed_var[3]   = some_input0;
//            packed_var[2:0] = some_input1;
//        end
//     end
//
//  then converted to
//
//     // Final
//     logic unpacked_array_var0__BRA__0__KET__;
//     logic unpacked_array_var0__BRA__1__KET__;
//     logic unpacked_array_var1__BRA__0__KET__;
//     logic unpacked_array_var1__BRA__1__KET__;
//     always_comb begin
//        unpacked_array_var1__BRA__0__KET__ =  unpacked_array_var0__BRA__0__KET__;
//        unpacked_array_var1__BRA__1__KET__ = ~unpacked_array_var0__BRA__1__KET__;
//     end
//     logic       packed_var__BRA__3__KET__;
//     logic [2:0] packed_var__BRA__2_0__KET__;
//     always_comb begin
//        if (some_cond) begin
//            {packed_var__BRA__3__KET__, packed_var__BRA__2_0__KET__} = 4'b0;
//        end else begin
//            packed_var__BRA__3__KET__   = some_input0;
//            packed_var__BRA__2_0__KET__ = some_input1;
//        end
//     end
//
//
// Two visitor classes are defined here, SplitUnpackedVarVisitor and SplitPackedVarVisitor.
//
// - SplitUnpackedVarVisitor class splits unpacked arrays. ( 1) in the explanation above.)
//   "unpacked_array_var" in the example above is a target of the class.
//   The class changes AST from "Original" to "Intermediate".
//   The visitor does not change packed variables.
//   In addition to splitting unpacked arrays, the visitor collects the following information
//   for each module.
//     - AstVar
//     - AstVarRef
//     - AstSel
//   They are stored in a RefsInModule instance and will be used in SplitPackedVarVisitor.
//
// - SplitPackedVarVisitor class splits packed variables ( 2), 3), 4), and 5) in the explanation
//   above.)
//   "unpacked_array0", "unpacked_array_var1", and "packed_var" in "Intermediate" are split by the
//   class.
//   Packed variables here include the result of SplitUnpackedVarVisitor.
//   The result of this class looks like "Final" above.
//   The class visits just necessary AstNode based on RefsInModule collected in the preceding
//   SplitUnpackedVarVisitor.
//   The visitor does not have to visit the entire AST because the necessary information is
//   already in RefsInModule.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Global.h"
#include "V3SplitVar.h"
#include "V3Stats.h"

#include <algorithm>  // sort
#include <map>
#include <set>
#include <vector>

struct SplitVarImpl {
    static AstNodeAssign* newAssign(FileLine* fileline, AstNode* lhsp, AstNode* rhsp,
                                    const AstVar* varp) {
        if (varp->isFuncLocal() || varp->isFuncReturn()) {
            return new AstAssign(fileline, lhsp, rhsp);
        } else {
            return new AstAssignW(fileline, lhsp, rhsp);
        }
    }

    static const char* const notSplitMsg;

    // These check functions return valid pointer to the reason text if a variable cannot be split.

    // Check if a var type can be split
    static const char* cannotSplitVarTypeReason(AstVarType type) {
        // Only SplitUnpackedVarVisitor can split WREAL. SplitPackedVarVisitor cannot.
        const bool ok
            = type == type.VAR || type == type.WIRE || type == type.PORT || type == type.WREAL;
        if (ok) return nullptr;
        return "it is not one of variable, net, port, nor wreal";
    }

    static const char* cannotSplitVarDirectionReason(VDirection dir) {
        if (dir == VDirection::REF) return "it is a ref argument";
        if (dir == VDirection::INOUT) return "it is an inout port";
        return nullptr;
    }

    static const char* cannotSplitConnectedPortReason(AstPin* pinp) {
        AstVar* varp = pinp->modVarp();
        if (!varp) return "it is not connected";
        if (const char* reason = cannotSplitVarDirectionReason(varp->direction())) return reason;
        return nullptr;
    }

    static const char* cannotSplitTaskReason(const AstNodeFTask* taskp) {
        if (taskp->prototype()) return "the task is prototype declaration";
        if (taskp->dpiImport()) return "the task is imported from DPI-C";
        if (taskp->dpiOpenChild()) return "the task takes DPI-C open array";
        return nullptr;
    }

    static const char* cannotSplitVarCommonReason(const AstVar* varp) {
        if (AstNodeFTask* taskp = VN_CAST(varp->backp(), NodeFTask)) {
            if (const char* reason = cannotSplitTaskReason(taskp)) return reason;
        }
        if (const char* reason = cannotSplitVarTypeReason(varp->varType())) return reason;
        if (const char* reason = cannotSplitVarDirectionReason(varp->direction())) return reason;
        if (varp->isSigPublic()) return "it is public";
        if (varp->isUsedLoopIdx()) return "it is used as a loop variable";
        return nullptr;
    }

    static const char* cannotSplitPackedVarReason(const AstVar* varp);

    template <class T_ALWAYSLIKE>
    static void insertBeginCore(T_ALWAYSLIKE* ap, AstNodeStmt* stmtp, AstNodeModule* modp) {
        if (ap->isJustOneBodyStmt() && ap->bodysp() == stmtp) {
            stmtp->unlinkFrBack();
            // Insert begin-end because temp value may be inserted to this block later.
            const std::string name = "__VsplitVarBlk" + cvtToStr(modp->varNumGetInc());
            ap->addStmtp(new AstBegin(ap->fileline(), name, stmtp));
        }
    }

    static void insertBeginCore(AstInitial* initp, AstNodeStmt* stmtp, AstNodeModule* modp) {
        if (initp->isJustOneBodyStmt() && initp->bodysp() == stmtp) {
            stmtp->unlinkFrBack();
            // Insert begin-end because temp value may be inserted to this block later.
            const std::string name = "__VsplitVarBlk" + cvtToStr(modp->varNumGetInc());
            initp->replaceWith(
                new AstInitial(initp->fileline(), new AstBegin(initp->fileline(), name, stmtp)));
            VL_DO_DANGLING(initp->deleteTree(), initp);
        }
    }

    static void insertBeginIfNecessary(AstNodeStmt* stmtp, AstNodeModule* modp) {
        AstNode* backp = stmtp->backp();
        if (AstAlways* ap = VN_CAST(backp, Always)) {
            insertBeginCore(ap, stmtp, modp);
        } else if (AstAlwaysPublic* ap = VN_CAST(backp, AlwaysPublic)) {
            insertBeginCore(ap, stmtp, modp);
        } else if (AstInitial* ap = VN_CAST(backp, Initial)) {
            insertBeginCore(ap, stmtp, modp);
        }
    }

};  // SplitVarImpl

const char* const SplitVarImpl::notSplitMsg
    = " has split_var metacomment but will not be split because ";

//######################################################################
// Split Unpacked Variables
// Replacement policy:
// AstArraySel  -> Just replace with the AstVarRef for the split variable
// AstVarRef    -> Create a temporary variable and refer the variable
// AstSliceSel  -> Create a temporary variable and refer the variable

// Compare AstNode* to get deterministic ordering when showing messages.
struct AstNodeComparator {
    bool operator()(const AstNode* ap, const AstNode* bp) const {
        const int lineComp = ap->fileline()->operatorCompare(*bp->fileline());
        if (lineComp != 0) return lineComp < 0;
        return ap < bp;
    }
};

class UnpackRef final {
    // m_nodep is called in this context (AstNodeStmt, AstCell, AstNodeFTask, or AstAlways)
    AstNode* m_contextp;
    AstNode* m_nodep;  // ArraySel, SliceSel, ArrayVarRef (entire value)
    int m_index;  // for ArraySel
    int m_msb;  // for SliceSel
    int m_lsb;  // for SliceSel
    VAccess m_access;
    bool m_ftask;  // true if the reference is in function/task. false if in module.
public:
    UnpackRef(AstNode* stmtp, AstVarRef* nodep, bool ftask)
        : m_contextp{stmtp}
        , m_nodep{nodep}
        , m_index{-1}
        , m_msb{0}
        , m_lsb{1}
        , m_access{nodep->access()}
        , m_ftask{ftask} {}
    UnpackRef(AstNode* stmtp, AstArraySel* nodep, int idx, const VAccess& access, bool ftask)
        : m_contextp{stmtp}
        , m_nodep{nodep}
        , m_index{idx}
        , m_msb{0}
        , m_lsb{1}
        , m_access{access}
        , m_ftask{ftask} {}
    UnpackRef(AstNode* stmtp, AstSliceSel* nodep, int msb, int lsb, const VAccess& access,
              bool ftask)
        : m_contextp{stmtp}
        , m_nodep{nodep}
        , m_index{msb == lsb ? msb : -1}  // Equivalent to ArraySel
        , m_msb{msb}
        , m_lsb{lsb}
        , m_access{access}
        , m_ftask{ftask} {}
    AstNode* nodep() const { return m_nodep; }
    bool isSingleRef() const {
        return VN_IS(m_nodep, ArraySel) || (m_msb == m_lsb && m_lsb == m_index);
    }
    int index() const {
        UASSERT_OBJ(isSingleRef(), m_nodep, "not array sel");
        return m_index;
    }
    AstNode* context() const { return m_contextp; }
    VAccess access() const { return m_access; }
    bool ftask() const { return m_ftask; }
    bool operator<(const UnpackRef& other) const {
        return AstNodeComparator()(m_nodep, other.m_nodep);
    }
};

class UnpackRefMap final {
public:
    using MapType = std::map<AstVar*, std::set<UnpackRef>, AstNodeComparator>;
    using MapIt = MapType::iterator;
    using SetIt = MapType::value_type::second_type::iterator;

private:
    MapType m_map;
    bool addCore(AstVarRef* refp, const UnpackRef& ref) {
        AstVar* varp = refp->varp();
        UASSERT_OBJ(varp->attrSplitVar(), varp, " no split_var metacomment");
        MapIt it = m_map.find(varp);
        if (it == m_map.end()) return false;  // Not registered
        const bool ok = m_map[varp].insert(ref).second;
        return ok;
    }

public:
    // Register a variable to split
    void registerVar(AstVar* varp) {
        const bool inserted
            = m_map.insert(std::make_pair(varp, MapType::value_type::second_type())).second;
        UASSERT_OBJ(inserted, varp, "already registered");
    }
    // Register the location where a variable is used.
    bool tryAdd(AstNode* context, AstVarRef* refp, AstArraySel* selp, int idx, bool ftask) {
        return addCore(refp, UnpackRef(context, selp, idx, refp->access(), ftask));
    }
    bool tryAdd(AstNode* context, AstVarRef* refp, AstSliceSel* selp, int msb, int lsb,
                bool ftask) {
        return addCore(refp, UnpackRef(context, selp, msb, lsb, refp->access(), ftask));
    }
    bool tryAdd(AstNode* context, AstVarRef* refp, bool ftask) {
        return addCore(refp, UnpackRef(context, refp, ftask));
    }

    // Remove a variable from the list to split
    void remove(AstVar* varp) {
        UASSERT_OBJ(varp->attrSplitVar(), varp, " no split_var metacomment");
        m_map.erase(varp);
        varp->attrSplitVar(!SplitVarImpl::cannotSplitPackedVarReason(varp));
    }
    bool empty() const { return m_map.empty(); }
    void swap(UnpackRefMap& other) { other.m_map.swap(m_map); }

    MapIt begin() { return m_map.begin(); }
    MapIt end() { return m_map.end(); }
};

// Found nodes for SplitPackedVarVisitor
struct RefsInModule {
    std::set<AstVar*, AstNodeComparator> m_vars;
    std::set<AstVarRef*, AstNodeComparator> m_refs;
    std::set<AstSel*, AstNodeComparator> m_sels;

public:
    void add(AstVar* nodep) { m_vars.insert(nodep); }
    void add(AstVarRef* nodep) { m_refs.insert(nodep); }
    void add(AstSel* nodep) { m_sels.insert(nodep); }
    void remove(AstNode* nodep) {
        struct Visitor : public AstNVisitor {
            RefsInModule& m_parent;
            virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }
            virtual void visit(AstVar* nodep) override { m_parent.m_vars.erase(nodep); }
            virtual void visit(AstVarRef* nodep) override { m_parent.m_refs.erase(nodep); }
            virtual void visit(AstSel* nodep) override {
                m_parent.m_sels.erase(nodep);
                iterateChildren(nodep);
            }
            explicit Visitor(RefsInModule& p)
                : m_parent(p) {}  // Need () or GCC 4.8 false warning
        } v(*this);
        v.iterate(nodep);
    }
    void visit(AstNVisitor* visitor) {
        for (const auto& varp : m_vars) visitor->iterate(varp);
        for (auto it = m_sels.begin(), it_end = m_sels.end(); it != it_end; ++it) {
            // If m_refs includes VarRef from ArraySel, remove it
            // because the VarRef would not be visited in SplitPackedVarVisitor::visit(AstSel*).
            if (AstVarRef* refp = VN_CAST((*it)->fromp(), VarRef)) {
                m_refs.erase(refp);
            } else if (AstVarRef* refp = VN_CAST((*it)->lsbp(), VarRef)) {
                m_refs.erase(refp);
            } else if (AstVarRef* refp = VN_CAST((*it)->widthp(), VarRef)) {
                m_refs.erase(refp);
            }
            UASSERT_OBJ(reinterpret_cast<uintptr_t>((*it)->op1p()) != 1, *it, "stale");
            visitor->iterate(*it);
        }
        for (auto it = m_refs.begin(), it_end = m_refs.end(); it != it_end; ++it) {
            UASSERT_OBJ(reinterpret_cast<uintptr_t>((*it)->op1p()) != 1, *it, "stale");
            visitor->iterate(*it);
        }
    }
};

using SplitVarRefsMap = std::map<AstNodeModule*, RefsInModule, AstNodeComparator>;

class SplitUnpackedVarVisitor final : public AstNVisitor, public SplitVarImpl {
    using VarSet = std::set<AstVar*, AstNodeComparator>;
    VarSet m_foundTargetVar;
    UnpackRefMap m_refs;
    AstNodeModule* m_modp = nullptr;
    // AstNodeStmt, AstCell, AstNodeFTaskRef, or AstAlways(Public) for sensitivity
    AstNode* m_contextp = nullptr;
    AstNodeFTask* m_inFTask = nullptr;
    size_t m_numSplit = 0;
    // List for SplitPackedVarVisitor
    SplitVarRefsMap m_refsForPackedSplit;

    static AstVarRef* isTargetVref(AstNode* nodep) {
        if (AstVarRef* refp = VN_CAST(nodep, VarRef)) {
            if (refp->varp()->attrSplitVar()) return refp;
        }
        return nullptr;
    }
    static int outerMostSizeOfUnpackedArray(AstVar* nodep) {
        AstUnpackArrayDType* dtypep = VN_CAST(nodep->dtypep()->skipRefp(), UnpackArrayDType);
        UASSERT_OBJ(dtypep, nodep, "Must be unapcked array");
        return dtypep->elementsConst();
    }

    void setContextAndIterateChildren(AstNode* nodep) {
        VL_RESTORER(m_contextp);
        {
            m_contextp = nodep;
            iterateChildren(nodep);
        }
    }
    void setContextAndIterate(AstNode* contextp, AstNode* nodep) {
        VL_RESTORER(m_contextp);
        {
            m_contextp = contextp;
            iterate(nodep);
        }
    }
    void pushDeletep(AstNode* nodep) {  // overriding AstNVisitor::pusDeletep()
        UASSERT_OBJ(m_modp, nodep, "Must not nullptr");
        m_refsForPackedSplit[m_modp].remove(nodep);
        AstNVisitor::pushDeletep(nodep);
    }
    AstVar* newVar(FileLine* fl, AstVarType type, const std::string& name, AstNodeDType* dtp) {
        AstVar* varp = new AstVar(fl, type, name, dtp);
        UASSERT_OBJ(m_modp, varp, "Must not nullptr");
        m_refsForPackedSplit[m_modp].add(varp);
        return varp;
    }
    AstVarRef* newVarRef(FileLine* fl, AstVar* varp, const VAccess& access) {
        AstVarRef* refp = new AstVarRef(fl, varp, access);
        UASSERT_OBJ(m_modp, refp, "Must not nullptr");
        m_refsForPackedSplit[m_modp].add(refp);
        return refp;
    }

    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }
    virtual void visit(AstNodeModule* nodep) override {
        UINFO(4, "Start checking " << nodep->prettyNameQ() << "\n");
        if (!VN_IS(nodep, Module)) {
            UINFO(4, "Skip " << nodep->prettyNameQ() << "\n");
            return;
        }
        UASSERT_OBJ(!m_modp, m_modp, "Nested module declaration");
        UASSERT_OBJ(m_refs.empty(), nodep, "The last module didn't finish split()");
        m_modp = nodep;
        iterateChildren(nodep);
        split();
        m_modp = nullptr;
    }
    virtual void visit(AstNodeStmt* nodep) override { setContextAndIterateChildren(nodep); }
    virtual void visit(AstCell* nodep) override { setContextAndIterateChildren(nodep); }
    virtual void visit(AstAlways* nodep) override {
        if (nodep->sensesp()) {  // When visiting sensitivity list, always is the context
            setContextAndIterate(nodep, nodep->sensesp());
        }
        for (AstNode* bodysp = nodep->bodysp(); bodysp; bodysp = bodysp->nextp()) {
            iterate(bodysp);
        }
    };
    virtual void visit(AstAlwaysPublic* nodep) override {
        if (nodep->sensesp()) {  // When visiting sensitivity list, always is the context
            setContextAndIterate(nodep, nodep->sensesp());
        }
        for (AstNode* bodysp = nodep->bodysp(); bodysp; bodysp = bodysp->nextp()) {
            iterate(bodysp);
        }
    }
    virtual void visit(AstNodeFTaskRef* nodep) override {
        VL_RESTORER(m_contextp);
        {
            m_contextp = nodep;
            AstNodeFTask* ftaskp = nodep->taskp();
            UASSERT_OBJ(ftaskp, nodep, "Unlinked");
            // Iterate arguments of a function/task.
            for (AstNode *argp = nodep->pinsp(), *paramp = ftaskp->stmtsp(); argp;
                 argp = argp->nextp(), paramp = paramp ? paramp->nextp() : nullptr) {
                const char* reason = nullptr;
                AstVar* vparamp = nullptr;
                while (paramp) {
                    vparamp = VN_CAST(paramp, Var);
                    if (vparamp && vparamp->isIO()) {
                        reason = cannotSplitVarDirectionReason(vparamp->direction());
                        break;
                    }
                    paramp = paramp->nextp();
                    vparamp = nullptr;
                }
                if (!reason && !vparamp) {
                    reason = "the number of argument to the task/function mismatches";
                }
                m_foundTargetVar.clear();
                iterate(argp);
                if (reason) {
                    for (VarSet::iterator it = m_foundTargetVar.begin(),
                                          it_end = m_foundTargetVar.end();
                         it != it_end; ++it) {
                        argp->v3warn(SPLITVAR, (*it)->prettyNameQ()
                                                   << notSplitMsg << reason << ".\n");
                        m_refs.remove(*it);
                    }
                }
                m_foundTargetVar.clear();
            }
        }
    }
    virtual void visit(AstPin* nodep) override {
        UINFO(5, nodep->modVarp()->prettyNameQ() << " pin \n");
        AstNode* exprp = nodep->exprp();
        if (!exprp) return;  // Not connected pin
        m_foundTargetVar.clear();
        iterate(exprp);
        if (const char* reason = cannotSplitConnectedPortReason(nodep)) {
            for (VarSet::iterator it = m_foundTargetVar.begin(), it_end = m_foundTargetVar.end();
                 it != it_end; ++it) {
                nodep->v3warn(SPLITVAR, (*it)->prettyNameQ() << notSplitMsg << reason << ".\n");
                m_refs.remove(*it);
            }
            m_foundTargetVar.clear();
        }
    }
    virtual void visit(AstNodeFTask* nodep) override {
        UASSERT_OBJ(!m_inFTask, nodep, "Nested func/task");
        if (!cannotSplitTaskReason(nodep)) {
            m_inFTask = nodep;
            iterateChildren(nodep);
            m_inFTask = nullptr;
        }
    }
    virtual void visit(AstVar* nodep) override {
        if (!nodep->attrSplitVar()) return;  // Nothing to do
        if (!cannotSplitReason(nodep)) {
            m_refs.registerVar(nodep);
            UINFO(4, nodep->name() << " is added to candidate list.\n");
        }
        m_refsForPackedSplit[m_modp].add(nodep);
    }
    virtual void visit(AstVarRef* nodep) override {
        if (!nodep->varp()->attrSplitVar()) return;  // Nothing to do
        if (m_refs.tryAdd(m_contextp, nodep, m_inFTask)) {
            m_foundTargetVar.insert(nodep->varp());
        }
        m_refsForPackedSplit[m_modp].add(nodep);
    }
    virtual void visit(AstSel* nodep) override {
        if (VN_IS(nodep->fromp(), VarRef)) m_refsForPackedSplit[m_modp].add(nodep);
        iterateChildren(nodep);
    }
    virtual void visit(AstArraySel* nodep) override {
        if (AstVarRef* refp = isTargetVref(nodep->fromp())) {
            AstConst* indexp = VN_CAST(nodep->bitp(), Const);
            if (indexp) {  // OK
                UINFO(4, "add " << nodep << " for " << refp->varp()->prettyName() << "\n");
                if (indexp->toSInt() < outerMostSizeOfUnpackedArray(refp->varp())) {
                    m_refs.tryAdd(m_contextp, refp, nodep, indexp->toSInt(), m_inFTask);
                } else {
                    nodep->bitp()->v3warn(SPLITVAR, refp->prettyNameQ()
                                                        << notSplitMsg
                                                        << "index is out of range.\n");
                    m_refs.remove(refp->varp());
                }
            } else {
                nodep->bitp()->v3warn(SPLITVAR, refp->prettyNameQ()
                                                    << notSplitMsg
                                                    << "index cannot be determined statically.\n");
                m_refs.remove(refp->varp());
                iterate(nodep->bitp());
            }
        } else {
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstSliceSel* nodep) override {
        if (AstVarRef* refp = isTargetVref(nodep->fromp())) {
            AstUnpackArrayDType* dtypep
                = VN_CAST(refp->varp()->dtypep()->skipRefp(), UnpackArrayDType);
            // declRange() of AstSliceSel is shifted by dtypep->declRange().lo() in V3WidthSel.cpp
            // restore the original decl range here.
            const VNumRange selRange{nodep->declRange().hi() + dtypep->declRange().lo(),
                                     nodep->declRange().lo() + dtypep->declRange().lo(),
                                     nodep->declRange().littleEndian()};
            UASSERT_OBJ(dtypep->lo() <= selRange.lo() && selRange.hi() <= dtypep->hi(), nodep,
                        "Range check for AstSliceSel must have been finished in V3Width.cpp");
            UINFO(4, "add " << nodep << " for " << refp->varp()->prettyName() << "\n");
            m_refs.tryAdd(m_contextp, refp, nodep, nodep->declRange().hi(),
                          nodep->declRange().lo(), m_inFTask);
        } else {
            iterateChildren(nodep);
        }
    }
    static AstNode* toInsertPoint(AstNode* insertp) {
        if (AstNodeStmt* stmtp = VN_CAST(insertp, NodeStmt)) {
            if (!stmtp->isStatement()) insertp = stmtp->backp();
        }
        return insertp;
    }
    AstVarRef* createTempVar(AstNode* context, AstNode* nodep, AstUnpackArrayDType* dtypep,
                             const std::string& name_prefix, std::vector<AstVar*>& vars,
                             int start_idx, bool lvalue, bool ftask) {
        const std::string name
            = "__VsplitVar" + cvtToStr(m_modp->varNumGetInc()) + "__" + name_prefix;
        AstNodeAssign* assignp = VN_CAST(context, NodeAssign);
        if (assignp) {
            // "always_comb a = b;" to "always_comb begin a = b; end" so that local
            // variable can be added.
            insertBeginIfNecessary(assignp, m_modp);
        }
        AstVar* varp = newVar(nodep->fileline(), AstVarType::VAR, name, dtypep);
        // Variable will be registered in the caller side.
        UINFO(3, varp->prettyNameQ()
                     << " is created lsb:" << dtypep->lo() << " msb:" << dtypep->hi() << "\n");
        // Use AstAssign if true, otherwise AstAssignW
        const bool use_simple_assign
            = (context && VN_IS(context, NodeFTaskRef)) || (assignp && VN_IS(assignp, Assign));

        for (int i = 0; i < dtypep->elementsConst(); ++i) {
            AstNode* lhsp = newVarRef(nodep->fileline(), vars.at(start_idx + i),
                                      lvalue ? VAccess::WRITE : VAccess::READ);
            AstNode* rhsp = new AstArraySel(
                nodep->fileline(),
                newVarRef(nodep->fileline(), varp, !lvalue ? VAccess::WRITE : VAccess::READ), i);
            AstNode* refp = lhsp;
            UINFO(9, "Creating assign idx:" << i << " + " << start_idx << "\n");
            if (!lvalue) std::swap(lhsp, rhsp);
            AstNode* newassignp;
            if (use_simple_assign) {
                AstNode* insertp = toInsertPoint(context);
                newassignp = new AstAssign(nodep->fileline(), lhsp, rhsp);
                if (lvalue) {
                    // If varp is LHS, this assignment must appear after the original
                    // assignment(context).
                    insertp->addNextHere(newassignp);
                } else {
                    // If varp is RHS, this assignment comes just before the original assignment
                    insertp->addHereThisAsNext(newassignp);
                }
            } else {
                newassignp = new AstAssignW(nodep->fileline(), lhsp, rhsp);
                // Continuous assignment must be in module context.
                varp->addNextHere(newassignp);
            }
            UASSERT_OBJ(!m_contextp, m_contextp, "must be null");
            setContextAndIterate(newassignp, refp);
        }
        return newVarRef(nodep->fileline(), varp, lvalue ? VAccess::WRITE : VAccess::READ);
    }
    void connectPort(AstVar* varp, std::vector<AstVar*>& vars, AstNode* insertp) {
        UASSERT_OBJ(varp->isIO(), varp, "must be port");
        insertp = insertp ? toInsertPoint(insertp) : nullptr;
        const bool lvalue = varp->direction().isWritable();
        for (size_t i = 0; i < vars.size(); ++i) {
            AstNode* nodes[] = {
                new AstArraySel(
                    varp->fileline(),
                    newVarRef(varp->fileline(), varp, lvalue ? VAccess::WRITE : VAccess::READ), i),
                newVarRef(varp->fileline(), vars.at(i), !lvalue ? VAccess::WRITE : VAccess::READ)};
            AstNode* lhsp = nodes[lvalue ? 0 : 1];
            AstNode* rhsp = nodes[lvalue ? 1 : 0];
            AstNodeAssign* assignp = newAssign(varp->fileline(), lhsp, rhsp, varp);
            if (insertp) {
                if (lvalue) {  // Just after writing to the temporary variable
                    insertp->addNextHere(assignp);
                } else {  // Just before reading the temporary variable
                    insertp->addHereThisAsNext(assignp);
                }
            } else {
                UASSERT_OBJ(VN_IS(assignp, AssignW), varp, "must be AssginW");
                vars.at(i)->addNextHere(assignp);
            }
            setContextAndIterate(assignp, nodes[1]);
        }
    }
    size_t collapse(UnpackRefMap& refs) {
        size_t numSplit = 0;
        for (UnpackRefMap::MapIt it = refs.begin(), it_end = refs.end(); it != it_end; ++it) {
            UINFO(3, "In module " << m_modp->name() << " var " << it->first->prettyNameQ()
                                  << " which has " << it->second.size()
                                  << " refs will be split.\n");
            AstVar* varp = it->first;
            AstNode* insertp = varp;
            AstUnpackArrayDType* dtypep = VN_CAST(varp->dtypep()->skipRefp(), UnpackArrayDType);
            AstNodeDType* subTypep = dtypep->subDTypep();
            const bool needNext = VN_IS(subTypep, UnpackArrayDType);  // Still unpacked array.
            std::vector<AstVar*> vars;
            // Add the split variables
            for (vlsint32_t i = 0; i < dtypep->elementsConst(); ++i) {
                // Unpacked array is traced as var(idx), not var[idx].
                const std::string name
                    = varp->name() + AstNode::encodeName('(' + cvtToStr(i + dtypep->lo()) + ')');
                AstVar* newp = newVar(varp->fileline(), AstVarType::VAR, name, subTypep);
                newp->propagateAttrFrom(varp);
                // If varp is an IO, varp will remain and will be traced.
                newp->trace(!varp->isIO() && varp->isTrace());
                newp->funcLocal(varp->isFuncLocal() || varp->isFuncReturn());
                insertp->addNextHere(newp);
                insertp = newp;
                newp->attrSplitVar(needNext || !cannotSplitPackedVarReason(newp));
                vars.push_back(newp);
                setContextAndIterate(nullptr, newp);
            }
            for (UnpackRefMap::SetIt sit = it->second.begin(), sit_end = it->second.end();
                 sit != sit_end; ++sit) {
                AstNode* newp = nullptr;
                if (sit->isSingleRef()) {
                    newp = newVarRef(sit->nodep()->fileline(), vars.at(sit->index()),
                                     sit->access());
                } else {
                    AstVarRef* refp = VN_CAST(sit->nodep(), VarRef);
                    AstUnpackArrayDType* adtypep;
                    int lsb = 0;
                    if (refp) {
                        adtypep = VN_CAST(refp->dtypep()->skipRefp(), UnpackArrayDType);
                    } else {
                        AstSliceSel* selp = VN_CAST(sit->nodep(), SliceSel);
                        UASSERT_OBJ(selp, sit->nodep(), "Unexpected op is registered");
                        refp = VN_CAST(selp->fromp(), VarRef);
                        UASSERT_OBJ(refp, selp, "Unexpected op is registered");
                        adtypep = VN_CAST(selp->dtypep()->skipRefp(), UnpackArrayDType);
                        lsb = adtypep->lo();
                    }
                    AstVarRef* newrefp = createTempVar(sit->context(), refp, adtypep, varp->name(),
                                                       vars, lsb, refp->access(), sit->ftask());
                    newp = newrefp;
                    refp->varp()->addNextHere(newrefp->varp());
                    UINFO(3,
                          "Create " << newrefp->varp()->prettyNameQ() << " for " << refp << "\n");
                }
                sit->nodep()->replaceWith(newp);
                pushDeletep(sit->nodep());
                setContextAndIterate(sit->context(), newp->backp());
                // AstAssign is used. So assignment is necessary for each reference.
                if (varp->isIO() && (varp->isFuncLocal() || varp->isFuncReturn()))
                    connectPort(varp, vars, sit->context());
            }
            if (varp->isIO()) {
                // AssignW will be created, so just once
                if (!varp->isFuncLocal() && !varp->isFuncReturn()) {
                    connectPort(varp, vars, nullptr);
                }
                varp->attrSplitVar(!cannotSplitPackedVarReason(varp));
                m_refsForPackedSplit[m_modp].add(varp);
            } else {
                pushDeletep(varp->unlinkFrBack());
            }
            ++numSplit;
        }
        return numSplit;
    }
    void split() {
        for (int trial = 0; !m_refs.empty(); ++trial) {
            UnpackRefMap next;
            m_refs.swap(next);
            const size_t n = collapse(next);
            UINFO(2, n << " Variables are split " << trial << " th trial in "
                       << m_modp->prettyNameQ() << '\n');
            if (trial == 0) m_numSplit += n;
        }
        doDeletes();
    }

public:
    explicit SplitUnpackedVarVisitor(AstNetlist* nodep)
        : m_refs{} {
        iterate(nodep);
    }
    ~SplitUnpackedVarVisitor() override {
        UASSERT(m_refs.empty(), "Don't forget to call split()");
        V3Stats::addStat("SplitVar, Split unpacked arrays", m_numSplit);
    }
    const SplitVarRefsMap& getPackedVarRefs() const { return m_refsForPackedSplit; }
    VL_DEBUG_FUNC;  // Declare debug()

    // Check if the passed variable can be split.
    // Even if this function returns true, the variable may not be split
    // because the access to the variable cannot be determined statically.
    static const char* cannotSplitReason(const AstVar* nodep) {
        const std::pair<uint32_t, uint32_t> dim = nodep->dtypep()->dimensions(false);
        UINFO(7, nodep->prettyNameQ()
                     << " pub:" << nodep->isSigPublic() << " pri:" << nodep->isPrimaryIO()
                     << " io:" << nodep->isInoutish() << " typ:" << nodep->varType() << "\n");
        const char* reason = nullptr;
        // Public variable cannot be split.
        // at least one unpacked dimension must exist
        if (dim.second < 1 || !VN_IS(nodep->dtypep()->skipRefp(), UnpackArrayDType))
            reason = "it is not an unpacked array";
        if (!reason) reason = cannotSplitVarCommonReason(nodep);
        if (reason) {
            UINFO(5,
                  "Check " << nodep->prettyNameQ() << " cannot split because" << reason << ".\n");
        }
        return reason;
    }
};

//######################################################################
//  Split packed variables

// Split variable
class SplitNewVar final {
    int m_lsb;  // LSB in the original bitvector
    int m_bitwidth;
    AstVar* m_varp;  // The LSB of this variable is always 0, not m_lsb
public:
    SplitNewVar(int lsb, int bitwidth, AstVar* varp = nullptr)
        : m_lsb{lsb}
        , m_bitwidth{bitwidth}
        , m_varp{varp} {}
    int lsb() const { return m_lsb; }
    int msb() const { return m_lsb + m_bitwidth - 1; }
    int bitwidth() const { return m_bitwidth; }
    void varp(AstVar* vp) {
        UASSERT_OBJ(!m_varp, m_varp, "must be nullptr");
        m_varp = vp;
    }
    AstVar* varp() const { return m_varp; }

    struct Match {
        bool operator()(int bit, const SplitNewVar& a) const {
            return bit < a.m_lsb + a.m_bitwidth;
        }
    };
};

// One Entry instance for an AstVarRef instance
class PackedVarRefEntry final {
    AstNode* m_nodep;  // Either AstSel or AstVarRef is expected.
    int m_lsb;
    int m_bitwidth;

public:
    PackedVarRefEntry(AstSel* selp, int lsb, int bitwidth)
        : m_nodep{selp}
        , m_lsb{lsb}
        , m_bitwidth{bitwidth} {}
    PackedVarRefEntry(AstVarRef* refp, int lsb, int bitwidth)
        : m_nodep{refp}
        , m_lsb{lsb}
        , m_bitwidth{bitwidth} {}
    AstNode* nodep() const { return m_nodep; }
    int lsb() const { return m_lsb; }
    int msb() const { return m_lsb + m_bitwidth - 1; }
    int bitwidth() const { return m_bitwidth; }
    void replaceNodeWith(AstNode* nodep) {
        m_nodep->replaceWith(nodep);
        VL_DO_DANGLING(m_nodep->deleteTree(), m_nodep);
    }
    // If this is AstVarRef and referred in the sensitivity list of always@,
    // return the sensitivity item
    AstSenItem* backSenItemp() const {
        if (AstVarRef* refp = VN_CAST(m_nodep, VarRef)) return VN_CAST(refp->backp(), SenItem);
        return nullptr;
    }
};

// How a variable is used
class PackedVarRef final {
    struct SortByFirst {
        bool operator()(const std::pair<int, bool>& a, const std::pair<int, bool>& b) const {
            if (a.first == b.first) return a.second < b.second;
            return a.first < b.first;
        }
    };
    std::vector<PackedVarRefEntry> m_lhs, m_rhs;
    AstBasicDType* m_basicp;  // Cache the ptr since varp->dtypep()->basicp() is expensive
    bool m_dedupDone = false;
    static void dedupRefs(std::vector<PackedVarRefEntry>& refs) {
        // Use raw pointer to dedup
        std::map<AstNode*, size_t, AstNodeComparator> nodes;
        for (size_t i = 0; i < refs.size(); ++i) { nodes.emplace(refs[i].nodep(), i); }
        std::vector<PackedVarRefEntry> vect;
        vect.reserve(nodes.size());
        for (auto it = nodes.cbegin(), it_end = nodes.cend(); it != it_end; ++it) {
            vect.push_back(refs[it->second]);
        }
        refs.swap(vect);
    }

public:
    using iterator = std::vector<PackedVarRefEntry>::iterator;
    using const_iterator = std::vector<PackedVarRefEntry>::const_iterator;
    std::vector<PackedVarRefEntry>& lhs() {
        UASSERT(m_dedupDone, "cannot read before dedup()");
        return m_lhs;
    }
    std::vector<PackedVarRefEntry>& rhs() {
        UASSERT(m_dedupDone, "cannot read before dedup()");
        return m_rhs;
    }
    explicit PackedVarRef(AstVar* varp)
        : m_basicp{varp->dtypep()->basicp()} {}
    void append(const PackedVarRefEntry& e, const VAccess& access) {
        UASSERT(!m_dedupDone, "cannot add after dedup()");
        if (access.isWriteOrRW()) m_lhs.push_back(e);
        if (access.isReadOrRW()) m_rhs.push_back(e);
    }
    void dedup() {
        UASSERT(!m_dedupDone, "dedup() called twice");
        dedupRefs(m_lhs);
        dedupRefs(m_rhs);
        m_dedupDone = true;
    }
    const AstBasicDType* basicp() const { return m_basicp; }
    // Make a plan for variables after split
    // when skipUnused==true, split variable for unread bits will not be created.
    std::vector<SplitNewVar> splitPlan(bool skipUnused) const {
        UASSERT(m_dedupDone, "dedup() must be called before");
        std::vector<SplitNewVar> plan;
        std::vector<std::pair<int, bool>> points;  // <bit location, is end>
        points.reserve(m_lhs.size() * 2 + 2);  // 2 points will be added per one PackedVarRefEntry
        for (const_iterator it = m_lhs.begin(), itend = m_lhs.end(); it != itend; ++it) {
            points.emplace_back(std::make_pair(it->lsb(), false));  // Start of a region
            points.emplace_back(std::make_pair(it->msb() + 1, true));  // End of a region
        }
        if (skipUnused && !m_rhs.empty()) {  // Range to be read must be kept, so add points here
            int lsb = m_basicp->hi() + 1;
            int msb = m_basicp->lo() - 1;
            for (size_t i = 0; i < m_rhs.size(); ++i) {
                lsb = std::min(lsb, m_rhs[i].lsb());
                msb = std::max(msb, m_rhs[i].msb());
            }
            UASSERT_OBJ(lsb <= msb, m_basicp, "lsb:" << lsb << " msb:" << msb << " are wrong");
            points.emplace_back(std::make_pair(lsb, false));
            points.emplace_back(std::make_pair(msb + 1, true));
        }
        if (!skipUnused) {  // All bits are necessary
            points.emplace_back(std::make_pair(m_basicp->lo(), false));
            points.emplace_back(std::make_pair(m_basicp->hi() + 1, true));
        }
        std::sort(points.begin(), points.end(), SortByFirst());

        // Scan the sorted points and sub bitfields
        int refcount = 0;
        for (size_t i = 0; i + 1 < points.size(); ++i) {
            const int bitwidth = points[i + 1].first - points[i].first;
            if (points[i].second) {
                --refcount;  // End of a region
            } else {
                ++refcount;  // Start of a region
            }
            UASSERT(refcount >= 0, "refcounut must not be negative");
            if (bitwidth == 0 || refcount == 0) continue;  // Vacant region
            plan.emplace_back(SplitNewVar(points[i].first, bitwidth));
        }

        return plan;
    }
};

class SplitPackedVarVisitor final : public AstNVisitor, public SplitVarImpl {
    AstNetlist* m_netp;
    AstNodeModule* m_modp = nullptr;  // Current module (just for log)
    int m_numSplit = 0;  // Total number of split variables
    // key:variable to be split. value:location where the variable is referenced.
    std::map<AstVar*, PackedVarRef, AstNodeComparator> m_refs;
    virtual void visit(AstNodeFTask* nodep) override {
        if (!cannotSplitTaskReason(nodep)) iterateChildren(nodep);
    }
    virtual void visit(AstVar* nodep) override {
        if (!nodep->attrSplitVar()) return;  // Nothing to do
        if (const char* reason = cannotSplitReason(nodep, true)) {
            nodep->v3warn(SPLITVAR, nodep->prettyNameQ() << notSplitMsg << reason);
            nodep->attrSplitVar(false);
        } else {  // Finally find a good candidate
            const bool inserted = m_refs.insert(std::make_pair(nodep, PackedVarRef(nodep))).second;
            if (inserted) UINFO(3, nodep->prettyNameQ() << " is added to candidate list.\n");
        }
    }
    virtual void visit(AstVarRef* nodep) override {
        AstVar* varp = nodep->varp();
        visit(varp);
        const auto refit = m_refs.find(varp);
        if (refit == m_refs.end()) return;  // variable without split_var metacomment
        UASSERT_OBJ(varp->attrSplitVar(), varp, "split_var attribute must be attached");
        UASSERT_OBJ(!nodep->classOrPackagep(), nodep,
                    "variable in package must have been dropped beforehand.");
        const AstBasicDType* basicp = refit->second.basicp();
        refit->second.append(PackedVarRefEntry(nodep, basicp->lo(), varp->width()),
                             nodep->access());
        UINFO(5, varp->prettyName()
                     << " Entire bit of [" << basicp->lo() << "+:" << varp->width() << "] \n");
    }
    virtual void visit(AstSel* nodep) override {
        AstVarRef* vrefp = VN_CAST(nodep->fromp(), VarRef);
        if (!vrefp) {
            iterateChildren(nodep);
            return;
        }

        AstVar* varp = vrefp->varp();
        const auto refit = m_refs.find(varp);
        if (refit == m_refs.end()) {
            iterateChildren(nodep);
            return;  // Variable without split_var metacomment
        }
        UASSERT_OBJ(varp->attrSplitVar(), varp, "split_var attribute must be attached");

        std::array<AstConst*, 2> consts
            = {{VN_CAST(nodep->lsbp(), Const),
                VN_CAST(nodep->widthp(), Const)}};  // GCC 3.8.0 wants {{}}
        if (consts[0] && consts[1]) {  // OK
            refit->second.append(
                PackedVarRefEntry(nodep, consts[0]->toSInt() + refit->second.basicp()->lo(),
                                  consts[1]->toUInt()),
                vrefp->access());
            UINFO(5, varp->prettyName()
                         << " [" << consts[0]->toSInt() << ":+" << consts[1]->toSInt()
                         << "] lsb:" << refit->second.basicp()->lo() << "\n");
        } else {
            nodep->v3warn(SPLITVAR, vrefp->prettyNameQ()
                                        << notSplitMsg
                                        << "its bit range cannot be determined statically.");
            if (!consts[0]) {
                UINFO(4, "LSB " << nodep->lsbp() << " is expected to be constant, but not\n");
            }
            if (!consts[1]) {
                UINFO(4, "WIDTH " << nodep->widthp() << " is expected to be constant, but not\n");
            }
            m_refs.erase(varp);
            varp->attrSplitVar(false);
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

    // Extract necessary bit range from a newly created variable to meet ref
    static AstNode* extractBits(const PackedVarRefEntry& ref, const SplitNewVar& var,
                                const VAccess access) {
        AstVarRef* refp = new AstVarRef(ref.nodep()->fileline(), var.varp(), access);
        if (ref.lsb() <= var.lsb() && var.msb() <= ref.msb()) {  // Use the entire bits
            return refp;
        } else {  // Use slice
            const int lsb = std::max(ref.lsb(), var.lsb());
            const int msb = std::min(ref.msb(), var.msb());
            const int bitwidth = msb + 1 - lsb;
            UINFO(4, var.varp()->prettyNameQ() << "[" << msb << ":" << lsb << "] used for "
                                               << ref.nodep()->prettyNameQ() << '\n');
            // LSB of varp is always 0. "lsb - var.lsb()" means this. see also SplitNewVar
            AstSel* selp = new AstSel(ref.nodep()->fileline(), refp, lsb - var.lsb(), bitwidth);
            return selp;
        }
    }
    static void connectPortAndVar(const std::vector<SplitNewVar>& vars, AstVar* portp,
                                  AstNode* insertp) {
        for (; insertp; insertp = insertp->backp()) {
            if (AstNodeStmt* stmtp = VN_CAST(insertp, NodeStmt)) {
                if (stmtp->isStatement()) break;
            }
        }
        const bool in = portp->isReadOnly();
        for (size_t i = 0; i < vars.size(); ++i) {
            AstNode* rhsp = new AstSel(
                portp->fileline(),
                new AstVarRef(portp->fileline(), portp, !in ? VAccess::WRITE : VAccess::READ),
                vars[i].lsb(), vars[i].bitwidth());
            AstNode* lhsp = new AstVarRef(portp->fileline(), vars[i].varp(),
                                          in ? VAccess::WRITE : VAccess::READ);
            if (!in) std::swap(lhsp, rhsp);
            AstNodeAssign* assignp = newAssign(portp->fileline(), lhsp, rhsp, portp);
            if (insertp) {
                if (in) {
                    insertp->addHereThisAsNext(assignp);
                } else {
                    insertp->addNextHere(assignp);
                }
            } else {
                vars[i].varp()->addNextHere(assignp);
            }
        }
    }
    void createVars(AstVar* varp, const AstBasicDType* basicp, std::vector<SplitNewVar>& vars) {
        for (size_t i = 0; i < vars.size(); ++i) {
            SplitNewVar* newvarp = &vars[i];
            int left = newvarp->msb();
            int right = newvarp->lsb();
            if (basicp->littleEndian()) std::swap(left, right);
            const std::string name
                = (left == right)
                      ? varp->name() + "__BRA__" + AstNode::encodeNumber(left) + "__KET__"
                      : varp->name() + "__BRA__" + AstNode::encodeNumber(left)
                            + AstNode::encodeName(":") + AstNode::encodeNumber(right) + "__KET__";

            AstBasicDType* dtypep;
            switch (basicp->keyword()) {
            case AstBasicDTypeKwd::BIT:
                dtypep = new AstBasicDType(varp->subDTypep()->fileline(), VFlagBitPacked(),
                                           newvarp->bitwidth());
                break;
            case AstBasicDTypeKwd::LOGIC:
                dtypep = new AstBasicDType(varp->subDTypep()->fileline(), VFlagLogicPacked(),
                                           newvarp->bitwidth());
                break;
            default: UASSERT_OBJ(false, basicp, "Only bit and logic are allowed");
            }
            dtypep->rangep(new AstRange{varp->fileline(), VNumRange{newvarp->msb(), newvarp->lsb(),
                                                                    basicp->littleEndian()}});
            newvarp->varp(new AstVar(varp->fileline(), AstVarType::VAR, name, dtypep));
            newvarp->varp()->propagateAttrFrom(varp);
            newvarp->varp()->funcLocal(varp->isFuncLocal() || varp->isFuncReturn());
            // Enable this line to trace split variable directly:
            // newvarp->varp()->trace(varp->isTrace());
            m_netp->typeTablep()->addTypesp(dtypep);
            varp->addNextHere(newvarp->varp());
            UINFO(4, newvarp->varp()->prettyNameQ()
                         << " is added for " << varp->prettyNameQ() << '\n');
        }
    }
    static void updateReferences(AstVar* varp, PackedVarRef& ref,
                                 const std::vector<SplitNewVar>& vars) {
        for (int lvalue = 0; lvalue <= 1; ++lvalue) {  // Refer the new split variables
            std::vector<PackedVarRefEntry>& refs = lvalue ? ref.lhs() : ref.rhs();
            for (PackedVarRef::iterator refit = refs.begin(), refitend = refs.end();
                 refit != refitend; ++refit) {
                auto varit = std::upper_bound(vars.begin(), vars.end(), refit->lsb(),
                                              SplitNewVar::Match());
                UASSERT_OBJ(varit != vars.end(), refit->nodep(), "Not found");
                UASSERT(!(varit->msb() < refit->lsb() || refit->msb() < varit->lsb()),
                        "wrong search result");
                AstNode* prevp;
                bool inSentitivityList = false;
                if (AstSenItem* senitemp = refit->backSenItemp()) {
                    AstNode* oldsenrefp = senitemp->sensp();
                    oldsenrefp->replaceWith(
                        new AstVarRef(senitemp->fileline(), varit->varp(), VAccess::READ));
                    VL_DO_DANGLING(oldsenrefp->deleteTree(), oldsenrefp);
                    prevp = senitemp;
                    inSentitivityList = true;
                } else {
                    prevp = extractBits(*refit, *varit, lvalue ? VAccess::WRITE : VAccess::READ);
                }
                for (int residue = refit->msb() - varit->msb(); residue > 0;
                     residue -= varit->bitwidth()) {
                    ++varit;
                    UASSERT_OBJ(varit != vars.end(), refit->nodep(), "not enough split variables");
                    if (AstSenItem* senitemp = VN_CAST(prevp, SenItem)) {
                        prevp = new AstSenItem(
                            senitemp->fileline(), senitemp->edgeType(),
                            new AstVarRef(senitemp->fileline(), varit->varp(), VAccess::READ));
                        senitemp->addNextHere(prevp);
                    } else {
                        AstNode* bitsp
                            = extractBits(*refit, *varit, lvalue ? VAccess::WRITE : VAccess::READ);
                        prevp = new AstConcat(refit->nodep()->fileline(), bitsp, prevp);
                    }
                }
                // If varp is an argument of task/func, need to update temporary var
                // everytime the var is updated. See also another call of connectPortAndVar() in
                // split()
                if (varp->isIO() && (varp->isFuncLocal() || varp->isFuncReturn()))
                    connectPortAndVar(vars, varp, refit->nodep());
                if (!inSentitivityList) refit->replaceNodeWith(prevp);
                UASSERT_OBJ(varit->msb() >= refit->msb(), varit->varp(), "Out of range");
            }
        }
    }
    // Do the actual splitting operation
    void split() {
        for (auto it = m_refs.begin(), it_end = m_refs.end(); it != it_end; ++it) {
            it->second.dedup();
            AstVar* varp = it->first;
            UINFO(3, "In module " << m_modp->name() << " var " << varp->prettyNameQ()
                                  << " which has " << it->second.lhs().size() << " lhs refs and "
                                  << it->second.rhs().size() << " rhs refs will be split.\n");
            std::vector<SplitNewVar> vars
                = it->second.splitPlan(!varp->isTrace());  // If traced, all bit must be kept
            if (vars.empty()) continue;
            if (vars.size() == 1 && vars.front().bitwidth() == varp->width())
                continue;  // No split

            createVars(varp, it->second.basicp(), vars);  // Add the split variables

            updateReferences(varp, it->second, vars);

            if (varp->isIO()) {  // port cannot be deleted
                // If varp is a port of a module, single AssignW is sufficient
                if (!(varp->isFuncLocal() || varp->isFuncReturn()))
                    connectPortAndVar(vars, varp, nullptr);
            } else if (varp->isTrace()) {
                // Let's reuse the original variable for tracing
                AstNode* rhsp = new AstVarRef(vars.front().varp()->fileline(), vars.front().varp(),
                                              VAccess::READ);
                for (size_t i = 1; i < vars.size(); ++i) {
                    rhsp = new AstConcat(
                        varp->fileline(),
                        new AstVarRef(varp->fileline(), vars[i].varp(), VAccess::READ), rhsp);
                }
                varp->addNextHere(newAssign(varp->fileline(),
                                            new AstVarRef(varp->fileline(), varp, VAccess::WRITE),
                                            rhsp, varp));
            } else {  // the original variable is not used anymore.
                VL_DO_DANGLING(varp->unlinkFrBack()->deleteTree(), varp);
            }
            ++m_numSplit;
        }
        m_refs.clear();  // Done
    }

public:
    // When reusing the information from SplitUnpackedVarVisitor
    SplitPackedVarVisitor(AstNetlist* nodep, SplitVarRefsMap& refs)
        : m_netp{nodep} {
        // If you want ignore refs and walk the tne entire AST,
        // just call iterateChildren(m_modp) and split() for each module
        for (auto& i : refs) {
            m_modp = i.first;
            i.second.visit(this);
            split();
            m_modp = nullptr;
        }
    }
    ~SplitPackedVarVisitor() override {
        UASSERT(m_refs.empty(), "Forgot to call split()");
        V3Stats::addStat("SplitVar, Split packed variables", m_numSplit);
    }

    // Check if the passed variable can be split.
    // Even if this function returns true, the variable may not be split
    // when the access to the variable cannot be determined statically.
    static const char* cannotSplitReason(const AstVar* nodep, bool checkUnpacked) {
        const char* reason = nullptr;
        if (AstBasicDType* const basicp = nodep->dtypep()->basicp()) {
            const std::pair<uint32_t, uint32_t> dim = nodep->dtypep()->dimensions(false);
            // Unpacked array will be split in SplitUnpackedVarVisitor() beforehand
            if (!((!checkUnpacked || dim.second == 0) && nodep->dtypep()->widthMin() > 1))
                reason = "its bitwidth is 1";
            if (!reason && !basicp->isBitLogic())  // Floating point and string are not supported
                reason = "it is not an aggregate type of bit nor logic";
            if (!reason) reason = cannotSplitVarCommonReason(nodep);
        } else {
            reason = "its type is unknown";  // LCOV_EXCL_LINE
        }
        if (reason)
            UINFO(5,
                  "Check " << nodep->prettyNameQ() << " cannot split because" << reason << endl);
        return reason;
    }
    VL_DEBUG_FUNC;  // Declare debug()
};

const char* SplitVarImpl::cannotSplitPackedVarReason(const AstVar* varp) {
    return SplitPackedVarVisitor::cannotSplitReason(varp, true);
}

//######################################################################
// Split class functions

void V3SplitVar::splitVariable(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    SplitVarRefsMap refs;
    {
        SplitUnpackedVarVisitor visitor(nodep);
        refs = visitor.getPackedVarRefs();
    }
    V3Global::dumpCheckGlobalTree("split_var", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 9);
    { SplitPackedVarVisitor visitor(nodep, refs); }
    V3Global::dumpCheckGlobalTree("split_var", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 9);
}

bool V3SplitVar::canSplitVar(const AstVar* varp) {
    // If either SplitUnpackedVarVisitor or SplitPackedVarVisitor can handle,
    // then accept varp.
    return !SplitUnpackedVarVisitor::cannotSplitReason(varp)
           || !SplitPackedVarVisitor::cannotSplitReason(varp, false);
}
