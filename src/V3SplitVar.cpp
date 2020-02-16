// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break variables into separate words to avoid UNOPTFLAT
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder.  This program is free software; you can
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
//     logic [1:0] unpcked_array_var[0:1] /*verilator split_var*/;
//     always_comb begin
//        unpacked_array_var[1] = unpacked_array_var[0]; // UNOPTFLAT warning
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
// is converted to
//
//     logic [1:0] unpcked_array_var0;
//     logic [1:0] unpcked_array_var1;
//     always_comb begin
//        unpacked_array_var1 = unpacked_array_var0;
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
// </pre>
//
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

static AstNodeAssign* newAssign(FileLine* fileline, AstNode* lhs, AstNode* rhs,
                                const AstVar* varp) {
    if (varp->isFuncLocal() || varp->isFuncReturn()) {
        return new AstAssign(fileline, lhs, rhs);
    } else {
        return new AstAssignW(fileline, lhs, rhs);
    }
}

static const char* const notSplitMsg = " has split_var metacomment but will not be split because ";

// These check functions return valid pointer to the reason text if a variable cannot be split.

// Check if a var type can be split
static const char* cannotSplitVarTypeReason(AstVarType type) {
    // Only SplitUnpackedVarVisitor can split WREAL. SplitPackedVarVisitor cannot.
    const bool ok
        = type == type.VAR || type == type.WIRE || type == type.PORT || type == type.WREAL;
    if (ok) return NULL;
    return "it is not one of variable, net, port, nor wreal";
}

static const char* cannotSplitVarDirectionReason(VDirection dir) {
    if (dir == VDirection::REF) return "it is a ref argument";
    if (dir == VDirection::INOUT) return "it is an inout port";
    return NULL;
}

static const char* cannotSplitConnectedPortReason(AstPin* pinp) {
    AstVar* varp = pinp->modVarp();
    if (!varp) return "it is not connected";
    if (const char* reason = cannotSplitVarDirectionReason(varp->direction())) return reason;
    return NULL;
}

static const char* cannotSplitTaskReason(const AstNodeFTask* taskp) {
    if (taskp->prototype()) return "the task is prototype declaration";
    if (taskp->dpiImport()) return "the task is imported from DPI-C";
    if (taskp->dpiOpenChild()) return "the task takes DPI-C open array";
    return NULL;
}

static const char* cannotSplitVarCommonReason(const AstVar* varp) {
    if (AstNodeFTask* taskp = VN_CAST(varp->backp(), NodeFTask)) {
        if (const char* reason = cannotSplitTaskReason(taskp)) return reason;
    }
    if (const char* reason = cannotSplitVarTypeReason(varp->varType())) return reason;
    if (const char* reason = cannotSplitVarDirectionReason(varp->direction())) return reason;
    if (varp->isSigPublic()) return "it is public";
    if (varp->isInoutish()) return "it is bidirectional";
    if (varp->isUsedLoopIdx()) return "it is used as a loop variable";
    if (varp->isGenVar()) return "it is genvar";
    if (varp->isParam()) return "it is parameter";
    return NULL;
}

static const char* cannotSplitPackedVarReason(const AstVar* varp);

template <class ALWAYSLIKE>
void InsertBeginCore(ALWAYSLIKE* ap, AstNodeStmt* stmtp, AstNodeModule* modp) {
    if (ap->isJustOneBodyStmt() && ap->bodysp() == stmtp) {
        stmtp->unlinkFrBack();
        // Insert begin-end because temp value may be inserted to this block later.
        const std::string name = "__SplitVar__Blk" + cvtToStr(modp->varNumGetInc());
        ap->addStmtp(new AstBegin(ap->fileline(), name, stmtp));
    }
}

void InsertBeginCore(AstInitial* initp, AstNodeStmt* stmtp, AstNodeModule* modp) {
    if (initp->isJustOneBodyStmt() && initp->bodysp() == stmtp) {
        stmtp->unlinkFrBack();
        // Insert begin-end because temp value may be inserted to this block later.
        const std::string name = "__SplitVar__Blk" + cvtToStr(modp->varNumGetInc());
        initp->replaceWith(
            new AstInitial(initp->fileline(), new AstBegin(initp->fileline(), name, stmtp)));
        VL_DO_DANGLING(initp->deleteTree(), initp);
    }
}

static void InsertBeginIfNecessary(AstNodeStmt* stmtp, AstNodeModule* modp) {
    AstNode* backp = stmtp->backp();
    if (AstAlways* ap = VN_CAST(backp, Always)) {
        InsertBeginCore(ap, stmtp, modp);
    } else if (AstAlwaysPublic* ap = VN_CAST(backp, AlwaysPublic)) {
        InsertBeginCore(ap, stmtp, modp);
    } else if (AstInitial* ap = VN_CAST(backp, Initial)) {
        InsertBeginCore(ap, stmtp, modp);
    }
}

// Assume startp is a port variable, traverse until the end of port declaration.
// Returned pointer is the end of port variable.
static AstNode* toEndOfPort(AstVar* startp) {
    AstNode* lastp = startp;
    for (AstNode* nodep = startp; nodep; nodep = nodep->nextp()) {
        if (AstVar* varp = VN_CAST(nodep, Var)) {
            if (varp->direction() == VDirection::NONE) return lastp;
        } else {
            return lastp;
        }
        lastp = nodep;
    }
    return lastp;
}

//######################################################################
// Split Unpacked Variables
// Replacement policy:
// AstArraySel  -> Just replace with the AstVarRef for the split variable
// AstVarRef    -> Create a temporary variable and refer the variable
// AstSliceSel  -> Create a temporary variable and refer the variable

class UnpackRef {
    // m_nodep is called in this context (AstNodeStmt, AstCell, AstNodeFTask, or AstAlways)
    AstNode* m_context;
    AstNode* m_nodep;  // ArraySel, SliceSel, ArrayVarRef (entire value)
    int m_index;  // for ArraySel
    int m_msb;  // for SliceSel
    int m_lsb;  // for SliceSel
    bool m_lvalue;
    bool m_ftask;  // true if the reference is in function/task. false if in module.
public:
    UnpackRef(AstNode* stmtp, AstVarRef* nodep, bool ftask)
        : m_context(stmtp)
        , m_nodep(nodep)
        , m_index(-1)
        , m_msb(0)
        , m_lsb(1)
        , m_lvalue(nodep->lvalue())
        , m_ftask(ftask) {}
    UnpackRef(AstNode* stmtp, AstArraySel* nodep, int idx, bool lvalue, bool ftask)
        : m_context(stmtp)
        , m_nodep(nodep)
        , m_index(idx)
        , m_msb(0)
        , m_lsb(1)
        , m_lvalue(lvalue)
        , m_ftask(ftask) {}
    UnpackRef(AstNode* stmtp, AstSliceSel* nodep, int msb, int lsb, bool lvalue, bool ftask)
        : m_context(stmtp)
        , m_nodep(nodep)
        , m_index(msb == lsb ? msb : -1)  // Equivalent to ArraySel
        , m_msb(msb)
        , m_lsb(lsb)
        , m_lvalue(lvalue)
        , m_ftask(ftask) {}
    AstNode* nodep() const { return m_nodep; }
    bool isSingleRef() const {
        return VN_IS(m_nodep, ArraySel) || (m_msb == m_lsb && m_lsb == m_index);
    }
    int index() const {
        UASSERT_OBJ(isSingleRef(), m_nodep, "not array sel");
        return m_index;
    }
    AstNode* context() const { return m_context; }
    std::pair<int, int> range() const {
        UASSERT_OBJ(VN_IS(m_nodep, SliceSel), m_nodep, "not slice sel");
        return std::make_pair(m_msb, m_lsb);
    }
    bool lvalue() const { return m_lvalue; }
    bool ftask() const { return m_ftask; }
};

class UnpackRefMap {
public:
    struct Hash {
        size_t operator()(const UnpackRef& r) const { return reinterpret_cast<size_t>(r.nodep()); }
    };
    struct Compare {
        bool operator()(const UnpackRef& a, const UnpackRef& b) const {
            return a.nodep() == b.nodep();
        }
    };
    typedef vl_unordered_map<AstVar*, vl_unordered_set<UnpackRef, Hash, Compare> > MapType;
    typedef MapType::iterator MapIt;
    typedef MapType::value_type::second_type::iterator SetIt;

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
        return addCore(refp, UnpackRef(context, selp, idx, refp->lvalue(), ftask));
    }
    bool tryAdd(AstNode* context, AstVarRef* refp, AstSliceSel* selp, int msb, int lsb,
                bool ftask) {
        return addCore(refp, UnpackRef(context, selp, msb, lsb, refp->lvalue(), ftask));
    }
    bool tryAdd(AstNode* context, AstVarRef* refp, bool ftask) {
        return addCore(refp, UnpackRef(context, refp, ftask));
    }

    // Remove a variable from the list to split
    void remove(AstVar* varp) {
        UASSERT_OBJ(varp->attrSplitVar(), varp, " no split_var metacomment");
        const bool deleted = m_map.erase(varp) > 0;
        varp->attrSplitVar(!cannotSplitPackedVarReason(varp));
    }
    bool empty() const { return m_map.empty(); }
    void swap(UnpackRefMap& other) { other.m_map.swap(m_map); }

    MapIt begin() { return m_map.begin(); }
    MapIt end() { return m_map.end(); }
};

class ContextKeeper {
    AstNode* m_origContext;
    AstNode** m_contextp;

public:
    ContextKeeper(AstNode** contextp, AstNode* curContext)
        : m_origContext(*contextp)
        , m_contextp(contextp) {
        *contextp = curContext;
    }
    ~ContextKeeper() {  // Restore the original value.
        *m_contextp = m_origContext;
    }
};

class SplitUnpackedVarVisitor : public AstNVisitor {
    vl_unordered_set<AstVar*> m_foundTargetVar;
    UnpackRefMap m_refs;
    AstNodeModule* m_modp;
    // AstNodeStmt, AstCell, AstNodeFTaskRef, or AstAlways(Public) for sensitivity
    AstNode* m_context;
    bool m_inFTask;
    size_t m_numSplit;

    static AstVarRef* isTargetVref(AstNode* nodep) {
        if (AstVarRef* refp = VN_CAST(nodep, VarRef)) {
            if (refp->varp()->attrSplitVar()) return refp;
        }
        return NULL;
    }
    // This visitor is used before V3Const::constifyAllLint(),
    // some parameters need to be resolved here, but don't abuse this function.
    static AstConst* constifyIfNot(AstNode* nodep) {
        AstConst* constp = VN_CAST(nodep, Const);
        if (!constp) {
            UINFO(6, nodep << " is expected to be constant, but not\n");
            AstNode* constified = V3Const::constifyEdit(nodep);
            UINFO(6, "After constified:" << constified << '\n');
            constp = VN_CAST(constified, Const);
        }
        return constp;
    }
    static int outerMostSizeOfUnpackedArray(AstVar* nodep) {
        AstUnpackArrayDType* dtypep = VN_CAST(nodep->dtypep()->skipRefp(), UnpackArrayDType);
        UASSERT_OBJ(dtypep, nodep, "Must be unapcked array");
        return dtypep->msb() - dtypep->lsb() + 1;
    }

    void setContextAndIterateChildren(AstNode* nodep) {
        const ContextKeeper keeper(&m_context, nodep);
        iterateChildren(nodep);
    }
    void setContextAndIterate(AstNode* context, AstNode* nodep) {
        const ContextKeeper keeper(&m_context, context);
        iterate(nodep);
    }

    virtual void visit(AstNode* nodep) VL_OVERRIDE { iterateChildren(nodep); }
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        UINFO(4, "Start checking " << nodep->prettyNameQ() << "\n");
        if (!VN_IS(nodep, Module)) {
            UINFO(4, "Skip " << nodep->prettyNameQ() << "\n");
            return;
        }
        UASSERT_OBJ(m_modp == NULL, m_modp, "Nested module declration");
        UASSERT_OBJ(m_refs.empty(), nodep, "The last module didn't finish split()");
        m_modp = nodep;
        iterateChildren(nodep);
        split();
        m_modp = NULL;
    }
    virtual void visit(AstNodeStmt* nodep) VL_OVERRIDE { setContextAndIterateChildren(nodep); }
    virtual void visit(AstCell* nodep) VL_OVERRIDE { setContextAndIterateChildren(nodep); }
    virtual void visit(AstAlways* nodep) VL_OVERRIDE {
        if (nodep->sensesp()) {  // When visiting sensitivity list, always is the context
            setContextAndIterate(nodep, nodep->sensesp());
        }
        if (AstNode* bodysp = nodep->bodysp()) iterate(bodysp);
    };
    virtual void visit(AstAlwaysPublic* nodep) VL_OVERRIDE {
        if (nodep->sensesp()) {  // When visiting sensitivity list, always is the context
            setContextAndIterate(nodep, nodep->sensesp());
        }
        if (AstNode* bodysp = nodep->bodysp()) iterate(bodysp);
    }
    virtual void visit(AstNodeFTaskRef* nodep) VL_OVERRIDE {
        const ContextKeeper keeper(&m_context, nodep);
        AstNodeFTask* ftaskp = nodep->taskp();
        // Iterate arguments of a function/task.
        for (AstNode *arg = nodep->pinsp(), *param = ftaskp->stmtsp(); arg && param;
             arg = arg->nextp(), param = param->nextp()) {
            bool ok = false;
            const char* reason = NULL;
            if (AstVar* vparam = VN_CAST(param, Var)) {
                reason = cannotSplitVarDirectionReason(vparam->direction());
                if (!reason) iterate(arg);
            }
            if (reason) {
                m_foundTargetVar.clear();
                iterate(arg);
                for (vl_unordered_set<AstVar*>::iterator it = m_foundTargetVar.begin(),
                                                         it_end = m_foundTargetVar.end();
                     it != it_end; ++it) {
                    arg->v3warn(SPLITVAR, (*it)->prettyNameQ() << notSplitMsg << reason << ".\n");
                    m_refs.remove(*it);
                }
                m_foundTargetVar.clear();
            }
        }
    }
    virtual void visit(AstPin* nodep) VL_OVERRIDE {
        UINFO(5, nodep->modVarp()->prettyNameQ() << " pin \n");
        AstNode* exprp = nodep->exprp();
        if (!exprp) return;  // Not connected pin
        m_foundTargetVar.clear();
        iterate(exprp);
        if (const char* reason = cannotSplitConnectedPortReason(nodep)) {
            for (vl_unordered_set<AstVar*>::iterator it = m_foundTargetVar.begin(),
                                                     it_end = m_foundTargetVar.end();
                 it != it_end; ++it) {
                nodep->v3warn(SPLITVAR, (*it)->prettyNameQ() << notSplitMsg << reason << ".\n");
                m_refs.remove(*it);
            }
            m_foundTargetVar.clear();
        }
    }
    virtual void visit(AstNodeFTask* nodep) VL_OVERRIDE {
        UASSERT_OBJ(!m_inFTask, nodep, "Nested func/task");
        if (!cannotSplitTaskReason(nodep)) {
            m_inFTask = true;
            iterateChildren(nodep);
            m_inFTask = false;
        }
    }
    virtual void visit(AstVar* nodep) VL_OVERRIDE {
        if (!nodep->attrSplitVar()) return;  // Nothing to do
        if (!cannotSplitReason(nodep)) {
            m_refs.registerVar(nodep);
            UINFO(4, nodep->name() << " is added to candidate list.\n");
        }
    }
    virtual void visit(AstVarRef* nodep) VL_OVERRIDE {
        if (!nodep->varp()->attrSplitVar()) return;  // Nothing to do
        if (m_refs.tryAdd(m_context, nodep, m_inFTask)) { m_foundTargetVar.insert(nodep->varp()); }
    }
    virtual void visit(AstArraySel* nodep) VL_OVERRIDE {
        if (AstVarRef* refp = isTargetVref(nodep->fromp())) {
            // nodep->bitp() is sometimes AstSel which consists of AstAdd/Sub and parameters.
            // constify can solve it.
            AstConst* indexp = constifyIfNot(nodep->bitp());
            if (indexp) {  // OK
                UINFO(4, "add " << nodep << " for " << refp->varp()->prettyName() << "\n");
                if (indexp->toUInt() < outerMostSizeOfUnpackedArray(refp->varp())) {
                    m_refs.tryAdd(m_context, refp, nodep, indexp->toSInt(), m_inFTask);
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
    virtual void visit(AstSliceSel* nodep) VL_OVERRIDE {
        if (AstVarRef* refp = isTargetVref(nodep->fromp())) {
            AstUnpackArrayDType* dtypep
                = VN_CAST(refp->varp()->dtypep()->skipRefp(), UnpackArrayDType);
            if (dtypep->lsb() <= nodep->declRange().lo()
                && nodep->declRange().hi() <= dtypep->msb()) {  // Range is ok
                UINFO(4, "add " << nodep << " for " << refp->varp()->prettyName() << "\n");
                m_refs.tryAdd(m_context, refp, nodep, nodep->declRange().hi(),
                              nodep->declRange().lo(), m_inFTask);
            } else {
                nodep->v3warn(SPLITVAR, refp->prettyNameQ()
                                            << notSplitMsg << "index if out of range.\n");
                m_refs.remove(refp->varp());
            }
        } else {
            iterateChildren(nodep);
        }
    }
    static AstNode* toInsertPoint(AstNode* insertp) {
        if (AstNodeStmt* stmtp = VN_CAST(insertp, NodeStmt)) {
            if (!stmtp->isStatement()) insertp = stmtp->backp();
        }
        if (AstVar* varp = VN_CAST(insertp, Var)) return toEndOfPort(varp);
        return insertp;
    }
    AstVarRef* createTempVar(AstNode* context, AstNode* nodep, AstUnpackArrayDType* dtypep,
                             const std::string& name_prefix, std::vector<AstVar*>& vars,
                             int start_idx, bool lvalue, bool ftask) {
        const std::string name
            = "__SplitVar" + cvtToStr(m_modp->varNumGetInc()) + "__" + name_prefix;
        AstNodeAssign* assignp = VN_CAST(context, NodeAssign);
        if (assignp)  // "always_comb a = b;" to "always_comb begin a = b; end" so that local variable can be added.
            InsertBeginIfNecessary(assignp, m_modp);
        AstVar* varp = new AstVar(nodep->fileline(), AstVarType::VAR, name, dtypep);
        // Variable will be registered in the caller side.
        UINFO(3, varp->prettyNameQ()
                     << " is created lsb:" << dtypep->lsb() << " msb:" << dtypep->msb() << "\n");
        // Use AstAssign if true, otherwise AstAssignW
        const bool use_simple_assign
            = (context && VN_IS(context, NodeFTaskRef)) || (assignp && VN_IS(assignp, Assign));

        for (int i = 0; i <= dtypep->msb() - dtypep->lsb(); ++i) {
            AstNode* lhsp = new AstVarRef(nodep->fileline(), vars.at(start_idx + i), lvalue);
            AstNode* rhsp = new AstArraySel(nodep->fileline(),
                                            new AstVarRef(nodep->fileline(), varp, !lvalue), i);
            AstNode* refp = lhsp;
            UINFO(9, "Creating assign idx:" << i << " + " << start_idx << "\n");
            if (!lvalue) std::swap(lhsp, rhsp);
            AstNode* newassignp;
            if (use_simple_assign) {
                AstNode* insertp = toInsertPoint(context);
                newassignp = new AstAssign(nodep->fileline(), lhsp, rhsp);
                if (lvalue) {  // If varp is LHS, this assignment must appear after the original assignment(context).
                    insertp->addNextHere(newassignp);
                } else {  // If varp is RHS, this assignment comes just before the original assignment
                    insertp->addHereThisAsNext(newassignp);
                }
            } else {
                newassignp = new AstAssignW(nodep->fileline(), lhsp, rhsp);
                // Continuous assignment must be in module context.
                varp->addNextHere(newassignp);
            }
            UASSERT_OBJ(!m_context, m_context, "must be null");
            setContextAndIterate(newassignp, refp);
        }
        return new AstVarRef(nodep->fileline(), varp, lvalue);
    }
    void connectPort(AstVar* varp, std::vector<AstVar*>& vars, AstNode* insertp) {
        UASSERT_OBJ(varp->isIO(), varp, "must be port");
        insertp = insertp ? toInsertPoint(insertp) : NULL;
        const bool lvalue = varp->direction().isWritable();
        for (size_t i = 0; i < vars.size(); ++i) {
            AstNode* nodes[] = {new AstArraySel(varp->fileline(),
                                                new AstVarRef(varp->fileline(), varp, lvalue), i),
                                new AstVarRef(varp->fileline(), vars.at(i), !lvalue)};
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
            AstNode* insertp = toEndOfPort(varp);
            AstUnpackArrayDType* dtypep = VN_CAST(varp->dtypep()->skipRefp(), UnpackArrayDType);
            AstNodeDType* subTypep = dtypep->subDTypep();
            const bool needNext = VN_IS(subTypep, UnpackArrayDType);  // Still unpacked array.
            std::vector<AstVar*> vars;
            // Add the split variables
            for (vlsint32_t i = 0; i <= dtypep->msb() - dtypep->lsb(); ++i) {
                // Unpacked array is traced as var(idx), not var[idx].
                const std::string name
                    = varp->name() + AstNode::encodeName('(' + cvtToStr(i + dtypep->lsb()) + ')');
                AstVar* newp = new AstVar(varp->fileline(), AstVarType::VAR, name, subTypep);
                newp->propagateAttrFrom(varp);
                // If varp is an IO, varp will remain and will be traced.
                newp->trace(!varp->isIO() && varp->isTrace());
                newp->funcLocal(varp->isFuncLocal() || varp->isFuncReturn());
                insertp->addNextHere(newp);
                insertp = newp;
                newp->attrSplitVar(needNext || !cannotSplitPackedVarReason(newp));
                vars.push_back(newp);
                setContextAndIterate(NULL, newp);
            }
            for (UnpackRefMap::SetIt sit = it->second.begin(), sit_end = it->second.end();
                 sit != sit_end; ++sit) {
                AstNode* newp = NULL;
                if (sit->isSingleRef()) {
                    newp = new AstVarRef(sit->nodep()->fileline(), vars.at(sit->index()), sit->lvalue());
                } else {
                    AstVarRef* refp = VN_CAST(sit->nodep(), VarRef);
                    AstUnpackArrayDType* dtypep;
                    int lsb = 0;
                    if (refp) {
                        dtypep = VN_CAST(refp->dtypep()->skipRefp(), UnpackArrayDType);
                    } else  {
                        AstSliceSel* selp = VN_CAST(sit->nodep(), SliceSel);
                        UASSERT_OBJ(selp, sit->nodep(), "Unexpected op is registered");
                        refp = VN_CAST(selp->fromp(), VarRef);
                        UASSERT_OBJ(refp, selp, "Unexpected op is registered");
                        dtypep = VN_CAST(selp->dtypep()->skipRefp(), UnpackArrayDType);
                        lsb = dtypep->lsb();
                    }
                    AstVarRef* newrefp = createTempVar(sit->context(), refp, dtypep, varp->name(),
                                                       vars, lsb, refp->lvalue(), sit->ftask());
                    newp = newrefp;
                    toEndOfPort(refp->varp())->addNextHere(newrefp->varp());
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
                if (!(varp->isFuncLocal() || varp->isFuncReturn()))  // AssignW will be created, so just once
                    connectPort(varp, vars, NULL);
                varp->attrSplitVar(!cannotSplitPackedVarReason(varp));
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
        : m_refs()
        , m_modp(NULL)
        , m_context(NULL)
        , m_inFTask(false)
        , m_numSplit(0) {
        iterate(nodep);
    }
    ~SplitUnpackedVarVisitor() {
        UASSERT(m_refs.empty(), "Don't forget to call split()");
        V3Stats::addStat("SplitVar, Split unpacked arrays", m_numSplit);
    }
    VL_DEBUG_FUNC;  // Declare debug()

    // Check if the passed variable can be split.
    // Even if this function returns true, the variable may not be split
    // because the access to the variable cannot be determined statically.
    static const char* cannotSplitReason(const AstVar* nodep) {
        const std::pair<uint32_t, uint32_t> dim = nodep->dtypep()->dimensions(false);
        UINFO(7, nodep->prettyNameQ()
                     << " pub:" << nodep->isSigPublic() << " pri:" << nodep->isPrimaryIO()
                     << " io:" << nodep->isInoutish() << " typ:" << nodep->varType() << "\n");
        const char* reason = NULL;
        // Public variable cannot be split.
        // at least one unpacked dimension must exist
        if (dim.second < 1 || !VN_IS(nodep->dtypep()->skipRefp(), UnpackArrayDType))
            reason = "it is not an unpacked array";
        if (!reason) reason = cannotSplitVarCommonReason(nodep);
        if (reason) UINFO(5, "Check " << nodep->prettyNameQ()
                                      << " cannot split because" << reason << ".\n");
        return reason;

    }
};

//######################################################################
//  Split packed variables

// Split variable
class SplitNewVar {
    int m_lsb;  // LSB in the original bitvector
    int m_bitwidth;
    AstVar* m_varp;  // The LSB of this variable is always 0, not m_lsb
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

// One Entry instance for an AstVarRef instance
class PackedVarRefEntry {
    AstNode* m_nodep;  // Either AstSel or AstVarRef is expected.
    int m_lsb;
    int m_bitwidth;

public:
    PackedVarRefEntry(AstSel* selp, int lsb, int bitwidth)
        : m_nodep(selp)
        , m_lsb(lsb)
        , m_bitwidth(bitwidth) {}
    PackedVarRefEntry(AstVarRef* refp, int lsb, int bitwidth)
        : m_nodep(refp)
        , m_lsb(lsb)
        , m_bitwidth(bitwidth) {}
    AstNode* nodep() const { return m_nodep; }
    int lsb() const { return m_lsb; }
    int msb() const { return m_lsb + m_bitwidth - 1; }
    int bitwidth() const { return m_bitwidth; }
    void replaceNodeWith(AstNode* nodep) {
        m_nodep->replaceWith(nodep);
        VL_DO_DANGLING(m_nodep->deleteTree(), m_nodep);
    }
    // If this is AstVarRef and referred in the sensitivity list of always@, return the sensitivity item
    AstSenItem* backSenItemp() const {
        if (AstVarRef* refp = VN_CAST(m_nodep, VarRef)) { return VN_CAST(refp->backp(), SenItem); }
        return NULL;
    }
};

// How a variable is used
class PackedVarRef {
    struct SortByFirst {
        bool operator()(const std::pair<int, bool>& a, const std::pair<int, bool>& b) const {
            if (a.first == b.first) return a.second < b.second;
            return a.first < b.first;
        }
    };
    std::vector<PackedVarRefEntry> m_lhs, m_rhs;
    AstBasicDType* m_basicp;  // Cache the ptr since varp->dtypep()->basicp() is expensive

public:
    typedef std::vector<PackedVarRefEntry>::iterator iterator;
    typedef std::vector<PackedVarRefEntry>::const_iterator const_iterator;
    std::vector<PackedVarRefEntry>& lhs() { return m_lhs; }
    std::vector<PackedVarRefEntry>& rhs() { return m_rhs; }
    explicit PackedVarRef(AstVar* varp)
        : m_basicp(varp->dtypep()->basicp()) {}
    void append(const PackedVarRefEntry& e, bool lvalue) {
        if (lvalue)
            m_lhs.push_back(e);
        else
            m_rhs.push_back(e);
    }
    const AstBasicDType* basicp() const { return m_basicp; }
    // Make a plan for variables after split
    // when skipUnused==true, split variable for unread bits will not be created.
    std::vector<SplitNewVar> splitPlan(bool skipUnused) const {
        std::vector<SplitNewVar> plan;
        std::vector<std::pair<int, bool> > points;  // <bit location, is end>
        points.reserve(m_lhs.size() * 2 + 2);  // 2 points will be added per one PackedVarRefEntry
        for (const_iterator it = m_lhs.begin(), itend = m_lhs.end(); it != itend; ++it) {
            points.push_back(std::make_pair(it->lsb(), false));  // Start of a region
            points.push_back(std::make_pair(it->msb() + 1, true));  // End of a region
        }
        if (skipUnused && !m_rhs.empty()) {  // Range to be read must be kept, so add points here
            int lsb = m_basicp->msb() + 1, msb = m_basicp->lsb() - 1;
            for (size_t i = 0; i < m_rhs.size(); ++i) {
                lsb = std::min(lsb, m_rhs[i].lsb());
                msb = std::max(msb, m_rhs[i].msb());
            }
            UASSERT_OBJ(lsb <= msb, m_basicp, "lsb:" << lsb << " msb:" << msb << " are wrong");
            points.push_back(std::make_pair(lsb, false));
            points.push_back(std::make_pair(msb + 1, true));
        }
        if (!skipUnused) {  // All bits are necessary
            points.push_back(std::make_pair(m_basicp->lsb(), false));
            points.push_back(std::make_pair(m_basicp->msb() + 1, true));
        }
        std::sort(points.begin(), points.end(), SortByFirst());

        // Scan the sorted points and sub bitfields
        int refcount = 0;
        for (size_t i = 0; i + 1 < points.size(); ++i) {
            const int bitwidth = points[i + 1].first - points[i].first;
            if (points[i].second)
                --refcount;  // End of a region
            else
                ++refcount;  // Start of a region
            UASSERT(refcount >= 0, "refcounut must not be negative");
            if (bitwidth == 0 || refcount == 0) continue;  // Vacant region
            plan.push_back(SplitNewVar(points[i].first, bitwidth));
        }

        return plan;
    }
};

class SplitPackedVarVisitor : public AstNVisitor {
    AstNetlist* m_netp;
    AstNodeModule* m_modp;  // Current module (just for log)
    int m_numSplit;  // Total number of split variables
    // key:variable to be split. value:location where the variable is referenced.
    vl_unordered_map<AstVar*, PackedVarRef> m_refs;
    virtual void visit(AstNode* nodep) VL_OVERRIDE { iterateChildren(nodep); }
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        UASSERT_OBJ(m_modp == NULL, m_modp, "Nested module declration");
        if (!VN_IS(nodep, Module)) {
            UINFO(5, "Skip " << nodep->prettyNameQ() << "\n");
            return;
        }
        UASSERT_OBJ(m_refs.empty(), nodep, "The last module didn't finish split()");
        m_modp = nodep;
        UINFO(3, "Start analyzing module " << nodep->prettyName() << '\n');
        iterateChildren(nodep);
        split();
        m_modp = NULL;
    }
    virtual void visit(AstNodeFTask* nodep) VL_OVERRIDE {
        if (!cannotSplitTaskReason(nodep)) iterateChildren(nodep);
    }
    virtual void visit(AstVar* nodep) VL_OVERRIDE {
        if (!nodep->attrSplitVar()) return;  // nothing to do
        if (const char* reason = cannotSplitReason(nodep, true)) {
            nodep->v3warn(SPLITVAR, nodep->prettyNameQ() << notSplitMsg << reason << ".\n");
            nodep->attrSplitVar(false);
        } else {  // finally find a good candidate
            const bool inserted = m_refs.insert(std::make_pair(nodep, PackedVarRef(nodep))).second;
            if (inserted) { UINFO(3, nodep->prettyNameQ() << " is added to candidate list.\n"); }
        }
    }
    virtual void visit(AstVarRef* nodep) VL_OVERRIDE {
        AstVar* varp = nodep->varp();
        visit(varp);
        vl_unordered_map<AstVar*, PackedVarRef>::iterator refit = m_refs.find(varp);
        if (refit == m_refs.end()) return;  // variable without split_var metacomment
        UASSERT_OBJ(varp->attrSplitVar(), varp, "split_var attribute must be attached");
        UASSERT_OBJ(!nodep->packagep(), nodep,
                    "variable in package must have been dropped beforehand.");
        const AstBasicDType* basicp = refit->second.basicp();
        refit->second.append(PackedVarRefEntry(nodep, basicp->lsb(), varp->width()),
                             nodep->lvalue());
        UINFO(5, varp->prettyName()
                     << " Entire bit of [" << basicp->lsb() << ":+" << varp->width() << "] \n");
    }
    virtual void visit(AstSel* nodep) VL_OVERRIDE {
        AstVarRef* vrefp = VN_CAST(nodep->fromp(), VarRef);
        if (!vrefp) {
            iterateChildren(nodep);
            return;
        }

        AstVar* varp = vrefp->varp();
        vl_unordered_map<AstVar*, PackedVarRef>::iterator refit = m_refs.find(varp);
        if (refit == m_refs.end()) {
            iterateChildren(nodep);
            return;  // Variable without split_var metacomment
        }
        UASSERT_OBJ(varp->attrSplitVar(), varp, "split_var attribute must be attached");

        AstConst* consts[2] = {VN_CAST(nodep->lsbp(), Const), VN_CAST(nodep->widthp(), Const)};
        if (consts[0] && consts[1]) {  // OK
            refit->second.append(
                PackedVarRefEntry(nodep, consts[0]->toSInt() + refit->second.basicp()->lsb(),
                                  consts[1]->toUInt()),
                vrefp->lvalue());
            UINFO(5, varp->prettyName() << " [" << consts[0]->toSInt() << ":+"
                  << consts[1]->toSInt() << "] lsb:" << refit->second.basicp()->lsb() << "\n");
        } else {
            nodep->v3warn(SPLITVAR, vrefp->prettyNameQ() << notSplitMsg
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
    // Extract necessary bit range from a newly created variable to meet ref
    static AstNode* extractBits(const PackedVarRefEntry& ref, const SplitNewVar& var,
                                bool lvalue) {
        AstVarRef* refp = new AstVarRef(ref.nodep()->fileline(), var.varp(), lvalue);
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
    static void connectPortAndVar(const std::vector<SplitNewVar>& vars, AstVar* port, AstNode* insertp) {
        for ( ; insertp; insertp = insertp->backp()) {
            if (AstNodeStmt* stmtp = VN_CAST(insertp, NodeStmt)) {
                if (stmtp->isStatement()) break;
            }
        }
        const bool in = port->isReadOnly();
        for (size_t i = 0; i < vars.size(); ++i) {
            AstNode* rhs = new AstSel(port->fileline(), new AstVarRef(port->fileline(), port, !in),
                                      vars[i].lsb(), vars[i].bitwidth());
            AstNode* lhs = new AstVarRef(port->fileline(), vars[i].varp(), in);
            if (!in) std::swap(lhs, rhs);
            AstNodeAssign* assignp = newAssign(port->fileline(), lhs, rhs, port);
            if (insertp) {
                if (in)
                    insertp->addHereThisAsNext(assignp);
                else
                    insertp->addNextHere(assignp);
            } else {
                vars[i].varp()->addNextHere(assignp);
            }
        }
    }
    void createVars(AstVar* varp, const AstBasicDType* basicp, std::vector<SplitNewVar>& vars) {
        for (size_t i = 0; i < vars.size(); ++i) {
            SplitNewVar* newvarp = &vars[i];
            int left = newvarp->msb(), right = newvarp->lsb();
            if (basicp->littleEndian()) std::swap(left, right);
            const std::string name
                = (left == right)
                      ? varp->name() + "__BRA__" + AstNode::encodeNumber(left) + "__KET__"
                      : varp->name() + "__BRA__" + AstNode::encodeNumber(left)
                            + AstNode::encodeName(":") + AstNode::encodeNumber(right)
                            + "__KET__";

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
            dtypep->rangep(new AstRange(varp->fileline(), newvarp->msb(), newvarp->lsb()));
            dtypep->rangep()->littleEndian(basicp->littleEndian());
            newvarp->varp(new AstVar(varp->fileline(), AstVarType::VAR, name, dtypep));
            newvarp->varp()->propagateAttrFrom(varp);
            newvarp->varp()->funcLocal(varp->isFuncLocal() || varp->isFuncReturn());
            // newvarp->varp()->trace(varp->isTrace());  // Enable this line to trace split
            // variable directly
            m_netp->typeTablep()->addTypesp(dtypep);
            varp->addNextHere(newvarp->varp());
            UINFO(4, newvarp->varp()->prettyNameQ()
                         << " is added for " << varp->prettyNameQ() << '\n');
        }
    }
    static void updateReferences(AstVar* varp, PackedVarRef& ref, const std::vector<SplitNewVar> &vars) {
        typedef std::vector<SplitNewVar> NewVars;  // Sorted by its lsb
        for (int lvalue = 0; lvalue <= 1; ++lvalue) {  // Refer the new split variables
            std::vector<PackedVarRefEntry>& refs = lvalue ? ref.lhs() : ref.rhs();
            for (PackedVarRef::iterator refit = refs.begin(), refitend = refs.end();
                 refit != refitend; ++refit) {
                NewVars::const_iterator varit = std::upper_bound(
                    vars.begin(), vars.end(), refit->lsb(), SplitNewVar::Match());
                UASSERT_OBJ(varit != vars.end(), refit->nodep(), "Not found");
                UASSERT(!(varit->msb() < refit->lsb() || refit->msb() < varit->lsb()),
                        "wrong search result");
                AstNode* prev;
                bool inSentitivityList = false;
                if (AstSenItem* senitemp = refit->backSenItemp()) {
                    AstNode* oldsenrefp = senitemp->sensp();
                    oldsenrefp->replaceWith(new AstVarRef(senitemp->fileline(), varit->varp(), false));
                    VL_DO_DANGLING(oldsenrefp->deleteTree(), oldsenrefp);
                    prev = senitemp;
                    inSentitivityList = true;
                } else {
                    prev = extractBits(*refit, *varit, lvalue);
                }
                for (int residue = refit->msb() - varit->msb(); residue > 0;
                     residue -= varit->bitwidth()) {
                    ++varit;
                    UASSERT_OBJ(varit != vars.end(), refit->nodep(),
                                "not enough split variables");
                    if (AstSenItem* senitemp = VN_CAST(prev, SenItem)) {
                        prev = new AstSenItem(senitemp->fileline(), senitemp->edgeType(),
                                              new AstVarRef(senitemp->fileline(), varit->varp(), false));
                        senitemp->addNextHere(prev);
                    } else {
                        AstNode* bitsp = extractBits(*refit, *varit, lvalue);
                        prev = new AstConcat(refit->nodep()->fileline(), bitsp, prev);
                    }
                }
                // If varp is an argument of task/func, need to update temporary var
                // everytime the var is updated. See also another call of connectPortAndVar() in split().
                if (varp->isIO() && (varp->isFuncLocal() || varp->isFuncReturn()))
                    connectPortAndVar(vars, varp, refit->nodep());
                if (!inSentitivityList) refit->replaceNodeWith(prev);
                UASSERT_OBJ(varit->msb() >= refit->msb(), varit->varp(), "Out of range");
            }
        }
    }
    // The actual splitting operation is done in this function.
    void split() {
        for (vl_unordered_map<AstVar*, PackedVarRef>::iterator it = m_refs.begin(),
                                                               it_end = m_refs.end();
             it != it_end; ++it) {
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
                // If varp is a port of a module, single AssignW is sufficient.
                if (!(varp->isFuncLocal() || varp->isFuncReturn()))
                    connectPortAndVar(vars, varp, NULL);
            } else if (varp->isTrace()) {
                // Let's reuse the original variable for tracing
                AstNode* rhs
                    = new AstVarRef(vars.front().varp()->fileline(), vars.front().varp(), false);
                for (size_t i = 1; i < vars.size(); ++i) {
                    rhs = new AstConcat(varp->fileline(),
                                        new AstVarRef(varp->fileline(), vars[i].varp(), false),
                                        rhs);
                }
                varp->addNextHere(newAssign(varp->fileline(), new AstVarRef(varp->fileline(), varp, true), rhs, varp));
            } else {  // the original variable is not used anymore.
                VL_DO_DANGLING(varp->unlinkFrBack()->deleteTree(), varp);
            }
            ++m_numSplit;
        }
        m_refs.clear();  // Done
    }

public:
    explicit SplitPackedVarVisitor(AstNetlist* nodep)
        : m_netp(nodep)
        , m_modp(NULL)
        , m_numSplit(0) {
        iterate(nodep);
    }
    ~SplitPackedVarVisitor() {
        UASSERT(m_refs.empty(), "Don't forget to call split()");
        V3Stats::addStat("SplitVar, Split packed variables", m_numSplit);
    }

    // Check if the passed variable can be split.
    // Even if this function returns true, the variable may not be split
    // when the access to the variable cannot be determined statically.
    static const char* cannotSplitReason(const AstVar* nodep, bool checkUnpacked) {
        const char* reason = NULL;
        if (AstBasicDType* const basicp = nodep->dtypep()->basicp()) {
            const std::pair<uint32_t, uint32_t> dim = nodep->dtypep()->dimensions(false);
            // Unpacked array will be split in  SplitUnpackedVarVisitor() beforehand
            if (!((!checkUnpacked || dim.second == 0) && nodep->dtypep()->widthMin() > 1))
                reason = "its bitwidth is 1";
            if (!reason && !basicp->isBitLogic())  // Floating point and string are not supported
                reason = "it is not an aggregate type of bit nor logic";
            if (!reason) reason = cannotSplitVarCommonReason(nodep);
        } else {
            reason = "its type is unknown";
        }
        if (reason) UINFO(5, "Check " << nodep->prettyNameQ()
                                      << " cannot split because" << reason << ".\n");
        return reason;
    }
    VL_DEBUG_FUNC;  // Declare debug()
};

static const char* cannotSplitPackedVarReason(const AstVar* varp) {
    return SplitPackedVarVisitor::cannotSplitReason(varp, true);
}

//######################################################################
// Split class functions

void V3SplitVar::splitVariable(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { SplitUnpackedVarVisitor visitor(nodep); }
    V3Global::dumpCheckGlobalTree("split_var", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 9);
    { SplitPackedVarVisitor visitor(nodep); }
    V3Global::dumpCheckGlobalTree("split_var", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 9);
}

bool V3SplitVar::canSplitVar(const AstVar* varp) {
    return !SplitUnpackedVarVisitor::cannotSplitReason(varp)
           || !SplitPackedVarVisitor::cannotSplitReason(varp, false);
}
