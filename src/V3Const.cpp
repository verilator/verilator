// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Constant folding
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
// CONST TRANSFORMATIONS:
//   Call on one node for PARAM values, or netlist for overall constant folding:
//      Bottom up traversal:
//          Attempt to convert operands to constants
//          If operands are constant, replace this node with constant.
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3String.h"
#include "V3Const.h"
#include "V3Ast.h"
#include "V3Width.h"
#include "V3Simulate.h"
#include "V3Stats.h"

#include <algorithm>

//######################################################################
// Utilities

class ConstVarMarkVisitor final : public AstNVisitor {
    // NODE STATE
    // AstVar::user4p           -> bool, Var marked, 0=not set yet
private:
    // VISITORS
    virtual void visit(AstVarRef* nodep) override {
        if (nodep->varp()) nodep->varp()->user4(1);
    }
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ConstVarMarkVisitor(AstNode* nodep) {
        AstNode::user4ClearTree();  // Check marked InUse before we're called
        iterate(nodep);
    }
    virtual ~ConstVarMarkVisitor() override = default;
};

class ConstVarFindVisitor final : public AstNVisitor {
    // NODE STATE
    // AstVar::user4p           -> bool, input from ConstVarMarkVisitor
    // MEMBERS
    bool m_found = false;

private:
    // VISITORS
    virtual void visit(AstVarRef* nodep) override {
        if (nodep->varp() && nodep->varp()->user4()) m_found = true;
    }
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ConstVarFindVisitor(AstNode* nodep) { iterateAndNextNull(nodep); }
    virtual ~ConstVarFindVisitor() override = default;
    // METHODS
    bool found() const { return m_found; }
};

// This visitor can be used in the post-expanded Ast from V3Expand, where the Ast satisfies:
// - Constants are 64 bit at most (because words are accessed via AstWordSel)
// - Variables are scoped.
class ConstBitOpTreeVisitor final : public AstNVisitor {
    // TYPES

    struct LeafInfo {  // Leaf node (either AstConst or AstVarRef)
        bool m_polarity = true;
        int m_lsb = 0;
        int m_wordIdx = -1;  // -1 means AstWordSel is not used.
        AstVarRef* m_refp = nullptr;
        AstConst* m_constp = nullptr;
    };
    // Collect information for each Variable to transform as below
    class VarInfo final {
        // MEMBERS
        int m_constResult = -1;  // -1: result is not constant, 0 or 1: result of this tree
        ConstBitOpTreeVisitor* m_parentp;  // ConstBitOpTreeVisitor that holds this VarInfo
        AstVarRef* m_refp;  // Points the variable that this VarInfo covers
        V3Number m_bitPolarity;  // Coefficient of each bit

    public:
        // METHODS
        bool hasConstantResult() const { return m_constResult >= 0; }
        bool sameVarAs(const AstNodeVarRef* otherp) const { return m_refp->same(otherp); }
        void setPolarity(bool compBit, int bit) {
            UASSERT_OBJ(!hasConstantResult(), m_refp, "Already has result of " << m_constResult);
            UASSERT_OBJ(bit < VL_QUADSIZE, m_refp,
                        "bit:" << bit << " is too big after V3Expand"
                               << " back:" << m_refp->backp());
            if (bit >= m_bitPolarity.width()) {  // Need to expand m_bitPolarity
                const V3Number oldPol = std::move(m_bitPolarity);
                // oldPol.width() is 8, 16, or 32 because this visitor is called after V3Expand
                // newWidth is increased by 2x because
                //  - CCast will cast to such bitwidth anyway
                //  - can avoid frequent expansion
                int newWidth = oldPol.width();
                while (bit >= newWidth) newWidth *= 2;
                m_bitPolarity = V3Number{m_refp, newWidth};
                UASSERT_OBJ(newWidth == 16 || newWidth == 32 || newWidth == 64, m_refp,
                            "bit:" << bit << " newWidth:" << newWidth);
                m_bitPolarity.setAllBitsX();
                for (int i = 0; i < oldPol.width(); ++i) {
                    if (oldPol.bitIs0(i))
                        m_bitPolarity.setBit(i, '0');
                    else if (oldPol.bitIs1(i))
                        m_bitPolarity.setBit(i, '1');
                }
            }
            UASSERT_OBJ(bit < m_bitPolarity.width(), m_refp,
                        "bit:" << bit << " width:" << m_bitPolarity.width() << m_refp);
            if (m_bitPolarity.bitIsX(bit)) {  // The bit is not yet set
                m_bitPolarity.setBit(bit, compBit);
            } else {  // Priviously set the bit
                const bool sameFlag = m_bitPolarity.bitIs1(bit) == compBit;
                if (m_parentp->isXorTree()) {
                    // ^{x[0], ~x[0], x[2], x[3]} === ~^{x[2], x[3]}
                    UASSERT_OBJ(sameFlag, m_refp, "Only true is set in Xor tree");
                    m_bitPolarity.setBit(bit, 'x');
                } else {  // And, Or
                    // Can ignore this nodep as the bit is already registered
                    if (sameFlag) return;  // a & a == a, b | b == b
                    // Otherwise result is constant
                    m_constResult = m_parentp->isAndTree() ? 0 : 1;
                    m_bitPolarity.setAllBitsX();  // The variable is not referred anymore
                }
            }
        }
        AstNode* getResult() const {
            FileLine* fl = m_refp->fileline();
            AstNode* srcp = VN_CAST(m_refp->backp(), WordSel);
            if (!srcp) srcp = m_refp;
            const int width = m_bitPolarity.width();

            if (hasConstantResult())
                return new AstConst{fl,
                                    V3Number{srcp, width, static_cast<vluint32_t>(m_constResult)}};

            AstConst* maskValuep = new AstConst{fl, V3Number{srcp, width, 0}};
            maskValuep->num().opBitsNonX(m_bitPolarity);  // 'x' -> 0, 0->1, 1->1
            // Let AstConst be in lhs as it is the common convention
            AstAnd* maskedp = new AstAnd{fl, maskValuep, srcp->cloneTree(false)};
            AstNode* resultp;
            if (m_parentp->isXorTree()) {
                resultp = new AstRedXor{fl, maskedp};
                resultp->dtypep()->widthForce(width, 1);
            } else {
                AstConst* compValuep = maskValuep->cloneTree(false);
                compValuep->num().opBitsOne(m_bitPolarity);  // 'x'->0, 0->0, 1->1
                if (m_parentp->isAndTree()) {
                    resultp = new AstEq{fl, compValuep, maskedp};
                } else {  // Or
                    compValuep->num().opXor(V3Number{compValuep->num()}, maskValuep->num());
                    resultp = new AstNeq{fl, compValuep, maskedp};
                }
            }
            return resultp;
        }

        // CONSTRUCTORS
        VarInfo(ConstBitOpTreeVisitor* parent, AstVarRef* refp)
            : m_parentp(parent)
            , m_refp(refp)
            , m_bitPolarity(refp, refp->isWide() ? VL_EDATASIZE : refp->width()) {
            m_bitPolarity.setAllBitsX();
        }
    };

    // MEMBERS
    bool m_failed = false;
    bool m_polarity = true;  // Flip when AstNot comes
    int m_ops = 0;  // Number of operations such as And, Or, Xor, Sel...
    int m_lsb = 0;  // Current LSB
    LeafInfo* m_leafp = nullptr;  // AstConst or AstVarRef that currently looking for
    AstNode* m_rootp;  // Root of this AST subtree
    AstNode* m_curOpp = nullptr;  // The node that should be added to m_frozenNodes

    AstUser4InUse m_inuser4;
    std::vector<AstNode*> m_frozenNodes;  // Nodes that cannot be optimized
    std::vector<VarInfo*> m_varInfos;  // VarInfo for each variable, [0] is nullptr

    // NODE STATE
    // AstVarRef::user4u      -> Base index of m_varInfos that points VarInfo
    // AstVarScope::user4u    -> Same as AstVarRef::user4

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    bool isAndTree() const { return VN_IS(m_rootp, And); }
    bool isOrTree() const { return VN_IS(m_rootp, Or); }
    bool isXorTree() const { return VN_IS(m_rootp, Xor) || VN_IS(m_rootp, RedXor); }

#define CONST_BITOP_RETURN_IF(cond, nodep) \
    if (setFailed(cond, #cond, nodep, __LINE__)) return

#define CONST_BITOP_SET_FAILED(reason, nodep) setFailed(true, reason, nodep, __LINE__)

    bool setFailed(bool fail, const char* reason, AstNode* nodep, int line) {
        if (fail) {
            UINFO(9, "cannot optimize " << m_rootp << " reason:" << reason << " called from line:"
                                        << line << " when checking:" << nodep << std::endl);
            // if (debug() >= 9) m_rootp->dumpTree(std::cout << "Root node:\n");
        }
        m_failed |= fail;
        return m_failed;
    }
    void incrOps(const AstNode* nodep, int line) {
        ++m_ops;
        UINFO(9, "Increment to " << m_ops << " " << nodep << " called from line " << line << "\n");
    }
    VarInfo& getVarInfo(const LeafInfo& ref) {
        UASSERT_OBJ(ref.m_refp, m_rootp, "null varref in And/Or/Xor optimization");
        AstNode* nodep = ref.m_refp->varScopep();
        if (!nodep) nodep = ref.m_refp->varp();  // Not scoped
        int baseIdx = nodep->user4();
        if (baseIdx == 0) {  // Not set yet
            baseIdx = m_varInfos.size();
            const int numWords
                = ref.m_refp->dtypep()->isWide() ? ref.m_refp->dtypep()->widthWords() : 1;
            m_varInfos.resize(m_varInfos.size() + numWords, nullptr);
            nodep->user4(baseIdx);
        }
        const size_t idx = baseIdx + std::max(0, ref.m_wordIdx);
        VarInfo* varInfop = m_varInfos[idx];
        if (!varInfop) {
            varInfop = new VarInfo{this, ref.m_refp};
            m_varInfos[idx] = varInfop;
        } else {
            if (!varInfop->sameVarAs(ref.m_refp))
                CONST_BITOP_SET_FAILED("different var (scope?)", ref.m_refp);
        }
        return *varInfop;
    }

    // Traverse down to see AstConst or AstVarRef
    LeafInfo findLeaf(AstNode* nodep, bool expectConst) {
        LeafInfo info;
        {
            VL_RESTORER(m_leafp);
            m_leafp = &info;
            iterate(nodep);
        }

        bool ok = !m_failed;
        if (expectConst)
            ok &= !info.m_refp && info.m_constp;
        else
            ok &= info.m_refp && !info.m_constp;
        return ok ? info : LeafInfo{};
    }
    AstNode* combineTree(AstNode* lhsp, AstNode* rhsp) {
        if (!lhsp) return rhsp;
        if (isAndTree())
            return new AstAnd(m_rootp->fileline(), lhsp, rhsp);
        else if (isOrTree())
            return new AstOr(m_rootp->fileline(), lhsp, rhsp);
        else {
            UASSERT_OBJ(isXorTree(), m_rootp, "must be either Xor or RedXor");
            return new AstXor(m_rootp->fileline(), lhsp, rhsp);
        }
    }

    // VISITORS
    virtual void visit(AstNode* nodep) override {
        CONST_BITOP_SET_FAILED("Hit unexpected op", nodep);
    }
    virtual void visit(AstCCast* nodep) override { iterateChildren(nodep); }
    virtual void visit(AstShiftR* nodep) override {
        CONST_BITOP_RETURN_IF(!m_leafp, nodep);
        AstConst* constp = VN_CAST(nodep->rhsp(), Const);
        CONST_BITOP_RETURN_IF(!constp, nodep->rhsp());
        m_lsb += constp->toUInt();
        incrOps(nodep, __LINE__);
        iterate(nodep->lhsp());
        m_lsb -= constp->toUInt();
    }
    virtual void visit(AstNot* nodep) override {
        CONST_BITOP_RETURN_IF(nodep->widthMin() != 1, nodep);
        AstNode* lhsp = nodep->lhsp();
        CONST_BITOP_RETURN_IF(VN_IS(lhsp, And) || VN_IS(lhsp, Or) || VN_IS(lhsp, Const), lhsp);
        incrOps(nodep, __LINE__);
        m_polarity = !m_polarity;
        iterateChildren(nodep);
        // Don't restore m_polarity for Xor as it counts parity of the entire tree
        if (!isXorTree()) m_polarity = !m_polarity;
    }
    virtual void visit(AstWordSel* nodep) override {
        CONST_BITOP_RETURN_IF(!m_leafp, nodep);
        AstConst* constp = VN_CAST(nodep->bitp(), Const);
        CONST_BITOP_RETURN_IF(!constp, nodep->rhsp());
        UASSERT_OBJ(m_leafp->m_wordIdx == -1, nodep, "Unexpected nested WordSel");
        m_leafp->m_wordIdx = constp->toSInt();
        iterate(nodep->fromp());
    }
    virtual void visit(AstVarRef* nodep) override {
        CONST_BITOP_RETURN_IF(!m_leafp, nodep);
        UASSERT_OBJ(!m_leafp->m_refp, nodep, m_leafp->m_refp << " is already set");
        m_leafp->m_refp = nodep;
        m_leafp->m_polarity = m_polarity;
        m_leafp->m_lsb = m_lsb;
    }
    virtual void visit(AstConst* nodep) override {
        CONST_BITOP_RETURN_IF(!m_leafp, nodep);
        UASSERT_OBJ(!m_leafp->m_constp, nodep, m_leafp->m_constp << " is already set");
        m_leafp->m_constp = nodep;
        m_leafp->m_lsb = m_lsb;
    }

    virtual void visit(AstRedXor* nodep) override {  // Expect '^(mask & v)'
        CONST_BITOP_RETURN_IF(!VN_IS(m_rootp, Xor), nodep);
        AstAnd* andp = VN_CAST(nodep->lhsp(), And);
        CONST_BITOP_RETURN_IF(!andp, nodep->lhsp());

        auto mask = findLeaf(andp->lhsp(), true);
        CONST_BITOP_RETURN_IF(!mask.m_constp || mask.m_lsb != 0, andp->lhsp());

        LeafInfo leaf = findLeaf(andp->rhsp(), false);
        CONST_BITOP_RETURN_IF(!leaf.m_refp, andp->rhsp());

        incrOps(nodep, __LINE__);
        incrOps(andp, __LINE__);
        const V3Number& maskNum = mask.m_constp->num();
        VarInfo& varInfo = getVarInfo(leaf);
        for (int i = 0; i < maskNum.width(); ++i) {
            // Set true, m_treePolarity takes care of the entire parity
            if (maskNum.bitIs1(i)) varInfo.setPolarity(true, i + leaf.m_lsb);
        }
    }

    virtual void visit(AstNodeBiop* nodep) override {
        auto isConst = [](AstNode* nodep, vluint64_t v) -> bool {
            AstConst* constp = VN_CAST(nodep, Const);
            return constp && constp->toUQuad() == v;
        };
        if (nodep->type() == m_rootp->type()) {  // And, Or, Xor
            CONST_BITOP_RETURN_IF(!m_polarity && isXorTree(), nodep);
            incrOps(nodep, __LINE__);
            VL_RESTORER(m_curOpp);
            VL_RESTORER(m_leafp);

            for (int i = 0; i < 2; ++i) {
                LeafInfo leafInfo;
                m_leafp = &leafInfo;
                m_curOpp = i == 0 ? nodep->lhsp() : nodep->rhsp();
                const size_t origFrozens = m_frozenNodes.size();
                const int origOps = m_ops;
                const bool origFailed = m_failed;
                iterate(m_curOpp);
                if (leafInfo.m_constp || m_failed) {
                    // Rvert changes in leaf
                    if (m_frozenNodes.size() > origFrozens) m_frozenNodes.resize(origFrozens);
                    m_frozenNodes.push_back(m_curOpp);
                    m_ops = origOps;
                    m_failed = origFailed;
                } else if (leafInfo.m_refp) {
                    VarInfo& varInfo = getVarInfo(leafInfo);
                    if (!varInfo.hasConstantResult()) {
                        varInfo.setPolarity(isXorTree() || leafInfo.m_polarity, leafInfo.m_lsb);
                    }
                }
            }
            return;
        } else if (VN_IS(m_rootp, Xor) && VN_IS(nodep, Eq) && isConst(nodep->lhsp(), 0)
                   && VN_IS(nodep->rhsp(), And)) {  // 0 == (1 & RedXor)
            AstAnd* andp = static_cast<AstAnd*>(nodep->rhsp());  // already checked above
            CONST_BITOP_RETURN_IF(!isConst(andp->lhsp(), 1), andp->lhsp());
            AstRedXor* redXorp = VN_CAST(andp->rhsp(), RedXor);
            CONST_BITOP_RETURN_IF(!redXorp, andp->rhsp());
            incrOps(nodep, __LINE__);
            incrOps(andp, __LINE__);
            m_polarity = !m_polarity;
            iterate(redXorp);
            return;
        } else if (VN_IS(m_rootp, Xor) && VN_IS(nodep, And) && isConst(nodep->lhsp(), 1)
                   && (VN_IS(nodep->rhsp(), Xor)
                       || VN_IS(nodep->rhsp(), RedXor))) {  // 1 & (v[3] ^ v[2])
            incrOps(nodep, __LINE__);
            iterate(nodep->rhsp());
            return;
        } else if ((isAndTree() && VN_IS(nodep, Eq)) || (isOrTree() && VN_IS(nodep, Neq))) {
            CONST_BITOP_RETURN_IF(!m_polarity, nodep);
            const bool maskFlip = isOrTree();
            LeafInfo comp = findLeaf(nodep->lhsp(), true);
            CONST_BITOP_RETURN_IF(!comp.m_constp || comp.m_lsb != 0, nodep->lhsp());

            AstAnd* andp = VN_CAST(nodep->rhsp(), And);  // comp == (mask & v)
            CONST_BITOP_RETURN_IF(!andp, nodep->rhsp());

            LeafInfo mask = findLeaf(andp->lhsp(), true);
            CONST_BITOP_RETURN_IF(!mask.m_constp || mask.m_lsb != 0, andp->lhsp());

            LeafInfo ref = findLeaf(andp->rhsp(), false);
            CONST_BITOP_RETURN_IF(!ref.m_refp, andp->rhsp());

            VarInfo& varInfo = getVarInfo(ref);

            const V3Number maskNum = mask.m_constp->num();
            const V3Number compNum = comp.m_constp->num();
            for (int i = 0; i < maskNum.width() && !varInfo.hasConstantResult(); ++i) {
                const int bit = i + ref.m_lsb;
                if (maskNum.bitIs0(i)) continue;
                varInfo.setPolarity(compNum.bitIs1(i) ^ maskFlip, bit);
            }
            incrOps(nodep, __LINE__);
            incrOps(andp, __LINE__);
            return;
        }
        CONST_BITOP_SET_FAILED("Mixture of different ops cannot be optimized", nodep);
    }

    // CONSTRUCTORS
    ConstBitOpTreeVisitor(AstNode* nodep, int ops)
        : m_ops(ops)
        , m_rootp(nodep) {
        // Fill nullptr at [0] because AstVarScope::user4 is 0 by default
        m_varInfos.push_back(nullptr);
        CONST_BITOP_RETURN_IF(!isAndTree() && !isOrTree() && !isXorTree(), nodep);
        AstNode::user4ClearTree();
        if (AstNodeBiop* biopp = VN_CAST(nodep, NodeBiop)) {
            iterate(biopp);
        } else {
            incrOps(nodep, __LINE__);
            iterateChildren(nodep);
        }
        UASSERT_OBJ(isXorTree() || m_polarity, nodep, "must be the original polarity");
    }
    virtual ~ConstBitOpTreeVisitor() {
        for (size_t i = 0; i < m_varInfos.size(); ++i) {
            VL_DO_DANGLING(delete m_varInfos[i], m_varInfos[i]);
        }
    }
#undef CONST_BITOP_RETURN_IF
#undef CONST_BITOP_SET_FAILED

public:
    // Transform as below.
    // v[0] & v[1] => 2'b11 == (2'b11 & v)
    // v[0] | v[1] => 2'b00 != (2'b11 & v)
    // v[0] ^ v[1] => ^{2'b11 & v}
    // (3'b011 == (3'b011 & v)) & v[2]  => 3'b111 == (3'b111 & v)
    // (3'b000 != (3'b011 & v)) | v[2]  => 3'b000 != (3'b111 & v)
    // Reduction ops are transformed in the same way.
    // &{v[0], v[1]} => 2'b11 == (2'b11 & v)
    static AstNode* simplify(AstNode* nodep, int ops, VDouble0& reduction) {
        ConstBitOpTreeVisitor visitor{nodep, ops};
        if (visitor.m_failed || visitor.m_varInfos.size() == 1) return nullptr;

        // Two ops for each varInfo. (And and Eq)
        const int vars = visitor.m_varInfos.size() - 1;
        int constTerms = 0;
        for (const VarInfo* v : visitor.m_varInfos) {
            if (v && v->hasConstantResult()) ++constTerms;
        }
        // Expected number of ops after this simplification
        // e.g. (comp0 == (mask0 & var0)) & (comp1 == (mask1 & var1)) & ....
        // e.g. redXor(mask1 & var0) ^ redXor(mask1 & var1)
        //  2 ops per variables, numVars - 1 ops among variables
        int expOps = 2 * (vars - constTerms) + vars - 1;
        expOps += 2 * visitor.m_frozenNodes.size();
        if (visitor.isXorTree()) {
            ++expOps;  // AstRedXor::cleanOut() == false, so need 1 & redXor
            if (!visitor.m_polarity) ++expOps;  // comparison with 0
        }
        if (visitor.m_ops <= expOps) return nullptr;  // Unless benefitial, return

        reduction += visitor.m_ops - expOps;

        AstNode* resultp = nullptr;
        // VarInfo in visitor.m_varInfos appears in deterministic order,
        // so the optimized AST is deterministic too.
        for (const VarInfo* varinfop : visitor.m_varInfos) {
            if (!varinfop) continue;
            AstNode* partialresultp = varinfop->getResult();
            resultp = visitor.combineTree(resultp, partialresultp);
        }
        AstNode* frozensp = nullptr;
        for (AstNode* frozenp : visitor.m_frozenNodes) {
            frozenp->unlinkFrBack();
            frozensp = visitor.combineTree(frozensp, frozenp);
        }
        if (frozensp) resultp = visitor.combineTree(resultp, frozensp);

        if (visitor.isXorTree()) {
            // VL_REDXOR_N functions don't guarantee to return only 0/1
            const int width = resultp->width();
            FileLine* fl = nodep->fileline();
            resultp = new AstAnd{fl, new AstConst{fl, V3Number{nodep, width, 1}}, resultp};
            if (!visitor.m_polarity) {
                resultp = new AstEq{fl, new AstConst{fl, V3Number{nodep, width, 0}}, resultp};
                resultp->dtypep()->widthForce(1, 1);
            }
        }
        if (resultp->width() != nodep->width()) {
            resultp = new AstCCast{resultp->fileline(), resultp, nodep};
        }
        return resultp;
    }
};

//######################################################################
// Const state, as a visitor of each AstNode

class ConstVisitor final : public AstNVisitor {
private:
    // NODE STATE
    // ** only when m_warn/m_doExpensive is set.  If state is needed other times,
    // ** must track down everywhere V3Const is called and make sure no overlaps.
    // AstVar::user4p           -> Used by ConstVarMarkVisitor/ConstVarFindVisitor
    // AstJumpLabel::user4      -> bool.  Set when AstJumpGo uses this label
    // AstEnum::user4           -> bool.  Recursing.

    // STATE
    bool m_params = false;  // If true, propagate parameterized and true numbers only
    bool m_required = false;  // If true, must become a constant
    bool m_wremove = true;  // Inside scope, no assignw removal
    bool m_warn = false;  // Output warnings
    bool m_doExpensive = false;  // Enable computationally expensive optimizations
    bool m_doCpp = false;  // Enable late-stage C++ optimizations
    bool m_doNConst = false;  // Enable non-constant-child simplifications
    bool m_doShort = true;  // Remove expressions that short circuit
    bool m_doV = false;  // Verilog, not C++ conversion
    bool m_doGenerate = false;  // Postpone width checking inside generate
    bool m_hasJumpDelay = false;  // JumpGo or Delay under this while
    AstNodeModule* m_modp = nullptr;  // Current module
    AstArraySel* m_selp = nullptr;  // Current select
    AstNode* m_scopep = nullptr;  // Current scope
    AstAttrOf* m_attrp = nullptr;  // Current attribute
    VDouble0 m_statBitOpReduction;  // Ops reduced in ConstBitOpTreeVisitor

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    bool operandConst(AstNode* nodep) { return VN_IS(nodep, Const); }
    bool operandAsvConst(const AstNode* nodep) {
        // BIASV(CONST, BIASV(CONST,...)) -> BIASV( BIASV_CONSTED(a,b), ...)
        const AstNodeBiComAsv* bnodep = VN_CAST_CONST(nodep, NodeBiComAsv);
        if (!bnodep) return false;
        if (!VN_IS(bnodep->lhsp(), Const)) return false;
        const AstNodeBiComAsv* rnodep = VN_CAST_CONST(bnodep->rhsp(), NodeBiComAsv);
        if (!rnodep) return false;
        if (rnodep->type() != bnodep->type()) return false;
        if (rnodep->width() != bnodep->width()) return false;
        if (rnodep->lhsp()->width() != bnodep->lhsp()->width()) return false;
        if (!VN_IS(rnodep->lhsp(), Const)) return false;
        return true;
    }
    bool operandAsvSame(const AstNode* nodep) {
        // BIASV(SAMEa, BIASV(SAMEb,...)) -> BIASV( BIASV(SAMEa,SAMEb), ...)
        const AstNodeBiComAsv* bnodep = VN_CAST_CONST(nodep, NodeBiComAsv);
        if (!bnodep) return false;
        const AstNodeBiComAsv* rnodep = VN_CAST_CONST(bnodep->rhsp(), NodeBiComAsv);
        if (!rnodep) return false;
        if (rnodep->type() != bnodep->type()) return false;
        if (rnodep->width() != bnodep->width()) return false;
        return operandsSame(bnodep->lhsp(), rnodep->lhsp());
    }
    bool operandAsvLUp(const AstNode* nodep) {
        // BIASV(BIASV(CONSTll,lr),r) -> BIASV(CONSTll,BIASV(lr,r)) ?
        //
        // Example of how this is useful:
        // BIASV(BIASV(CONSTa,b...),BIASV(CONSTc,d...))  // hits operandAsvUp
        // BIASV(CONSTa,BIASV(b...,BIASV(CONSTc,d...)))  // hits operandAsvUp
        // BIASV(CONSTa,BIASV(CONSTc,BIASV(c...,d...)))  // hits operandAsvConst
        // BIASV(BIASV(CONSTa,CONSTc),BIASV(c...,d...))) // hits normal constant propagation
        // BIASV(CONST_a_c,BIASV(c...,d...)))
        //
        // Idea for the future: All BiComAsvs could be lists, sorted by if they're constant
        const AstNodeBiComAsv* bnodep = VN_CAST_CONST(nodep, NodeBiComAsv);
        if (!bnodep) return false;
        const AstNodeBiComAsv* lnodep = VN_CAST_CONST(bnodep->lhsp(), NodeBiComAsv);
        if (!lnodep) return false;
        if (lnodep->type() != bnodep->type()) return false;
        if (lnodep->width() != bnodep->width()) return false;
        return VN_IS(lnodep->lhsp(), Const);
    }
    bool operandAsvRUp(const AstNode* nodep) {
        // BIASV(l,BIASV(CONSTrl,rr)) -> BIASV(CONSTrl,BIASV(l,rr)) ?
        const AstNodeBiComAsv* bnodep = VN_CAST_CONST(nodep, NodeBiComAsv);
        if (!bnodep) return false;
        const AstNodeBiComAsv* rnodep = VN_CAST_CONST(bnodep->rhsp(), NodeBiComAsv);
        if (!rnodep) return false;
        if (rnodep->type() != bnodep->type()) return false;
        if (rnodep->width() != bnodep->width()) return false;
        return VN_IS(rnodep->lhsp(), Const);
    }
    static bool operandSubAdd(const AstNode* nodep) {
        // SUB( ADD(CONSTx,y), CONSTz) -> ADD(SUB(CONSTx,CONSTz), y)
        const AstNodeBiop* np = VN_CAST_CONST(nodep, NodeBiop);
        const AstNodeBiop* lp = VN_CAST_CONST(np->lhsp(), NodeBiop);
        return (lp && VN_IS(lp->lhsp(), Const) && VN_IS(np->rhsp(), Const)
                && lp->width() == np->width());
    }
    bool matchRedundantClean(AstAnd* andp) {
        // Remove And with constant one inserted by V3Clean
        // 1 & (a == b)  -> (IData)(a == b)
        // When bool is casted to int, the value is either 0 or 1
        AstConst* constp = VN_CAST(andp->lhsp(), Const);
        UASSERT_OBJ(constp && constp->isOne(), andp->lhsp(), "TRREEOPC must meet this condition");
        AstNode* rhsp = andp->rhsp();
        AstCCast* ccastp = nullptr;
        auto isEqOrNeq
            = [](AstNode* nodep) -> bool { return VN_IS(nodep, Eq) || VN_IS(nodep, Neq); };
        if (isEqOrNeq(rhsp)) {
            ccastp = new AstCCast{andp->fileline(), rhsp->unlinkFrBack(), andp};
        } else if (AstCCast* tmpp = VN_CAST(rhsp, CCast)) {
            if (isEqOrNeq(tmpp->lhsp())) {
                if (tmpp->width() == andp->width()) {
                    tmpp->unlinkFrBack();
                    ccastp = tmpp;
                } else {
                    ccastp = new AstCCast{andp->fileline(), tmpp->lhsp()->unlinkFrBack(), andp};
                }
            }
        }
        if (ccastp) {
            andp->replaceWith(ccastp);
            VL_DO_DANGLING(andp->deleteTree(), andp);
        }
        return ccastp;
    }

    static bool operandAndOrSame(const AstNode* nodep) {
        // OR( AND(VAL,x), AND(VAL,y)) -> AND(VAL,OR(x,y))
        // OR( AND(x,VAL), AND(y,VAL)) -> AND(OR(x,y),VAL)
        const AstNodeBiop* np = VN_CAST_CONST(nodep, NodeBiop);
        const AstNodeBiop* lp = VN_CAST_CONST(np->lhsp(), NodeBiop);
        const AstNodeBiop* rp = VN_CAST_CONST(np->rhsp(), NodeBiop);
        return (lp && rp && lp->width() == rp->width() && lp->type() == rp->type()
                && (operandsSame(lp->lhsp(), rp->lhsp()) || operandsSame(lp->rhsp(), rp->rhsp())));
    }
    static bool matchOrAndNot(AstNodeBiop* nodep) {
        // AstOr{$a, AstAnd{AstNot{$b}, $c}} if $a.width1, $a==$b => AstOr{$a,$c}
        // Someday we'll sort the biops completely and this can be simplified
        // This often results from our simplified clock generation:
        // if (rst) ... else if (enable)... -> OR(rst,AND(!rst,enable))
        AstNode* ap;
        AstNodeBiop* andp;
        if (VN_IS(nodep->lhsp(), And)) {
            andp = VN_CAST(nodep->lhsp(), And);
            ap = nodep->rhsp();
        } else if (VN_IS(nodep->rhsp(), And)) {
            andp = VN_CAST(nodep->rhsp(), And);
            ap = nodep->lhsp();
        } else
            return false;
        AstNodeUniop* notp;
        AstNode* cp;
        if (VN_IS(andp->lhsp(), Not)) {
            notp = VN_CAST(andp->lhsp(), Not);
            cp = andp->rhsp();
        } else if (VN_IS(andp->rhsp(), Not)) {
            notp = VN_CAST(andp->rhsp(), Not);
            cp = andp->lhsp();
        } else
            return false;
        AstNode* bp = notp->lhsp();
        if (!operandsSame(ap, bp)) return false;
        // Do it
        cp->unlinkFrBack();
        VL_DO_DANGLING(andp->unlinkFrBack()->deleteTree(), andp);
        VL_DANGLING(notp);
        // Replace whichever branch is now dangling
        if (nodep->rhsp()) {
            nodep->lhsp(cp);
        } else {
            nodep->rhsp(cp);
        }
        return true;
    }
    bool matchAndCond(AstAnd* nodep) {
        // Push down a AND into conditional, when one side of conditional is constant
        // (otherwise we'd be trading one operation for two operations)
        // V3Clean often makes this pattern, as it postpones the AND until
        // as high as possible, which is usally the right choice, except for this.
        AstNodeCond* condp = VN_CAST(nodep->rhsp(), NodeCond);
        if (!condp) return false;
        if (!VN_IS(condp->expr1p(), Const) && !VN_IS(condp->expr2p(), Const)) return false;
        AstConst* maskp = VN_CAST(nodep->lhsp(), Const);
        if (!maskp) return false;
        UINFO(4, "AND(CONSTm, CONDcond(c, i, e))->CONDcond(c, AND(m,i), AND(m, e)) " << nodep
                                                                                     << endl);
        AstNodeCond* newp = static_cast<AstNodeCond*>(
            condp->cloneType(condp->condp()->unlinkFrBack(),
                             new AstAnd(nodep->fileline(), maskp->cloneTree(false),
                                        condp->expr1p()->unlinkFrBack()),
                             new AstAnd(nodep->fileline(), maskp->cloneTree(false),
                                        condp->expr2p()->unlinkFrBack())));
        newp->dtypeFrom(nodep);
        newp->expr1p()->dtypeFrom(nodep);  // As And might have been to change widths
        newp->expr2p()->dtypeFrom(nodep);
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
        return true;
    }
    bool matchBitOpTree(AstNode* nodep) {
        if (!v3Global.opt.oConstBitOpTree()) return false;

        AstNode* newp = nullptr;
        bool tried = false;
        if (AstAnd* andp = VN_CAST(nodep, And)) {  // 1 & BitOpTree
            if (AstConst* bitMaskp = VN_CAST(andp->lhsp(), Const)) {
                if (bitMaskp->num().toUQuad() != 1) return false;
                newp = ConstBitOpTreeVisitor::simplify(andp->rhsp(), 1, m_statBitOpReduction);
                tried = true;
            }
        }
        if (!tried) {
            // (comp == BitOpTree) & BitOpTree
            // (comp != BitOpTree) | BitOpTree
            newp = ConstBitOpTreeVisitor::simplify(nodep, 0, m_statBitOpReduction);
        }
        if (newp) {
            UINFO(4, "Transformed leaf of bit tree to " << newp << std::endl);
            if (debug() >= 9) {  // LCOV_EXCL_START
                static int c = 0;
                std::cout << "Call matchBitOpTree[" << c << "]\n";
                nodep->dumpTree(std::cout);
                std::cout << "\nResult:\n";
                newp->dumpTree(std::cout);
                ++c;
            }  // LCOV_EXCL_STOP
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
        return newp;
    }
    static bool operandShiftSame(const AstNode* nodep) {
        const AstNodeBiop* np = VN_CAST_CONST(nodep, NodeBiop);
        {
            const AstShiftL* lp = VN_CAST_CONST(np->lhsp(), ShiftL);
            const AstShiftL* rp = VN_CAST_CONST(np->rhsp(), ShiftL);
            if (lp && rp) {
                return (lp->width() == rp->width() && lp->lhsp()->width() == rp->lhsp()->width()
                        && operandsSame(lp->rhsp(), rp->rhsp()));
            }
        }
        {
            const AstShiftR* lp = VN_CAST_CONST(np->lhsp(), ShiftR);
            const AstShiftR* rp = VN_CAST_CONST(np->rhsp(), ShiftR);
            if (lp && rp) {
                return (lp->width() == rp->width() && lp->lhsp()->width() == rp->lhsp()->width()
                        && operandsSame(lp->rhsp(), rp->rhsp()));
            }
        }
        return false;
    }
    bool operandHugeShiftL(const AstNodeBiop* nodep) {
        return (VN_IS(nodep->rhsp(), Const)
                && !VN_CAST_CONST(nodep->rhsp(), Const)->num().isFourState()
                && (VN_CAST_CONST(nodep->rhsp(), Const)->toUInt()
                    >= static_cast<uint32_t>(nodep->width()))
                && isTPure(nodep->lhsp()));
    }
    bool operandHugeShiftR(const AstNodeBiop* nodep) {
        return (VN_IS(nodep->rhsp(), Const)
                && !VN_CAST_CONST(nodep->rhsp(), Const)->num().isFourState()
                && (VN_CAST_CONST(nodep->rhsp(), Const)->toUInt()
                    >= static_cast<uint32_t>(nodep->lhsp()->width()))
                && isTPure(nodep->lhsp()));
    }
    bool operandIsTwo(const AstNode* nodep) {
        return (VN_IS(nodep, Const) && !VN_CAST_CONST(nodep, Const)->num().isFourState()
                && nodep->width() <= VL_QUADSIZE && VN_CAST_CONST(nodep, Const)->toUQuad() == 2);
    }
    bool operandIsTwostate(const AstNode* nodep) {
        return (VN_IS(nodep, Const) && !VN_CAST_CONST(nodep, Const)->num().isFourState());
    }
    bool operandIsPowTwo(const AstNode* nodep) {
        if (!operandIsTwostate(nodep)) return false;
        return (1 == VN_CAST_CONST(nodep, Const)->num().countOnes());
    }
    bool operandShiftOp(const AstNodeBiop* nodep) {
        if (!VN_IS(nodep->rhsp(), Const)) return false;
        const AstNodeBiop* lhsp = VN_CAST(nodep->lhsp(), NodeBiop);
        if (!lhsp || !(VN_IS(lhsp, And) || VN_IS(lhsp, Or) || VN_IS(lhsp, Xor))) return false;
        if (nodep->width() != lhsp->width()) return false;
        if (nodep->width() != lhsp->lhsp()->width()) return false;
        if (nodep->width() != lhsp->rhsp()->width()) return false;
        return true;
    }
    bool operandShiftShift(const AstNodeBiop* nodep) {
        // We could add a AND though.
        const AstNodeBiop* lhsp = VN_CAST(nodep->lhsp(), NodeBiop);
        if (!lhsp || !(VN_IS(lhsp, ShiftL) || VN_IS(lhsp, ShiftR))) return false;
        // We can only get rid of a<<b>>c or a<<b<<c, with constant b & c
        // because bits may be masked in that process, or (b+c) may exceed the word width.
        if (!(VN_IS(nodep->rhsp(), Const) && VN_IS(lhsp->rhsp(), Const))) return false;
        if (VN_CAST_CONST(nodep->rhsp(), Const)->num().isFourState()
            || VN_CAST_CONST(lhsp->rhsp(), Const)->num().isFourState())
            return false;
        if (nodep->width() != lhsp->width()) return false;
        if (nodep->width() != lhsp->lhsp()->width()) return false;
        return true;
    }
    bool operandWordOOB(const AstWordSel* nodep) {
        // V3Expand may make a arraysel that exceeds the bounds of the array
        // It was an expression, then got constified.  In reality, the WordSel
        // must be wrapped in a Cond, that will be false.
        return (VN_IS(nodep->rhsp(), Const) && VN_IS(nodep->fromp(), NodeVarRef)
                && VN_CAST_CONST(nodep->fromp(), NodeVarRef)->access().isReadOnly()
                && (static_cast<int>(VN_CAST_CONST(nodep->rhsp(), Const)->toUInt())
                    >= VN_CAST(nodep->fromp(), NodeVarRef)->varp()->widthWords()));
    }
    bool operandSelFull(const AstSel* nodep) {
        return (VN_IS(nodep->lsbp(), Const) && VN_IS(nodep->widthp(), Const)
                && nodep->lsbConst() == 0
                && static_cast<int>(nodep->widthConst()) == nodep->fromp()->width());
    }
    bool operandSelExtend(AstSel* nodep) {
        // A pattern created by []'s after offsets have been removed
        // SEL(EXTEND(any,width,...),(width-1),0) -> ...
        // Since select's return unsigned, this is always an extend
        AstExtend* extendp = VN_CAST(nodep->fromp(), Extend);
        if (!(m_doV && extendp && VN_IS(nodep->lsbp(), Const) && VN_IS(nodep->widthp(), Const)
              && nodep->lsbConst() == 0
              && static_cast<int>(nodep->widthConst()) == extendp->lhsp()->width()))
            return false;
        VL_DO_DANGLING(replaceWChild(nodep, extendp->lhsp()), nodep);
        return true;
    }
    bool operandSelBiLower(AstSel* nodep) {
        // SEL(ADD(a,b),(width-1),0) -> ADD(SEL(a),SEL(b))
        // Add or any operation which doesn't care if we discard top bits
        AstNodeBiop* bip = VN_CAST(nodep->fromp(), NodeBiop);
        if (!(m_doV && bip && VN_IS(nodep->lsbp(), Const) && VN_IS(nodep->widthp(), Const)
              && nodep->lsbConst() == 0))
            return false;
        if (debug() >= 9) nodep->dumpTree(cout, "SEL(BI)-in:");
        AstNode* bilhsp = bip->lhsp()->unlinkFrBack();
        AstNode* birhsp = bip->rhsp()->unlinkFrBack();
        bip->lhsp(new AstSel(nodep->fileline(), bilhsp, 0, nodep->widthConst()));
        bip->rhsp(new AstSel(nodep->fileline(), birhsp, 0, nodep->widthConst()));
        if (debug() >= 9) bip->dumpTree(cout, "SEL(BI)-ou:");
        VL_DO_DANGLING(replaceWChild(nodep, bip), nodep);
        return true;
    }
    bool operandSelShiftLower(AstSel* nodep) {
        // AND({a}, SHIFTR({b}, {c})) is often shorthand in C for Verilog {b}[{c} :+ {a}]
        // becomes thought other optimizations
        // SEL(SHIFTR({a},{b}),{lsb},{width}) -> SEL({a},{lsb+b},{width})
        AstShiftR* shiftp = VN_CAST(nodep->fromp(), ShiftR);
        if (!(m_doV && shiftp && VN_IS(shiftp->rhsp(), Const) && VN_IS(nodep->lsbp(), Const)
              && VN_IS(nodep->widthp(), Const))) {
            return false;
        }
        AstNode* ap = shiftp->lhsp();
        AstConst* bp = VN_CAST(shiftp->rhsp(), Const);
        AstConst* lp = VN_CAST(nodep->lsbp(), Const);
        if (bp->isWide() || bp->num().isFourState() || bp->num().isNegative() || lp->isWide()
            || lp->num().isFourState() || lp->num().isNegative()) {
            return false;
        }
        int newLsb = lp->toSInt() + bp->toSInt();
        if (newLsb + nodep->widthConst() > ap->width()) return false;
        //
        UINFO(9, "SEL(SHIFTR(a,b),l,w) -> SEL(a,l+b,w)\n");
        if (debug() >= 9) nodep->dumpTree(cout, "SEL(SH)-in:");
        AstSel* newp
            = new AstSel(nodep->fileline(), ap->unlinkFrBack(), newLsb, nodep->widthConst());
        newp->dtypeFrom(nodep);
        if (debug() >= 9) newp->dumpTree(cout, "SEL(SH)-ou:");
        VL_DO_DANGLING(nodep->replaceWith(newp), nodep);
        return true;
    }

    bool operandBiExtendConstShrink(AstNodeBiop* nodep) {
        // Loop unrolling favors standalone compares
        // EQ(const{width32}, EXTEND(xx{width3})) -> EQ(const{3}, xx{3})
        // The constant must have zero bits (+ 1 if signed) or compare
        // would be incorrect. See also operandBiExtendConst
        AstExtend* extendp = VN_CAST(nodep->rhsp(), Extend);
        if (!extendp) return false;
        AstNode* smallerp = extendp->lhsp();
        int subsize = smallerp->width();
        AstConst* constp = VN_CAST(nodep->lhsp(), Const);
        if (!constp) return false;
        if (!constp->num().isBitsZero(constp->width() - 1, subsize)) return false;
        //
        if (debug() >= 9) nodep->dumpTree(cout, "BI(EXTEND)-in:");
        smallerp->unlinkFrBack();
        VL_DO_DANGLING(extendp->unlinkFrBack()->deleteTree(), extendp);  // aka nodep->lhsp.
        nodep->rhsp(smallerp);

        constp->unlinkFrBack();
        V3Number num(constp, subsize);
        num.opAssign(constp->num());
        nodep->lhsp(new AstConst(constp->fileline(), num));
        VL_DO_DANGLING(constp->deleteTree(), constp);
        if (debug() >= 9) nodep->dumpTree(cout, "BI(EXTEND)-ou:");
        return true;
    }
    bool operandBiExtendConstOver(const AstNodeBiop* nodep) {
        // EQ(const{width32}, EXTEND(xx{width3})) -> constant
        // When the constant has non-zero bits above the extend it's a constant.
        // Avoids compiler warning
        const AstExtend* extendp = VN_CAST_CONST(nodep->rhsp(), Extend);
        if (!extendp) return false;
        AstNode* smallerp = extendp->lhsp();
        int subsize = smallerp->width();
        const AstConst* constp = VN_CAST_CONST(nodep->lhsp(), Const);
        if (!constp) return false;
        if (constp->num().isBitsZero(constp->width() - 1, subsize)) return false;
        return true;
    }

    AstNode* afterComment(AstNode* nodep) {
        // Ignore comments, such as to determine if a AstIf is empty.
        // nodep may be null, if so return null.
        while (nodep && VN_IS(nodep, Comment)) { nodep = nodep->nextp(); }
        return nodep;
    }

    bool isTPure(AstNode* nodep) {
        // Pure checks - if this node and all nodes under it are free of
        // side effects can do this optimization
        // Eventually we'll recurse through tree when unknown, memoizing results so far,
        // but for now can disable en-mass until V3Purify takes effect.
        return m_doShort || VN_IS(nodep, VarRef) || VN_IS(nodep, Const);
    }

    // Extraction checks
    bool warnSelect(AstSel* nodep) {
        if (m_doGenerate) {
            // Never checked yet
            V3Width::widthParamsEdit(nodep);
            iterateChildren(nodep);  // May need "constifying"
        }
        // Find range of dtype we are selecting from
        // Similar code in V3Unknown::AstSel
        bool doit = true;
        if (m_warn && VN_IS(nodep->lsbp(), Const) && VN_IS(nodep->widthp(), Const) && doit) {
            int maxDeclBit = nodep->declRange().hiMaxSelect() * nodep->declElWidth()
                             + (nodep->declElWidth() - 1);
            if (VN_CAST(nodep->lsbp(), Const)->num().isFourState()
                || VN_CAST(nodep->widthp(), Const)->num().isFourState()) {
                nodep->v3error("Selection index is constantly unknown or tristated: "
                               "lsb="
                               << nodep->lsbp()->name() << " width=" << nodep->widthp()->name());
                // Replacing nodep will make a mess above, so we replace the offender
                replaceZero(nodep->lsbp());
            } else if (nodep->declRange().ranged()
                       && (nodep->msbConst() > maxDeclBit || nodep->lsbConst() > maxDeclBit)) {
                // See also warning in V3Width
                // Must adjust by element width as declRange() is in number of elements
                nodep->v3warn(SELRANGE,
                              "Selection index out of range: "
                                  << (nodep->msbConst() / nodep->declElWidth()) << ":"
                                  << (nodep->lsbConst() / nodep->declElWidth()) << " outside "
                                  << nodep->declRange().hiMaxSelect() << ":0"
                                  << (nodep->declRange().lo() >= 0
                                          ? ""
                                          : (" (adjusted +" + cvtToStr(-nodep->declRange().lo())
                                             + " to account for negative lsb)")));
                UINFO(1, "    Related Raw index is " << nodep->msbConst() << ":"
                                                     << nodep->lsbConst() << endl);
                // Don't replace with zero, we'll do it later
            }
        }
        return false;  // Not a transform, so NOP
    }

    static bool operandsSame(AstNode* node1p, AstNode* node2p) {
        // For now we just detect constants & simple vars, though it could be more generic
        if (VN_IS(node1p, Const) && VN_IS(node2p, Const)) {
            return node1p->sameGateTree(node2p);
        } else if (VN_IS(node1p, VarRef) && VN_IS(node2p, VarRef)) {
            // Avoid comparing widthMin's, which results in lost optimization attempts
            // If cleanup sameGateTree to be smarter, this can be restored.
            // return node1p->sameGateTree(node2p);
            return node1p->same(node2p);
        } else {
            return false;
        }
    }
    bool ifSameAssign(const AstNodeIf* nodep) {
        const AstNodeAssign* ifp = VN_CAST_CONST(nodep->ifsp(), NodeAssign);
        const AstNodeAssign* elsep = VN_CAST_CONST(nodep->elsesp(), NodeAssign);
        if (!ifp || ifp->nextp()) return false;  // Must be SINGLE statement
        if (!elsep || elsep->nextp()) return false;
        if (ifp->type() != elsep->type()) return false;  // Can't mix an assigndly and an assign
        if (!ifp->lhsp()->sameGateTree(elsep->lhsp())) return false;
        if (!ifp->rhsp()->gateTree()) return false;
        if (!elsep->rhsp()->gateTree()) return false;
        return true;
    }
    bool operandIfIf(const AstNodeIf* nodep) {
        if (nodep->elsesp()) return false;
        const AstNodeIf* lowerIfp = VN_CAST_CONST(nodep->ifsp(), NodeIf);
        if (!lowerIfp || lowerIfp->nextp()) return false;
        if (nodep->type() != lowerIfp->type()) return false;
        if (afterComment(lowerIfp->elsesp())) return false;
        return true;
    }
    bool ifConcatMergeableBiop(const AstNode* nodep) {
        return (VN_IS(nodep, And) || VN_IS(nodep, Or) || VN_IS(nodep, Xor));
    }
    bool ifAdjacentSel(const AstSel* lhsp, const AstSel* rhsp) {
        if (!v3Global.opt.oAssemble()) return false;  // opt disabled
        if (!lhsp || !rhsp) return false;
        const AstNode* lfromp = lhsp->fromp();
        const AstNode* rfromp = rhsp->fromp();
        if (!lfromp || !rfromp || !lfromp->sameGateTree(rfromp)) return false;
        const AstConst* lstart = VN_CAST_CONST(lhsp->lsbp(), Const);
        const AstConst* rstart = VN_CAST_CONST(rhsp->lsbp(), Const);
        const AstConst* lwidth = VN_CAST_CONST(lhsp->widthp(), Const);
        const AstConst* rwidth = VN_CAST_CONST(rhsp->widthp(), Const);
        if (!lstart || !rstart || !lwidth || !rwidth) return false;  // too complicated
        int rend = (rstart->toSInt() + rwidth->toSInt());
        return (rend == lstart->toSInt());
    }
    bool ifMergeAdjacent(AstNode* lhsp, AstNode* rhsp) {
        // called by concatmergeable to determine if {lhsp, rhsp} make sense
        if (!v3Global.opt.oAssemble()) return false;  // opt disabled
        // two same varref
        if (operandsSame(lhsp, rhsp)) return true;
        AstSel* lselp = VN_CAST(lhsp, Sel);
        AstSel* rselp = VN_CAST(rhsp, Sel);
        // a[i:0] a
        if (lselp && !rselp && rhsp->sameGateTree(lselp->fromp()))
            rselp = new AstSel(rhsp->fileline(), rhsp->cloneTree(false), 0, rhsp->width());
        // a[i:j] {a[j-1:k], b}
        if (lselp && !rselp && VN_IS(rhsp, Concat))
            return ifMergeAdjacent(lhsp, VN_CAST(rhsp, Concat)->lhsp());
        // a a[msb:j]
        if (rselp && !lselp && lhsp->sameGateTree(rselp->fromp()))
            lselp = new AstSel(lhsp->fileline(), lhsp->cloneTree(false), 0, lhsp->width());
        // {b, a[j:k]} a[k-1:i]
        if (rselp && !lselp && VN_IS(lhsp, Concat))
            return ifMergeAdjacent(VN_CAST(lhsp, Concat)->rhsp(), rhsp);
        if (!lselp || !rselp) return false;

        // a[a:b] a[b-1:c] are adjacent
        AstNode* lfromp = lselp->fromp();
        AstNode* rfromp = rselp->fromp();
        if (!lfromp || !rfromp || !lfromp->sameGateTree(rfromp)) return false;
        AstConst* lstart = VN_CAST(lselp->lsbp(), Const);
        AstConst* rstart = VN_CAST(rselp->lsbp(), Const);
        AstConst* lwidth = VN_CAST(lselp->widthp(), Const);
        AstConst* rwidth = VN_CAST(rselp->widthp(), Const);
        if (!lstart || !rstart || !lwidth || !rwidth) return false;  // too complicated
        int rend = (rstart->toSInt() + rwidth->toSInt());
        // a[i:j] a[j-1:k]
        if (rend == lstart->toSInt()) return true;
        // a[i:0] a[msb:j]
        if (rend == rfromp->width() && lstart->toSInt() == 0) return true;
        return false;
    }
    bool concatMergeable(const AstNode* lhsp, const AstNode* rhsp) {
        // determine if {a OP b, c OP d} => {a, c} OP {b, d} is advantageous
        if (!v3Global.opt.oAssemble()) return false;  // opt disabled
        if (lhsp->type() != rhsp->type()) return false;
        if (!ifConcatMergeableBiop(lhsp)) return false;

        const AstNodeBiop* lp = VN_CAST_CONST(lhsp, NodeBiop);
        const AstNodeBiop* rp = VN_CAST_CONST(rhsp, NodeBiop);
        if (!lp || !rp) return false;
        // {a[]&b[], a[]&b[]}
        bool lad = ifMergeAdjacent(lp->lhsp(), rp->lhsp());
        bool rad = ifMergeAdjacent(lp->rhsp(), rp->rhsp());
        if (lad && rad) return true;
        // {a[] & b[]&c[], a[] & b[]&c[]}
        if (lad && concatMergeable(lp->rhsp(), rp->rhsp())) return true;
        // {a[]&b[] & c[], a[]&b[] & c[]}
        if (rad && concatMergeable(lp->lhsp(), rp->lhsp())) return true;
        // {(a[]&b[])&(c[]&d[]), (a[]&b[])&(c[]&d[])}
        if (concatMergeable(lp->lhsp(), rp->lhsp()) && concatMergeable(lp->rhsp(), rp->rhsp())) {
            return true;
        }
        return false;
    }
    bool operandsSameSize(AstNode* lhsp, AstNode* rhsp) { return lhsp->width() == rhsp->width(); }

    //----------------------------------------
    // Constant Replacement functions.
    // These all take a node, delete its tree, and replaces it with a constant

    void replaceNum(AstNode* oldp, const V3Number& num) {
        // Replace oldp node with a constant set to specified value
        UASSERT(oldp, "Null old");
        UASSERT_OBJ(!(VN_IS(oldp, Const) && !VN_CAST(oldp, Const)->num().isFourState()), oldp,
                    "Already constant??");
        AstNode* newp = new AstConst(oldp->fileline(), num);
        newp->dtypeFrom(oldp);
        if (debug() > 5) oldp->dumpTree(cout, "  const_old: ");
        if (debug() > 5) newp->dumpTree(cout, "       _new: ");
        oldp->replaceWith(newp);
        VL_DO_DANGLING(oldp->deleteTree(), oldp);
    }
    void replaceNum(AstNode* nodep, uint32_t val) {
        V3Number num(nodep, nodep->width(), val);
        VL_DO_DANGLING(replaceNum(nodep, num), nodep);
    }
    void replaceNumSigned(AstNodeBiop* nodep, uint32_t val) {
        // We allow both sides to be constant, as one may have come from
        // parameter propagation, etc.
        if (m_warn && !(VN_IS(nodep->lhsp(), Const) && VN_IS(nodep->rhsp(), Const))) {
            nodep->v3warn(UNSIGNED, "Comparison is constant due to unsigned arithmetic");
        }
        VL_DO_DANGLING(replaceNum(nodep, val), nodep);
    }
    void replaceNumLimited(AstNodeBiop* nodep, uint32_t val) {
        // Avoids gcc warning about same
        if (m_warn) nodep->v3warn(CMPCONST, "Comparison is constant due to limited range");
        VL_DO_DANGLING(replaceNum(nodep, val), nodep);
    }
    void replaceZero(AstNode* nodep) { VL_DO_DANGLING(replaceNum(nodep, 0), nodep); }
    void replaceZeroChkPure(AstNode* nodep, AstNode* checkp) {
        // For example, "0 * n" -> 0 if n has no side effects
        // Else strength reduce it to 0 & n.
        // If ever change the operation note AstAnd rule specially ignores this created pattern
        if (isTPure(checkp)) {
            VL_DO_DANGLING(replaceNum(nodep, 0), nodep);
        } else {
            AstNode* newp = new AstAnd(nodep->fileline(), new AstConst(nodep->fileline(), 0),
                                       checkp->unlinkFrBack());
            newp->dtypeFrom(nodep);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }
    void replaceAllOnes(AstNode* nodep) {
        V3Number ones(nodep, nodep->width(), 0);
        ones.setMask(nodep->width());
        VL_DO_DANGLING(replaceNum(nodep, ones), nodep);
    }
    void replaceConst(AstNodeUniop* nodep) {
        V3Number num(nodep, nodep->width());
        nodep->numberOperate(num, VN_CAST(nodep->lhsp(), Const)->num());
        UINFO(4, "UNICONST -> " << num << endl);
        VL_DO_DANGLING(replaceNum(nodep, num), nodep);
    }
    void replaceConst(AstNodeBiop* nodep) {
        V3Number num(nodep, nodep->width());
        nodep->numberOperate(num, VN_CAST(nodep->lhsp(), Const)->num(),
                             VN_CAST(nodep->rhsp(), Const)->num());
        UINFO(4, "BICONST -> " << num << endl);
        VL_DO_DANGLING(replaceNum(nodep, num), nodep);
    }
    void replaceConst(AstNodeTriop* nodep) {
        V3Number num(nodep, nodep->width());
        nodep->numberOperate(num, VN_CAST(nodep->lhsp(), Const)->num(),
                             VN_CAST(nodep->rhsp(), Const)->num(),
                             VN_CAST(nodep->thsp(), Const)->num());
        UINFO(4, "TRICONST -> " << num << endl);
        VL_DO_DANGLING(replaceNum(nodep, num), nodep);
    }
    void replaceConst(AstNodeQuadop* nodep) {
        V3Number num(nodep, nodep->width());
        nodep->numberOperate(
            num, VN_CAST(nodep->lhsp(), Const)->num(), VN_CAST(nodep->rhsp(), Const)->num(),
            VN_CAST(nodep->thsp(), Const)->num(), VN_CAST(nodep->fhsp(), Const)->num());
        UINFO(4, "QUADCONST -> " << num << endl);
        VL_DO_DANGLING(replaceNum(nodep, num), nodep);
    }

    void replaceConstString(AstNode* oldp, const string& num) {
        // Replace oldp node with a constant set to specified value
        UASSERT(oldp, "Null old");
        AstNode* newp = new AstConst(oldp->fileline(), AstConst::String(), num);
        if (debug() > 5) oldp->dumpTree(cout, "  const_old: ");
        if (debug() > 5) newp->dumpTree(cout, "       _new: ");
        oldp->replaceWith(newp);
        VL_DO_DANGLING(oldp->deleteTree(), oldp);
    }
    //----------------------------------------
    // Replacement functions.
    // These all take a node and replace it with something else

    void replaceWChild(AstNode* nodep, AstNode* childp) {
        // NODE(..., CHILD(...)) -> CHILD(...)
        childp->unlinkFrBackWithNext();
        // If replacing a SEL for example, the data type comes from the parent (is less wide).
        // This may adversely affect the operation of the node being replaced.
        childp->dtypeFrom(nodep);
        nodep->replaceWith(childp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }

    //! Replace a ternary node with its RHS after iterating
    //! Used with short-circuiting, where the RHS has not yet been iterated.
    void replaceWIteratedRhs(AstNodeTriop* nodep) {
        if (AstNode* rhsp = nodep->rhsp()) iterateAndNextNull(rhsp);
        replaceWChild(nodep, nodep->rhsp());  // May have changed
    }

    //! Replace a ternary node with its THS after iterating
    //! Used with short-circuiting, where the THS has not yet been iterated.
    void replaceWIteratedThs(AstNodeTriop* nodep) {
        if (AstNode* thsp = nodep->thsp()) iterateAndNextNull(thsp);
        replaceWChild(nodep, nodep->thsp());  // May have changed
    }
    void replaceWLhs(AstNodeUniop* nodep) {
        // Keep LHS, remove RHS
        replaceWChild(nodep, nodep->lhsp());
    }
    void replaceWLhs(AstNodeBiop* nodep) {
        // Keep LHS, remove RHS
        replaceWChild(nodep, nodep->lhsp());
    }
    void replaceWRhs(AstNodeBiop* nodep) {
        // Keep RHS, remove LHS
        replaceWChild(nodep, nodep->rhsp());
    }
    void replaceAsv(AstNodeBiop* nodep) {
        // BIASV(CONSTa, BIASV(CONSTb, c)) -> BIASV( BIASV_CONSTED(a,b), c)
        // BIASV(SAMEa,  BIASV(SAMEb, c))  -> BIASV( BIASV(SAMEa,SAMEb), c)
        // nodep->dumpTree(cout, "  repAsvConst_old: ");
        AstNode* ap = nodep->lhsp();
        AstNodeBiop* rp = VN_CAST(nodep->rhsp(), NodeBiop);
        AstNode* bp = rp->lhsp();
        AstNode* cp = rp->rhsp();
        ap->unlinkFrBack();
        bp->unlinkFrBack();
        cp->unlinkFrBack();
        rp->unlinkFrBack();
        nodep->lhsp(rp);
        nodep->rhsp(cp);
        rp->lhsp(ap);
        rp->rhsp(bp);
        if (VN_IS(rp->lhsp(), Const) && VN_IS(rp->rhsp(), Const)) replaceConst(rp);
        // nodep->dumpTree(cout, "  repAsvConst_new: ");
    }
    void replaceAsvLUp(AstNodeBiop* nodep) {
        // BIASV(BIASV(CONSTll,lr),r) -> BIASV(CONSTll,BIASV(lr,r))
        AstNodeBiop* lp = VN_CAST(nodep->lhsp()->unlinkFrBack(), NodeBiop);
        AstNode* llp = lp->lhsp()->unlinkFrBack();
        AstNode* lrp = lp->rhsp()->unlinkFrBack();
        AstNode* rp = nodep->rhsp()->unlinkFrBack();
        nodep->lhsp(llp);
        nodep->rhsp(lp);
        lp->lhsp(lrp);
        lp->rhsp(rp);
        // nodep->dumpTree(cout, "  repAsvLUp_new: ");
    }
    void replaceAsvRUp(AstNodeBiop* nodep) {
        // BIASV(l,BIASV(CONSTrl,rr)) -> BIASV(CONSTrl,BIASV(l,rr))
        AstNode* lp = nodep->lhsp()->unlinkFrBack();
        AstNodeBiop* rp = VN_CAST(nodep->rhsp()->unlinkFrBack(), NodeBiop);
        AstNode* rlp = rp->lhsp()->unlinkFrBack();
        AstNode* rrp = rp->rhsp()->unlinkFrBack();
        nodep->lhsp(rlp);
        nodep->rhsp(rp);
        rp->lhsp(lp);
        rp->rhsp(rrp);
        // nodep->dumpTree(cout, "  repAsvRUp_new: ");
    }
    void replaceAndOr(AstNodeBiop* nodep) {
        //  OR  (AND (CONSTll,lr), AND(CONSTrl==ll,rr))    -> AND (CONSTll, OR(lr,rr))
        //  OR  (AND (CONSTll,lr), AND(CONSTrl,    rr=lr)) -> AND (OR(ll,rl), rr)
        // nodep ^lp  ^llp   ^lrp  ^rp  ^rlp       ^rrp
        // (Or/And may also be reversed)
        AstNodeBiop* lp = VN_CAST(nodep->lhsp()->unlinkFrBack(), NodeBiop);
        AstNode* llp = lp->lhsp()->unlinkFrBack();
        AstNode* lrp = lp->rhsp()->unlinkFrBack();
        AstNodeBiop* rp = VN_CAST(nodep->rhsp()->unlinkFrBack(), NodeBiop);
        AstNode* rlp = rp->lhsp()->unlinkFrBack();
        AstNode* rrp = rp->rhsp()->unlinkFrBack();
        nodep->replaceWith(lp);
        if (operandsSame(llp, rlp)) {
            lp->lhsp(llp);
            lp->rhsp(nodep);
            nodep->lhsp(lrp);
            nodep->rhsp(rrp);
            VL_DO_DANGLING(rp->deleteTree(), rp);
            VL_DO_DANGLING(rlp->deleteTree(), rlp);
        } else if (operandsSame(lrp, rrp)) {
            lp->lhsp(nodep);
            lp->rhsp(rrp);
            nodep->lhsp(llp);
            nodep->rhsp(rlp);
            VL_DO_DANGLING(rp->deleteTree(), rp);
            VL_DO_DANGLING(lrp->deleteTree(), lrp);
        } else {
            nodep->v3fatalSrc("replaceAndOr on something operandAndOrSame shouldn't have matched");
        }
        // nodep->dumpTree(cout, "  repAndOr_new: ");
    }
    void replaceShiftSame(AstNodeBiop* nodep) {
        // Or(Shift(ll,CONSTlr),Shift(rl,CONSTrr==lr)) -> Shift(Or(ll,rl),CONSTlr)
        // (Or/And may also be reversed)
        AstNodeBiop* lp = VN_CAST(nodep->lhsp()->unlinkFrBack(), NodeBiop);
        AstNode* llp = lp->lhsp()->unlinkFrBack();
        AstNode* lrp = lp->rhsp()->unlinkFrBack();
        AstNodeBiop* rp = VN_CAST(nodep->rhsp()->unlinkFrBack(), NodeBiop);
        AstNode* rlp = rp->lhsp()->unlinkFrBack();
        AstNode* rrp = rp->rhsp()->unlinkFrBack();
        nodep->replaceWith(lp);
        lp->lhsp(nodep);
        lp->rhsp(lrp);
        nodep->lhsp(llp);
        nodep->rhsp(rlp);
        VL_DO_DANGLING(rp->deleteTree(), rp);
        VL_DO_DANGLING(rrp->deleteTree(), rrp);
        // nodep->dumpTree(cout, "  repShiftSame_new: ");
    }
    void replaceConcatSel(AstConcat* nodep) {
        // {a[1], a[0]} -> a[1:0]
        AstSel* lselp = VN_CAST(nodep->lhsp()->unlinkFrBack(), Sel);
        AstSel* rselp = VN_CAST(nodep->rhsp()->unlinkFrBack(), Sel);
        int lstart = lselp->lsbConst();
        int lwidth = lselp->widthConst();
        int rstart = rselp->lsbConst();
        int rwidth = rselp->widthConst();

        UASSERT_OBJ((rstart + rwidth) == lstart, nodep,
                    "tried to merge two selects which are not adjacent");
        AstSel* newselp = new AstSel(lselp->fromp()->fileline(), rselp->fromp()->cloneTree(false),
                                     rstart, lwidth + rwidth);
        UINFO(5, "merged two adjacent sel " << lselp << " and " << rselp << " to one " << newselp
                                            << endl);

        nodep->replaceWith(newselp);
        VL_DO_DANGLING(lselp->deleteTree(), lselp);
        VL_DO_DANGLING(rselp->deleteTree(), rselp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void replaceConcatMerge(AstConcat* nodep) {
        AstNodeBiop* lp = VN_CAST(nodep->lhsp(), NodeBiop);
        AstNodeBiop* rp = VN_CAST(nodep->rhsp(), NodeBiop);
        AstNode* llp = lp->lhsp()->cloneTree(false);
        AstNode* lrp = lp->rhsp()->cloneTree(false);
        AstNode* rlp = rp->lhsp()->cloneTree(false);
        AstNode* rrp = rp->rhsp()->cloneTree(false);
        if (concatMergeable(lp, rp)) {
            AstConcat* newlp = new AstConcat(rlp->fileline(), llp, rlp);
            AstConcat* newrp = new AstConcat(rrp->fileline(), lrp, rrp);
            // use the lhs to replace the parent concat
            lp->lhsp()->replaceWith(newlp);
            lp->rhsp()->replaceWith(newrp);
            lp->dtypeChgWidthSigned(newlp->width(), newlp->width(), VSigning::UNSIGNED);
            UINFO(5, "merged " << nodep << endl);
            VL_DO_DANGLING(rp->unlinkFrBack()->deleteTree(), rp);
            nodep->replaceWith(lp->unlinkFrBack());
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            iterate(lp->lhsp());
            iterate(lp->rhsp());
        } else {
            nodep->v3fatalSrc("tried to merge two Concat which are not adjacent");
        }
    }
    void replaceExtend(AstNode* nodep, AstNode* arg0p) {
        // -> EXTEND(nodep)
        // like a AstExtend{$rhsp}, but we need to set the width correctly from base node
        arg0p->unlinkFrBack();
        AstNode* newp = (VN_IS(nodep, ExtendS)
                             ? static_cast<AstNode*>(new AstExtendS(nodep->fileline(), arg0p))
                             : static_cast<AstNode*>(new AstExtend(nodep->fileline(), arg0p)));
        newp->dtypeFrom(nodep);
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void replacePowShift(AstNodeBiop* nodep) {  // Pow or PowS
        UINFO(5, "POW(2,b)->SHIFTL(1,b) " << nodep << endl);
        AstNode* rhsp = nodep->rhsp()->unlinkFrBack();
        AstShiftL* newp
            = new AstShiftL(nodep->fileline(), new AstConst(nodep->fileline(), 1), rhsp);
        newp->dtypeFrom(nodep);
        newp->lhsp()->dtypeFrom(nodep);
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void replaceMulShift(AstMul* nodep) {  // Mul, but not MulS as not simple shift
        UINFO(5, "MUL(2^n,b)->SHIFTL(b,n) " << nodep << endl);
        int amount = VN_CAST(nodep->lhsp(), Const)->num().mostSetBitP1() - 1;  // 2^n->n+1
        AstNode* opp = nodep->rhsp()->unlinkFrBack();
        AstShiftL* newp
            = new AstShiftL(nodep->fileline(), opp, new AstConst(nodep->fileline(), amount));
        newp->dtypeFrom(nodep);
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void replaceDivShift(AstDiv* nodep) {  // Mul, but not MulS as not simple shift
        UINFO(5, "DIV(b,2^n)->SHIFTR(b,n) " << nodep << endl);
        int amount = VN_CAST(nodep->rhsp(), Const)->num().mostSetBitP1() - 1;  // 2^n->n+1
        AstNode* opp = nodep->lhsp()->unlinkFrBack();
        AstShiftR* newp
            = new AstShiftR(nodep->fileline(), opp, new AstConst(nodep->fileline(), amount));
        newp->dtypeFrom(nodep);
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void replaceModAnd(AstModDiv* nodep) {  // Mod, but not ModS as not simple shift
        UINFO(5, "MOD(b,2^n)->AND(b,2^n-1) " << nodep << endl);
        int amount = VN_CAST(nodep->rhsp(), Const)->num().mostSetBitP1() - 1;  // 2^n->n+1
        V3Number mask(nodep, nodep->width());
        mask.setMask(amount);
        AstNode* opp = nodep->lhsp()->unlinkFrBack();
        AstAnd* newp = new AstAnd(nodep->fileline(), opp, new AstConst(nodep->fileline(), mask));
        newp->dtypeFrom(nodep);
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void replaceShiftOp(AstNodeBiop* nodep) {
        UINFO(5, "SHIFT(AND(a,b),CONST)->AND(SHIFT(a,CONST),SHIFT(b,CONST)) " << nodep << endl);
        AstNRelinker handle;
        nodep->unlinkFrBack(&handle);
        AstNodeBiop* lhsp = VN_CAST(nodep->lhsp(), NodeBiop);
        lhsp->unlinkFrBack();
        AstNode* shiftp = nodep->rhsp()->unlinkFrBack();
        AstNode* ap = lhsp->lhsp()->unlinkFrBack();
        AstNode* bp = lhsp->rhsp()->unlinkFrBack();
        AstNodeBiop* shift1p = nodep;
        AstNodeBiop* shift2p = nodep->cloneTree(true);
        shift1p->lhsp(ap);
        shift1p->rhsp(shiftp->cloneTree(true));
        shift2p->lhsp(bp);
        shift2p->rhsp(shiftp);
        AstNodeBiop* newp = lhsp;
        newp->lhsp(shift1p);
        newp->rhsp(shift2p);
        handle.relink(newp);
        iterate(newp);  // Further reduce, either node may have more reductions.
    }
    void replaceShiftShift(AstNodeBiop* nodep) {
        UINFO(4, "SHIFT(SHIFT(a,s1),s2)->SHIFT(a,ADD(s1,s2)) " << nodep << endl);
        if (debug() >= 9) nodep->dumpTree(cout, "  repShiftShift_old: ");
        AstNodeBiop* lhsp = VN_CAST(nodep->lhsp(), NodeBiop);
        lhsp->unlinkFrBack();
        AstNode* ap = lhsp->lhsp()->unlinkFrBack();
        AstNode* shift1p = lhsp->rhsp()->unlinkFrBack();
        AstNode* shift2p = nodep->rhsp()->unlinkFrBack();
        // Shift1p and shift2p may have different sizes, both are
        // self-determined so sum with infinite width
        if (nodep->type() == lhsp->type()) {
            int shift1 = VN_CAST(shift1p, Const)->toUInt();
            int shift2 = VN_CAST(shift2p, Const)->toUInt();
            int newshift = shift1 + shift2;
            VL_DO_DANGLING(shift1p->deleteTree(), shift1p);
            VL_DO_DANGLING(shift2p->deleteTree(), shift2p);
            nodep->lhsp(ap);
            nodep->rhsp(new AstConst(nodep->fileline(), newshift));
            iterate(nodep);  // Further reduce, either node may have more reductions.
        } else {
            // We know shift amounts are constant, but might be a mixed left/right shift
            int shift1 = VN_CAST(shift1p, Const)->toUInt();
            if (VN_IS(lhsp, ShiftR)) shift1 = -shift1;
            int shift2 = VN_CAST(shift2p, Const)->toUInt();
            if (VN_IS(nodep, ShiftR)) shift2 = -shift2;
            int newshift = shift1 + shift2;
            VL_DO_DANGLING(shift1p->deleteTree(), shift1p);
            VL_DO_DANGLING(shift2p->deleteTree(), shift2p);
            AstNode* newp;
            V3Number mask1(nodep, nodep->width());
            V3Number ones(nodep, nodep->width());
            ones.setMask(nodep->width());
            if (shift1 < 0) {
                mask1.opShiftR(ones, V3Number(nodep, VL_IDATASIZE, -shift1));
            } else {
                mask1.opShiftL(ones, V3Number(nodep, VL_IDATASIZE, shift1));
            }
            V3Number mask(nodep, nodep->width());
            if (shift2 < 0) {
                mask.opShiftR(mask1, V3Number(nodep, VL_IDATASIZE, -shift2));
            } else {
                mask.opShiftL(mask1, V3Number(nodep, VL_IDATASIZE, shift2));
            }
            if (newshift < 0) {
                newp = new AstShiftR(nodep->fileline(), ap,
                                     new AstConst(nodep->fileline(), -newshift));
            } else {
                newp = new AstShiftL(nodep->fileline(), ap,
                                     new AstConst(nodep->fileline(), newshift));
            }
            newp->dtypeFrom(nodep);
            newp = new AstAnd(nodep->fileline(), newp, new AstConst(nodep->fileline(), mask));
            newp->dtypeFrom(nodep);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            // newp->dumpTree(cout, "  repShiftShift_new: ");
            iterate(newp);  // Further reduce, either node may have more reductions.
        }
        VL_DO_DANGLING(lhsp->deleteTree(), lhsp);
    }

    bool replaceAssignMultiSel(AstNodeAssign* nodep) {
        // Multiple assignments to sequential bits can be concated
        // ASSIGN(SEL(a),aq), ASSIGN(SEL(a+1),bq) -> ASSIGN(SEL(a:b),CONCAT(aq,bq)
        // ie. assign var[2]=a, assign var[3]=b -> assign var[3:2]={b,a}

        // Skip if we're not const'ing an entire module (IE doing only one assign, etc)
        if (!m_modp) return false;
        AstSel* sel1p = VN_CAST(nodep->lhsp(), Sel);
        if (!sel1p) return false;
        AstNodeAssign* nextp = VN_CAST(nodep->nextp(), NodeAssign);
        if (!nextp) return false;
        if (nodep->type() != nextp->type()) return false;
        AstSel* sel2p = VN_CAST(nextp->lhsp(), Sel);
        if (!sel2p) return false;
        AstVarRef* varref1p = VN_CAST(sel1p->fromp(), VarRef);
        if (!varref1p) return false;
        AstVarRef* varref2p = VN_CAST(sel2p->fromp(), VarRef);
        if (!varref2p) return false;
        if (!varref1p->sameGateTree(varref2p)) return false;
        AstConst* con1p = VN_CAST(sel1p->lsbp(), Const);
        if (!con1p) return false;
        AstConst* con2p = VN_CAST(sel2p->lsbp(), Const);
        if (!con2p) return false;
        // We need to make sure there's no self-references involved in either
        // assignment.  For speed, we only look 3 deep, then give up.
        if (!varNotReferenced(nodep->rhsp(), varref1p->varp())) return false;
        if (!varNotReferenced(nextp->rhsp(), varref2p->varp())) return false;
        // Swap?
        if ((con1p->toSInt() != con2p->toSInt() + sel2p->width())
            && (con2p->toSInt() != con1p->toSInt() + sel1p->width())) {
            return false;
        }
        bool lsbFirstAssign = (con1p->toUInt() < con2p->toUInt());
        UINFO(4, "replaceAssignMultiSel " << nodep << endl);
        UINFO(4, "                   && " << nextp << endl);
        // nodep->dumpTree(cout, "comb1: ");
        // nextp->dumpTree(cout, "comb2: ");
        AstNode* rhs1p = nodep->rhsp()->unlinkFrBack();
        AstNode* rhs2p = nextp->rhsp()->unlinkFrBack();
        AstNode* newp;
        if (lsbFirstAssign) {
            newp = nodep->cloneType(new AstSel(sel1p->fileline(), varref1p->unlinkFrBack(),
                                               sel1p->lsbConst(), sel1p->width() + sel2p->width()),
                                    new AstConcat(rhs1p->fileline(), rhs2p, rhs1p));
        } else {
            newp = nodep->cloneType(new AstSel(sel1p->fileline(), varref1p->unlinkFrBack(),
                                               sel2p->lsbConst(), sel1p->width() + sel2p->width()),
                                    new AstConcat(rhs1p->fileline(), rhs1p, rhs2p));
        }
        // pnewp->dumpTree(cout, "conew: ");
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
        VL_DO_DANGLING(nextp->unlinkFrBack()->deleteTree(), nextp);
        return true;
    }

    bool varNotReferenced(AstNode* nodep, AstVar* varp, int level = 0) {
        // Return true if varp never referenced under node.
        // Return false if referenced, or tree too deep to be worth it, or side effects
        if (!nodep) return true;
        if (level > 2) return false;
        if (!nodep->isPure()) return false;  // For example a $fgetc can't be reordered
        if (VN_IS(nodep, NodeVarRef) && VN_CAST(nodep, NodeVarRef)->varp() == varp) return false;
        return (varNotReferenced(nodep->nextp(), varp, level + 1)
                && varNotReferenced(nodep->op1p(), varp, level + 1)
                && varNotReferenced(nodep->op2p(), varp, level + 1)
                && varNotReferenced(nodep->op3p(), varp, level + 1)
                && varNotReferenced(nodep->op4p(), varp, level + 1));
    }

    bool replaceNodeAssign(AstNodeAssign* nodep) {
        if (VN_IS(nodep->lhsp(), VarRef) && VN_IS(nodep->rhsp(), VarRef)
            && VN_CAST(nodep->lhsp(), VarRef)->sameNoLvalue(VN_CAST(nodep->rhsp(), VarRef))
            && !VN_IS(nodep, AssignDly)) {
            // X = X.  Quite pointless, though X <= X may override another earlier assignment
            if (VN_IS(nodep, AssignW)) {
                nodep->v3error("Wire inputs its own output, creating circular logic (wire x=x)");
                return false;  // Don't delete the assign, or V3Gate will freak out
            } else {
                VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
                return true;
            }
        } else if (m_doV && VN_IS(nodep->lhsp(), Concat)) {
            bool need_temp = false;
            if (m_warn && !VN_IS(nodep, AssignDly)) {  // Is same var on LHS and RHS?
                // Note only do this (need user4) when m_warn, which is
                // done as unique visitor
                AstUser4InUse m_inuser4;
                ConstVarMarkVisitor mark(nodep->lhsp());
                ConstVarFindVisitor find(nodep->rhsp());
                if (find.found()) need_temp = true;
            }
            if (need_temp) {
                // The first time we constify, there may be the same variable on the LHS
                // and RHS.  In that case, we must use temporaries, or {a,b}={b,a} will break.
                UINFO(4, "  ASSITEMP " << nodep << endl);
                // ASSIGN(CONCAT(lc1,lc2),rhs) -> ASSIGN(temp1,SEL(rhs,{size})),
                //                                ASSIGN(temp2,SEL(newrhs,{size}))
                //                                ASSIGN(lc1,temp1),
                //                                ASSIGN(lc2,temp2)
            } else {
                UINFO(4, "  ASSI " << nodep << endl);
                // ASSIGN(CONCAT(lc1,lc2),rhs) -> ASSIGN(lc1,SEL(rhs,{size})),
                //                                ASSIGN(lc2,SEL(newrhs,{size}))
            }
            if (debug() >= 9) nodep->dumpTree(cout, "  Ass_old: ");
            // Unlink the stuff
            AstNode* lc1p = VN_CAST(nodep->lhsp(), Concat)->lhsp()->unlinkFrBack();
            AstNode* lc2p = VN_CAST(nodep->lhsp(), Concat)->rhsp()->unlinkFrBack();
            AstNode* conp = VN_CAST(nodep->lhsp(), Concat)->unlinkFrBack();
            AstNode* rhsp = nodep->rhsp()->unlinkFrBack();
            AstNode* rhs2p = rhsp->cloneTree(false);
            // Calc widths
            int lsb2 = 0;
            int msb2 = lsb2 + lc2p->width() - 1;
            int lsb1 = msb2 + 1;
            int msb1 = lsb1 + lc1p->width() - 1;
            UASSERT_OBJ(msb1 == (conp->width() - 1), nodep, "Width calc mismatch");
            // Form ranges
            AstSel* sel1p = new AstSel(conp->fileline(), rhsp, lsb1, msb1 - lsb1 + 1);
            AstSel* sel2p = new AstSel(conp->fileline(), rhs2p, lsb2, msb2 - lsb2 + 1);
            // Make new assigns of same flavor as old one
            //*** Not cloneTree; just one node.
            AstNode* newp = nullptr;
            if (!need_temp) {
                AstNodeAssign* asn1ap = VN_CAST(nodep->cloneType(lc1p, sel1p), NodeAssign);
                AstNodeAssign* asn2ap = VN_CAST(nodep->cloneType(lc2p, sel2p), NodeAssign);
                asn1ap->dtypeFrom(sel1p);
                asn2ap->dtypeFrom(sel2p);
                newp = AstNode::addNext(newp, asn1ap);
                newp = AstNode::addNext(newp, asn2ap);
            } else {
                UASSERT_OBJ(m_modp, nodep, "Not under module");
                // We could create just one temp variable, but we'll get better optimization
                // if we make one per term.
                string name1 = (string("__Vconcswap") + cvtToStr(m_modp->varNumGetInc()));
                string name2 = (string("__Vconcswap") + cvtToStr(m_modp->varNumGetInc()));
                AstVar* temp1p = new AstVar(sel1p->fileline(), AstVarType::BLOCKTEMP, name1,
                                            VFlagLogicPacked(), msb1 - lsb1 + 1);
                AstVar* temp2p = new AstVar(sel2p->fileline(), AstVarType::BLOCKTEMP, name2,
                                            VFlagLogicPacked(), msb2 - lsb2 + 1);
                m_modp->addStmtp(temp1p);
                m_modp->addStmtp(temp2p);
                AstNodeAssign* asn1ap
                    = VN_CAST(nodep->cloneType(
                                  new AstVarRef(sel1p->fileline(), temp1p, VAccess::WRITE), sel1p),
                              NodeAssign);
                AstNodeAssign* asn2ap
                    = VN_CAST(nodep->cloneType(
                                  new AstVarRef(sel2p->fileline(), temp2p, VAccess::WRITE), sel2p),
                              NodeAssign);
                AstNodeAssign* asn1bp
                    = VN_CAST(nodep->cloneType(
                                  lc1p, new AstVarRef(sel1p->fileline(), temp1p, VAccess::READ)),
                              NodeAssign);
                AstNodeAssign* asn2bp
                    = VN_CAST(nodep->cloneType(
                                  lc2p, new AstVarRef(sel2p->fileline(), temp2p, VAccess::READ)),
                              NodeAssign);
                asn1ap->dtypeFrom(temp1p);
                asn1bp->dtypeFrom(temp1p);
                asn2ap->dtypeFrom(temp2p);
                asn2bp->dtypeFrom(temp2p);
                // This order matters
                newp = AstNode::addNext(newp, asn1ap);
                newp = AstNode::addNext(newp, asn2ap);
                newp = AstNode::addNext(newp, asn1bp);
                newp = AstNode::addNext(newp, asn2bp);
            }
            if (debug() >= 9 && newp) newp->dumpTreeAndNext(cout, "     _new: ");
            nodep->addNextHere(newp);
            // Cleanup
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            VL_DO_DANGLING(conp->deleteTree(), conp);
            // Further reduce, either node may have more reductions.
            return true;
        } else if (m_doV && VN_IS(nodep->rhsp(), StreamR)) {
            // The right-streaming operator on rhs of assignment does not
            // change the order of bits. Eliminate stream but keep its lhsp
            // Unlink the stuff
            AstNode* srcp = VN_CAST(nodep->rhsp(), StreamR)->lhsp()->unlinkFrBack();
            AstNode* sizep = VN_CAST(nodep->rhsp(), StreamR)->rhsp()->unlinkFrBack();
            AstNode* streamp = VN_CAST(nodep->rhsp(), StreamR)->unlinkFrBack();
            nodep->rhsp(srcp);
            // Cleanup
            VL_DO_DANGLING(sizep->deleteTree(), sizep);
            VL_DO_DANGLING(streamp->deleteTree(), streamp);
            // Further reduce, any of the nodes may have more reductions.
            return true;
        } else if (m_doV && VN_IS(nodep->lhsp(), StreamL)) {
            // Push the stream operator to the rhs of the assignment statement
            int dWidth = VN_CAST(nodep->lhsp(), StreamL)->lhsp()->width();
            int sWidth = nodep->rhsp()->width();
            // Unlink the stuff
            AstNode* dstp = VN_CAST(nodep->lhsp(), StreamL)->lhsp()->unlinkFrBack();
            AstNode* streamp = VN_CAST(nodep->lhsp(), StreamL)->unlinkFrBack();
            AstNode* srcp = nodep->rhsp()->unlinkFrBack();
            // Connect the rhs to the stream operator and update its width
            VN_CAST(streamp, StreamL)->lhsp(srcp);
            streamp->dtypeSetLogicUnsized(srcp->width(), srcp->widthMin(), VSigning::UNSIGNED);
            // Shrink the RHS if necessary
            if (sWidth > dWidth) {
                streamp = new AstSel(streamp->fileline(), streamp, sWidth - dWidth, dWidth);
            }
            // Link the nodes back in
            nodep->lhsp(dstp);
            nodep->rhsp(streamp);
            return true;
        } else if (m_doV && VN_IS(nodep->lhsp(), StreamR)) {
            // The right stream operator on lhs of assignment statement does
            // not reorder bits. However, if the rhs is wider than the lhs,
            // then we select bits from the left-most, not the right-most.
            int dWidth = VN_CAST(nodep->lhsp(), StreamR)->lhsp()->width();
            int sWidth = nodep->rhsp()->width();
            // Unlink the stuff
            AstNode* dstp = VN_CAST(nodep->lhsp(), StreamR)->lhsp()->unlinkFrBack();
            AstNode* sizep = VN_CAST(nodep->lhsp(), StreamR)->rhsp()->unlinkFrBack();
            AstNode* streamp = VN_CAST(nodep->lhsp(), StreamR)->unlinkFrBack();
            AstNode* srcp = nodep->rhsp()->unlinkFrBack();
            if (sWidth > dWidth) {
                srcp = new AstSel(streamp->fileline(), srcp, sWidth - dWidth, dWidth);
            }
            nodep->lhsp(dstp);
            nodep->rhsp(srcp);
            // Cleanup
            VL_DO_DANGLING(sizep->deleteTree(), sizep);
            VL_DO_DANGLING(streamp->deleteTree(), streamp);
            // Further reduce, any of the nodes may have more reductions.
            return true;
        } else if (m_doV && replaceAssignMultiSel(nodep)) {
            return true;
        }
        return false;
    }

    // Boolean replacements
    bool operandBoolShift(const AstNode* nodep) {
        // boolean test of AND(const,SHIFTR(x,const)) -> test of AND(SHIFTL(x,const), x)
        if (!VN_IS(nodep, And)) return false;
        if (!VN_IS(VN_CAST_CONST(nodep, And)->lhsp(), Const)) return false;
        if (!VN_IS(VN_CAST_CONST(nodep, And)->rhsp(), ShiftR)) return false;
        const AstShiftR* shiftp = VN_CAST(VN_CAST_CONST(nodep, And)->rhsp(), ShiftR);
        if (!VN_IS(shiftp->rhsp(), Const)) return false;
        if (static_cast<uint32_t>(nodep->width())
            <= VN_CAST_CONST(shiftp->rhsp(), Const)->toUInt()) {
            return false;
        }
        return true;
    }
    void replaceBoolShift(AstNode* nodep) {
        if (debug() >= 9) nodep->dumpTree(cout, "  bshft_old: ");
        AstConst* andConstp = VN_CAST(VN_CAST(nodep, And)->lhsp(), Const);
        AstNode* fromp = VN_CAST(VN_CAST(nodep, And)->rhsp(), ShiftR)->lhsp()->unlinkFrBack();
        AstConst* shiftConstp
            = VN_CAST(VN_CAST(VN_CAST(nodep, And)->rhsp(), ShiftR)->rhsp(), Const);
        V3Number val(andConstp, andConstp->width());
        val.opShiftL(andConstp->num(), shiftConstp->num());
        AstAnd* newp = new AstAnd(nodep->fileline(), new AstConst(nodep->fileline(), val), fromp);
        // widthMin no longer applicable if different C-expanded width
        newp->dtypeSetLogicSized(nodep->width(), VSigning::UNSIGNED);
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
        if (debug() >= 9) newp->dumpTree(cout, "       _new: ");
    }

    void replaceWithSimulation(AstNode* nodep) {
        SimulateVisitor simvis;
        // Run it - may be unoptimizable due to large for loop, etc
        simvis.mainParamEmulate(nodep);
        if (!simvis.optimizable()) {
            AstNode* errorp = simvis.whyNotNodep();
            if (!errorp) errorp = nodep;
            nodep->v3error("Expecting expression to be constant, but can't determine constant for "
                           << nodep->prettyTypeName() << '\n'
                           << errorp->warnOther() << "... Location of non-constant "
                           << errorp->prettyTypeName() << ": " << simvis.whyNotMessage());
            VL_DO_DANGLING(replaceZero(nodep), nodep);
        } else {
            // Fetch the result
            AstNode* valuep = simvis.fetchValueNull(nodep);  // valuep is owned by Simulate
            UASSERT_OBJ(valuep, nodep, "No value returned from simulation");
            // Replace it
            AstNode* newp = valuep->cloneTree(false);
            newp->dtypeFrom(nodep);
            newp->fileline(nodep->fileline());
            UINFO(4, "Simulate->" << newp << endl);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }

    //----------------------------------------

    // VISITORS
    virtual void visit(AstNetlist* nodep) override {
        // Iterate modules backwards, in bottom-up order.  That's faster
        iterateChildrenBackwards(nodep);
    }
    virtual void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        {
            m_modp = nodep;
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstCFunc* nodep) override {
        // No ASSIGNW removals under funcs, we've long eliminated INITIALs
        // (We should perhaps rename the assignw's to just assigns)
        VL_RESTORER(m_wremove);
        {
            m_wremove = false;
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstScope* nodep) override {
        // No ASSIGNW removals under scope, we've long eliminated INITIALs
        VL_RESTORER(m_wremove);
        VL_RESTORER(m_scopep);
        {
            m_wremove = false;
            m_scopep = nodep;
            iterateChildren(nodep);
        }
    }

    void swapSides(AstNodeBiCom* nodep) {
        // COMMUTATIVE({a},CONST) -> COMMUTATIVE(CONST,{a})
        // This simplifies later optimizations
        AstNode* lhsp = nodep->lhsp()->unlinkFrBackWithNext();
        AstNode* rhsp = nodep->rhsp()->unlinkFrBackWithNext();
        nodep->lhsp(rhsp);
        nodep->rhsp(lhsp);
        iterate(nodep);  // Again?
    }

    int operandConcatMove(AstConcat* nodep) {
        //    CONCAT under concat  (See moveConcat)
        // Return value: true indicates to do it; 2 means move to LHS
        AstConcat* abConcp = VN_CAST(nodep->lhsp(), Concat);
        AstConcat* bcConcp = VN_CAST(nodep->rhsp(), Concat);
        if (!abConcp && !bcConcp) return 0;
        if (bcConcp) {
            AstNode* ap = nodep->lhsp();
            AstNode* bp = bcConcp->lhsp();
            // If a+b == 32,64,96 etc, then we want to have a+b together on LHS
            if (VL_BITBIT_I(ap->width() + bp->width()) == 0) return 2;  // Transform 2: to abConc
        } else {  // abConcp
            // Unless lhs is already 32 bits due to above, reorder it
            if (VL_BITBIT_I(nodep->lhsp()->width()) != 0) return 1;  // Transform 1: to bcConc
        }
        return 0;  // ok
    }
    void moveConcat(AstConcat* nodep) {
        //    1: CONCAT(CONCAT({a},{b}),{c})  -> CONCAT({a},CONCAT({b}, {c}))
        // or 2: CONCAT({a}, CONCAT({b},{c})) -> CONCAT(CONCAT({a},{b}),{c})
        // Because the lhs of a concat needs a shift but the rhs doesn't,
        // putting additional CONCATs on the RHS leads to fewer assembler operations.
        // However, we'll end up with lots of wide moves if we make huge trees
        // like that, so on 32 bit boundaries, we'll do the opposite form.
        UINFO(4, "Move concat: " << nodep << endl);
        if (operandConcatMove(nodep) > 1) {
            AstNode* ap = nodep->lhsp()->unlinkFrBack();
            AstConcat* bcConcp = VN_CAST(nodep->rhsp(), Concat);
            bcConcp->unlinkFrBack();
            AstNode* bp = bcConcp->lhsp()->unlinkFrBack();
            AstNode* cp = bcConcp->rhsp()->unlinkFrBack();
            AstConcat* abConcp = new AstConcat(bcConcp->fileline(), ap, bp);
            nodep->lhsp(abConcp);
            nodep->rhsp(cp);
            // If bp was a concat, then we have this exact same form again!
            // Recurse rather then calling node->iterate to prevent 2^n recursion!
            if (operandConcatMove(abConcp)) moveConcat(abConcp);
            VL_DO_DANGLING(bcConcp->deleteTree(), bcConcp);
        } else {
            AstConcat* abConcp = VN_CAST(nodep->lhsp(), Concat);
            abConcp->unlinkFrBack();
            AstNode* ap = abConcp->lhsp()->unlinkFrBack();
            AstNode* bp = abConcp->rhsp()->unlinkFrBack();
            AstNode* cp = nodep->rhsp()->unlinkFrBack();
            AstConcat* bcConcp = new AstConcat(abConcp->fileline(), bp, cp);
            nodep->lhsp(ap);
            nodep->rhsp(bcConcp);
            if (operandConcatMove(bcConcp)) moveConcat(bcConcp);
            VL_DO_DANGLING(abConcp->deleteTree(), abConcp);
        }
    }

    // Special cases
    virtual void visit(AstConst*) override {}  // Already constant

    virtual void visit(AstCell* nodep) override {
        if (m_params) {
            iterateAndNextNull(nodep->paramsp());
        } else {
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstPin* nodep) override { iterateChildren(nodep); }

    void replaceLogEq(AstLogEq* nodep) {
        // LOGEQ(a,b) => AstLogAnd{AstLogOr{AstLogNot{a},b},AstLogOr{AstLogNot{b},a}}
        AstNode* lhsp = nodep->lhsp()->unlinkFrBack();
        AstNode* rhsp = nodep->rhsp()->unlinkFrBack();
        // Do exactly as IEEE says, might result in extra terms, so in future may do differently
        AstLogAnd* newp = new AstLogAnd(
            nodep->fileline(),
            new AstLogOr(nodep->fileline(), new AstLogNot(nodep->fileline(), lhsp), rhsp),
            new AstLogOr(nodep->fileline(),
                         new AstLogNot(nodep->fileline(), rhsp->cloneTree(false)),
                         lhsp->cloneTree(false)));
        newp->dtypeFrom(nodep);
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }

    void replaceSelSel(AstSel* nodep) {
        // SEL(SEL({x},a,b),c,d) => SEL({x},a+c,d)
        AstSel* belowp = VN_CAST(nodep->fromp(), Sel);
        AstNode* fromp = belowp->fromp()->unlinkFrBack();
        AstNode* widthp = nodep->widthp()->unlinkFrBack();
        AstNode* lsb1p = nodep->lsbp()->unlinkFrBack();
        AstNode* lsb2p = belowp->lsbp()->unlinkFrBack();
        // Eliminate lower range
        UINFO(4, "Elim Lower range: " << nodep << endl);
        AstNode* newlsbp;
        if (VN_IS(lsb1p, Const) && VN_IS(lsb2p, Const)) {
            newlsbp = new AstConst(lsb1p->fileline(), VN_CAST(lsb1p, Const)->toUInt()
                                                          + VN_CAST(lsb2p, Const)->toUInt());
            VL_DO_DANGLING(lsb1p->deleteTree(), lsb1p);
            VL_DO_DANGLING(lsb2p->deleteTree(), lsb2p);
        } else {
            // Width is important, we need the width of the fromp's
            // expression, not the potentially smaller lsb1p's width
            newlsbp
                = new AstAdd(lsb1p->fileline(), lsb2p, new AstExtend(lsb1p->fileline(), lsb1p));
            newlsbp->dtypeFrom(lsb2p);  // Unsigned
            VN_CAST(newlsbp, Add)->rhsp()->dtypeFrom(lsb2p);
        }
        AstSel* newp = new AstSel(nodep->fileline(), fromp, newlsbp, widthp);
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }

    void replaceSelConcat(AstSel* nodep) {
        // SEL(CONCAT(a,b),c,d) => SEL(a or b, . .)
        AstConcat* conp = VN_CAST(nodep->fromp(), Concat);
        AstNode* conLhsp = conp->lhsp();
        AstNode* conRhsp = conp->rhsp();
        if (static_cast<int>(nodep->lsbConst()) >= conRhsp->width()) {
            conLhsp->unlinkFrBack();
            AstSel* newp = new AstSel(nodep->fileline(), conLhsp,
                                      nodep->lsbConst() - conRhsp->width(), nodep->widthConst());
            nodep->replaceWith(newp);
        } else if (static_cast<int>(nodep->msbConst()) < conRhsp->width()) {
            conRhsp->unlinkFrBack();
            AstSel* newp
                = new AstSel(nodep->fileline(), conRhsp, nodep->lsbConst(), nodep->widthConst());
            nodep->replaceWith(newp);
        } else {
            // Yuk, split between the two
            conRhsp->unlinkFrBack();
            conLhsp->unlinkFrBack();
            AstConcat* newp
                = new AstConcat(nodep->fileline(),
                                new AstSel(nodep->fileline(), conLhsp, 0,
                                           nodep->msbConst() - conRhsp->width() + 1),
                                new AstSel(nodep->fileline(), conRhsp, nodep->lsbConst(),
                                           conRhsp->width() - nodep->lsbConst()));
            nodep->replaceWith(newp);
        }
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    bool operandSelReplicate(AstSel* nodep) {
        // SEL(REPLICATE(from,rep),lsb,width) => SEL(from,0,width) as long
        // as SEL's width <= b's width
        AstReplicate* repp = VN_CAST(nodep->fromp(), Replicate);
        AstNode* fromp = repp->lhsp();
        AstConst* lsbp = VN_CAST(nodep->lsbp(), Const);
        if (!lsbp) return false;
        AstNode* widthp = nodep->widthp();
        if (!VN_IS(widthp, Const)) return false;
        UASSERT_OBJ(fromp->width(), nodep, "Not widthed");
        if ((lsbp->toUInt() / fromp->width())
            != ((lsbp->toUInt() + nodep->width() - 1) / fromp->width())) {
            return false;
        }
        //
        fromp->unlinkFrBack();
        widthp->unlinkFrBack();
        AstSel* newp
            = new AstSel(nodep->fileline(), fromp,
                         new AstConst(lsbp->fileline(), lsbp->toUInt() % fromp->width()), widthp);
        newp->dtypeFrom(nodep);
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
        return true;
    }
    bool operandRepRep(AstReplicate* nodep) {
        // REPLICATE(REPLICATE2(from2,cnt2),cnt1) => REPLICATE(from2,(cnt1+cnt2))
        AstReplicate* rep2p = VN_CAST(nodep->lhsp(), Replicate);
        AstNode* from2p = rep2p->lhsp();
        AstConst* cnt1p = VN_CAST(nodep->rhsp(), Const);
        if (!cnt1p) return false;
        AstConst* cnt2p = VN_CAST(rep2p->rhsp(), Const);
        if (!cnt2p) return false;
        //
        from2p->unlinkFrBack();
        cnt1p->unlinkFrBack();
        cnt2p->unlinkFrBack();
        AstReplicate* newp
            = new AstReplicate(nodep->fileline(), from2p, cnt1p->toUInt() * cnt2p->toUInt());
        newp->dtypeFrom(nodep);
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
        return true;
    }
    bool operandConcatSame(AstConcat* nodep) {
        // CONCAT(fromp,fromp) -> REPLICATE(fromp,1+1)
        // CONCAT(REP(fromp,cnt1),fromp) -> REPLICATE(fromp,cnt1+1)
        // CONCAT(fromp,REP(fromp,cnt1)) -> REPLICATE(fromp,1+cnt1)
        // CONCAT(REP(fromp,cnt1),REP(fromp,cnt2)) -> REPLICATE(fromp,cnt1+cnt2)
        AstNode* from1p = nodep->lhsp();
        uint32_t cnt1 = 1;
        AstNode* from2p = nodep->rhsp();
        uint32_t cnt2 = 1;
        if (VN_IS(from1p, Replicate)) {
            AstConst* cnt1p = VN_CAST(VN_CAST(from1p, Replicate)->rhsp(), Const);
            if (!cnt1p) return false;
            from1p = VN_CAST(from1p, Replicate)->lhsp();
            cnt1 = cnt1p->toUInt();
        }
        if (VN_IS(from2p, Replicate)) {
            AstConst* cnt2p = VN_CAST(VN_CAST(from2p, Replicate)->rhsp(), Const);
            if (!cnt2p) return false;
            from2p = VN_CAST(from2p, Replicate)->lhsp();
            cnt2 = cnt2p->toUInt();
        }
        if (!operandsSame(from1p, from2p)) return false;
        //
        from1p->unlinkFrBack();
        AstReplicate* newp = new AstReplicate(nodep->fileline(), from1p, cnt1 + cnt2);
        newp->dtypeFrom(nodep);
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
        return true;
    }
    void replaceSelIntoBiop(AstSel* nodep) {
        // SEL(BUFIF1(a,b),1,bit) => BUFIF1(SEL(a,1,bit),SEL(b,1,bit))
        AstNodeBiop* fromp = VN_CAST(nodep->fromp()->unlinkFrBack(), NodeBiop);
        UASSERT_OBJ(fromp, nodep, "Called on non biop");
        AstNode* lsbp = nodep->lsbp()->unlinkFrBack();
        AstNode* widthp = nodep->widthp()->unlinkFrBack();
        //
        AstNode* bilhsp = fromp->lhsp()->unlinkFrBack();
        AstNode* birhsp = fromp->rhsp()->unlinkFrBack();
        //
        fromp->lhsp(
            new AstSel(nodep->fileline(), bilhsp, lsbp->cloneTree(true), widthp->cloneTree(true)));
        fromp->rhsp(new AstSel(nodep->fileline(), birhsp, lsbp, widthp));
        fromp->dtypeFrom(nodep);
        nodep->replaceWith(fromp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void replaceSelIntoUniop(AstSel* nodep) {
        // SEL(NOT(a),1,bit) => NOT(SEL(a,bit))
        AstNodeUniop* fromp = VN_CAST(nodep->fromp()->unlinkFrBack(), NodeUniop);
        UASSERT_OBJ(fromp, nodep, "Called on non biop");
        AstNode* lsbp = nodep->lsbp()->unlinkFrBack();
        AstNode* widthp = nodep->widthp()->unlinkFrBack();
        //
        AstNode* bilhsp = fromp->lhsp()->unlinkFrBack();
        //
        fromp->lhsp(new AstSel(nodep->fileline(), bilhsp, lsbp, widthp));
        fromp->dtypeFrom(nodep);
        nodep->replaceWith(fromp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }

    virtual void visit(AstAttrOf* nodep) override {
        VL_RESTORER(m_attrp);
        {
            m_attrp = nodep;
            iterateChildren(nodep);
        }
    }

    virtual void visit(AstArraySel* nodep) override {
        iterateAndNextNull(nodep->bitp());
        if (VN_IS(nodep->bitp(), Const)
            && VN_IS(nodep->fromp(), VarRef)
            // Need to make sure it's an array object so don't mis-allow a constant (bug509.)
            && VN_CAST(nodep->fromp(), VarRef)->varp()
            && VN_IS(VN_CAST(nodep->fromp(), VarRef)->varp()->valuep(), InitArray)) {
            m_selp = nodep;  // Ask visit(AstVarRef) to replace varref with const
        }
        iterateAndNextNull(nodep->fromp());
        if (VN_IS(nodep->fromp(), Const)) {  // It did.
            if (!m_selp) {
                nodep->v3error("Illegal assignment of constant to unpacked array");
            } else {
                AstNode* fromp = nodep->fromp()->unlinkFrBack();
                nodep->replaceWith(fromp);
                if (VN_IS(fromp->dtypep()->skipRefp(), NodeArrayDType)) {
                    // Strip off array to find what array references
                    fromp->dtypeFrom(
                        VN_CAST(fromp->dtypep()->skipRefp(), NodeArrayDType)->subDTypep());
                }
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
            }
        }
        m_selp = nullptr;
    }
    virtual void visit(AstNodeVarRef* nodep) override {
        iterateChildren(nodep);
        UASSERT_OBJ(nodep->varp(), nodep, "Not linked");
        bool did = false;
        if (m_doV && nodep->varp()->valuep() && !m_attrp) {
            // if (debug()) valuep->dumpTree(cout, "  visitvaref: ");
            iterateAndNextNull(nodep->varp()->valuep());  // May change nodep->varp()->valuep()
            AstNode* valuep = nodep->varp()->valuep();
            if (nodep->access().isReadOnly()
                && ((!m_params  // Can reduce constant wires into equations
                     && m_doNConst
                     && v3Global.opt.oConst()
                     // Default value, not a "known" constant for this usage
                     && !nodep->varp()->isClassMember()
                     && !(nodep->varp()->isFuncLocal() && nodep->varp()->isNonOutput())
                     && !nodep->varp()->noSubst() && !nodep->varp()->isSigPublic())
                    || nodep->varp()->isParam())) {
                if (operandConst(valuep)) {
                    const V3Number& num = VN_CAST(valuep, Const)->num();
                    // UINFO(2,"constVisit "<<cvtToHex(valuep)<<" "<<num<<endl);
                    VL_DO_DANGLING(replaceNum(nodep, num), nodep);
                    did = true;
                } else if (m_selp && VN_IS(valuep, InitArray)) {
                    AstInitArray* initarp = VN_CAST(valuep, InitArray);
                    uint32_t bit = m_selp->bitConst();
                    AstNode* itemp = initarp->getIndexDefaultedValuep(bit);
                    if (VN_IS(itemp, Const)) {
                        const V3Number& num = VN_CAST(itemp, Const)->num();
                        // UINFO(2,"constVisit "<<cvtToHex(valuep)<<" "<<num<<endl);
                        VL_DO_DANGLING(replaceNum(nodep, num), nodep);
                        did = true;
                    }
                } else if (m_params && VN_IS(valuep, InitArray)) {
                    // Allow parameters to pass arrays
                    // Earlier recursion of InitArray made sure each array value is constant
                    // This exception is fairly fragile, i.e. doesn't
                    // support arrays of arrays or other stuff
                    AstNode* newp = valuep->cloneTree(false);
                    nodep->replaceWith(newp);
                    VL_DO_DANGLING(nodep->deleteTree(), nodep);
                    did = true;
                } else if (nodep->varp()->isParam() && VN_IS(valuep, Unbounded)) {
                    AstNode* newp = valuep->cloneTree(false);
                    nodep->replaceWith(newp);
                    VL_DO_DANGLING(nodep->deleteTree(), nodep);
                    did = true;
                }
            }
        }
        if (!did && m_required) {
            nodep->v3error("Expecting expression to be constant, but variable isn't const: "
                           << nodep->varp()->prettyNameQ());
        }
    }
    virtual void visit(AstEnumItemRef* nodep) override {
        iterateChildren(nodep);
        UASSERT_OBJ(nodep->itemp(), nodep, "Not linked");
        bool did = false;
        if (nodep->itemp()->valuep()) {
            // if (debug()) nodep->itemp()->valuep()->dumpTree(cout, "  visitvaref: ");
            if (nodep->itemp()->user4()) {
                nodep->v3error("Recursive enum value: " << nodep->itemp()->prettyNameQ());
            } else {
                nodep->itemp()->user4(true);
                iterateAndNextNull(nodep->itemp()->valuep());
                nodep->itemp()->user4(false);
            }
            if (AstConst* valuep = VN_CAST(nodep->itemp()->valuep(), Const)) {
                const V3Number& num = valuep->num();
                VL_DO_DANGLING(replaceNum(nodep, num), nodep);
                did = true;
            }
        }
        if (!did && m_required) {
            nodep->v3error("Expecting expression to be constant, but enum value isn't const: "
                           << nodep->itemp()->prettyNameQ());
        }
    }

    // virtual void visit(AstCvtPackString* nodep) override {
    // Not constant propagated (for today) because AstNodeMath::isOpaque is set
    // Someday if lower is constant, convert to quoted "string".

    bool onlySenItemInSenTree(AstSenItem* nodep) {
        // Only one if it's not in a list
        return (!nodep->nextp() && nodep->backp()->nextp() != nodep);
    }
    virtual void visit(AstSenItem* nodep) override {
        iterateChildren(nodep);
        if (m_doNConst
            && (VN_IS(nodep->sensp(), Const) || VN_IS(nodep->sensp(), EnumItemRef)
                || (nodep->varrefp() && nodep->varrefp()->varp()->isParam()))) {
            // Constants in sensitivity lists may be removed (we'll simplify later)
            if (nodep->isClocked()) {  // A constant can never get a pos/negedge
                if (onlySenItemInSenTree(nodep)) {
                    nodep->replaceWith(new AstSenItem(nodep->fileline(), AstSenItem::Never()));
                    VL_DO_DANGLING(nodep->deleteTree(), nodep);
                } else {
                    VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
                }
            } else {  // Otherwise it may compute a result that needs to settle out
                nodep->replaceWith(new AstSenItem(nodep->fileline(), AstSenItem::Combo()));
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
            }
        } else if (m_doNConst && VN_IS(nodep->sensp(), Not)) {
            // V3Gate may propagate NOTs into clocks... Just deal with it
            AstNode* sensp = nodep->sensp();
            AstNode* lastSensp = sensp;
            bool invert = false;
            while (VN_IS(lastSensp, Not)) {
                lastSensp = VN_CAST(lastSensp, Not)->lhsp();
                invert = !invert;
            }
            UINFO(8, "senItem(NOT...) " << nodep << " " << invert << endl);
            if (invert) nodep->edgeType(nodep->edgeType().invert());
            AstNodeVarRef* senvarp = VN_CAST(lastSensp->unlinkFrBack(), NodeVarRef);
            UASSERT_OBJ(senvarp, sensp, "Non-varref sensitivity variable");
            sensp->replaceWith(senvarp);
            VL_DO_DANGLING(sensp->deleteTree(), sensp);
        } else if (!m_doNConst  // Deal with later when doNConst missing
                   && (VN_IS(nodep->sensp(), EnumItemRef) || VN_IS(nodep->sensp(), Const))) {
        } else if (nodep->isIllegal()) {  // Deal with later
        } else {
            UASSERT_OBJ(!(nodep->hasVar() && !nodep->varrefp()), nodep,
                        "Null sensitivity variable");
        }
    }

    struct SenItemCmp {
        bool operator()(const AstSenItem* lhsp, const AstSenItem* rhsp) const {
            if (lhsp->type() < rhsp->type()) return true;
            if (lhsp->type() > rhsp->type()) return false;
            // Looks visually better if we keep sorted by name
            if (!lhsp->varrefp() && rhsp->varrefp()) return true;
            if (lhsp->varrefp() && !rhsp->varrefp()) return false;
            if (lhsp->varrefp() && rhsp->varrefp()) {
                if (lhsp->varrefp()->name() < rhsp->varrefp()->name()) return true;
                if (lhsp->varrefp()->name() > rhsp->varrefp()->name()) return false;
                // But might be same name with different scopes
                if (lhsp->varrefp()->varScopep() < rhsp->varrefp()->varScopep()) return true;
                if (lhsp->varrefp()->varScopep() > rhsp->varrefp()->varScopep()) return false;
                // Or rarely, different data types
                if (lhsp->varrefp()->dtypep() < rhsp->varrefp()->dtypep()) return true;
                if (lhsp->varrefp()->dtypep() > rhsp->varrefp()->dtypep()) return false;
            }
            // Sort by edge, AFTER variable, as we want multiple edges for same var adjacent.
            // note the SenTree optimizer requires this order (more
            // general first, less general last)
            if (lhsp->edgeType() < rhsp->edgeType()) return true;
            if (lhsp->edgeType() > rhsp->edgeType()) return false;
            return false;
        }
    };

    virtual void visit(AstSenTree* nodep) override {
        iterateChildren(nodep);
        if (m_doExpensive) {
            // cout<<endl; nodep->dumpTree(cout, "ssin: ");
            // Optimize ideas for the future:
            //   SENTREE(... SENGATE(x,a), SENGATE(SENITEM(x),b) ...)  => SENGATE(x,OR(a,b))

            //   SENTREE(... SENITEM(x),   SENGATE(SENITEM(x),*) ...)  => SENITEM(x)
            // Do we need the SENITEM's to be identical?  No because we're
            // ORing between them; we just need to ensure that the result is at
            // least as frequently activating.  So we simply
            // SENGATE(SENITEM(x)) -> SENITEM(x), then let it collapse with the
            // other SENITEM(x).
            {
                AstUser4InUse m_inuse4;
                // Mark x in SENITEM(x)
                for (AstSenItem* senp = VN_CAST(nodep->sensesp(), SenItem); senp;
                     senp = VN_CAST(senp->nextp(), SenItem)) {
                    if (senp->varrefp() && senp->varrefp()->varScopep()) {
                        senp->varrefp()->varScopep()->user4(1);
                    }
                }
            }

            // Sort the sensitivity names so "posedge a or b" and "posedge b or a" end up together.
            // Also, remove duplicate assignments, and fold POS&NEGs into ANYEDGEs
            // Make things a little faster; check first if we need a sort
            for (AstSenItem *nextp, *senp = VN_CAST(nodep->sensesp(), SenItem); senp;
                 senp = nextp) {
                nextp = VN_CAST(senp->nextp(), SenItem);
                // cppcheck-suppress unassignedVariable  // cppcheck bug
                SenItemCmp cmp;
                if (nextp && !cmp(senp, nextp)) {
                    // Something's out of order, sort it
                    senp = nullptr;
                    std::vector<AstSenItem*> vec;
                    for (AstSenItem* senp = VN_CAST(nodep->sensesp(), SenItem); senp;
                         senp = VN_CAST(senp->nextp(), SenItem)) {
                        vec.push_back(senp);
                    }
                    stable_sort(vec.begin(), vec.end(), SenItemCmp());
                    for (const auto& ip : vec) ip->unlinkFrBack();
                    for (const auto& ip : vec) nodep->addSensesp(ip);
                    break;
                }
            }

            // Pass2, remove dup edges
            for (AstSenItem *nextp, *senp = VN_CAST(nodep->sensesp(), SenItem); senp;
                 senp = nextp) {
                nextp = VN_CAST(senp->nextp(), SenItem);
                AstSenItem* const litemp = senp;
                AstSenItem* const ritemp = nextp;
                if (ritemp) {
                    if ((litemp->varrefp() && ritemp->varrefp()
                         && litemp->varrefp()->sameGateTree(ritemp->varrefp()))
                        || (!litemp->varrefp() && !ritemp->varrefp())) {
                        // We've sorted in the order ANY, BOTH, POS, NEG,
                        // so we don't need to try opposite orders
                        if ((litemp->edgeType()
                             == VEdgeType::ET_ANYEDGE)  // ANY  or {BOTH|POS|NEG} -> ANY
                            || (litemp->edgeType()
                                == VEdgeType::ET_BOTHEDGE)  // BOTH or {POS|NEG} -> BOTH
                            || (litemp->edgeType() == VEdgeType::ET_POSEDGE  // POS  or NEG -> BOTH
                                && ritemp->edgeType() == VEdgeType::ET_NEGEDGE)
                            || (litemp->edgeType() == ritemp->edgeType())  // Identical edges
                        ) {
                            // Fix edge of old node
                            if (litemp->edgeType() == VEdgeType::ET_POSEDGE
                                && ritemp->edgeType() == VEdgeType::ET_NEGEDGE)
                                litemp->edgeType(VEdgeType::ET_BOTHEDGE);
                            // Remove redundant node
                            VL_DO_DANGLING(ritemp->unlinkFrBack()->deleteTree(), ritemp);
                            VL_DANGLING(ritemp);
                            // Try to collapse again
                            nextp = litemp;
                        }
                    }
                }
            }
            // nodep->dumpTree(cout, "ssou: ");
        }
    }

    //-----
    // Zero elimination
    virtual void visit(AstNodeAssign* nodep) override {
        iterateChildren(nodep);
        if (m_doNConst && replaceNodeAssign(nodep)) return;
    }
    virtual void visit(AstAssignAlias* nodep) override {
        // Don't perform any optimizations, keep the alias around
    }
    virtual void visit(AstAssignVarScope* nodep) override {
        // Don't perform any optimizations, the node won't be linked yet
    }
    virtual void visit(AstAssignW* nodep) override {
        iterateChildren(nodep);
        if (m_doNConst && replaceNodeAssign(nodep)) return;
        AstNodeVarRef* varrefp = VN_CAST(
            nodep->lhsp(),
            VarRef);  // Not VarXRef, as different refs may set different values to each hierarchy
        if (m_wremove && !m_params && m_doNConst && m_modp && operandConst(nodep->rhsp())
            && !VN_CAST(nodep->rhsp(), Const)->num().isFourState()
            && varrefp  // Don't do messes with BITREFs/ARRAYREFs
            && !varrefp->varp()->valuep()  // Not already constified
            && !varrefp->varScopep()) {  // Not scoped (or each scope may have different initial
                                         // value)
            // ASSIGNW (VARREF, const) -> INITIAL ( ASSIGN (VARREF, const) )
            UINFO(4, "constAssignW " << nodep << endl);
            // Make a initial assignment
            AstNode* exprp = nodep->rhsp()->unlinkFrBack();
            varrefp->unlinkFrBack();
            AstInitial* newinitp = new AstInitial(
                nodep->fileline(), new AstAssign(nodep->fileline(), varrefp, exprp));
            m_modp->addStmtp(newinitp);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            // Set the initial value right in the variable so we can constant propagate
            AstNode* initvaluep = exprp->cloneTree(false);
            varrefp->varp()->valuep(initvaluep);
        }
    }

    virtual void visit(AstNodeIf* nodep) override {
        iterateChildren(nodep);
        if (m_doNConst) {
            if (const AstConst* constp = VN_CAST(nodep->condp(), Const)) {
                AstNode* keepp = nullptr;
                if (constp->isZero()) {
                    UINFO(4, "IF(0,{any},{x}) => {x}: " << nodep << endl);
                    keepp = nodep->elsesp();
                } else if (!m_doV || constp->isNeqZero()) {  // Might be X in Verilog
                    UINFO(4, "IF(!0,{x},{any}) => {x}: " << nodep << endl);
                    keepp = nodep->ifsp();
                } else {
                    UINFO(4, "IF condition is X, retaining: " << nodep << endl);
                    return;
                }
                if (keepp) {
                    keepp->unlinkFrBackWithNext();
                    nodep->replaceWith(keepp);
                } else {
                    nodep->unlinkFrBack();
                }
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
            } else if (!afterComment(nodep->ifsp()) && !afterComment(nodep->elsesp())) {
                // Empty block, remove it
                // Note if we support more C++ then there might be side
                // effects in the condition itself
                VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            } else if (!afterComment(nodep->ifsp())) {
                UINFO(4, "IF({x}) nullptr {...} => IF(NOT{x}}: " << nodep << endl);
                AstNode* condp = nodep->condp();
                AstNode* elsesp = nodep->elsesp();
                condp->unlinkFrBackWithNext();
                elsesp->unlinkFrBackWithNext();
                if (nodep->ifsp()) {  // Must have been comment
                    nodep->ifsp()->unlinkFrBackWithNext()->deleteTree();
                }
                nodep->condp(new AstLogNot(condp->fileline(),
                                           condp));  // LogNot, as C++ optimization also possible
                nodep->addIfsp(elsesp);
            } else if (((VN_IS(nodep->condp(), Not) && nodep->condp()->width() == 1)
                        || VN_IS(nodep->condp(), LogNot))
                       && nodep->ifsp() && nodep->elsesp()) {
                UINFO(4, "IF(NOT {x})  => IF(x) swapped if/else" << nodep << endl);
                AstNode* condp
                    = VN_CAST(nodep->condp(), NodeUniop)->lhsp()->unlinkFrBackWithNext();
                AstNode* ifsp = nodep->ifsp()->unlinkFrBackWithNext();
                AstNode* elsesp = nodep->elsesp()->unlinkFrBackWithNext();
                AstIf* ifp = new AstIf(nodep->fileline(), condp, elsesp, ifsp);
                ifp->branchPred(nodep->branchPred().invert());
                nodep->replaceWith(ifp);
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
            } else if (ifSameAssign(nodep)) {
                UINFO(
                    4,
                    "IF({a}) ASSIGN({b},{c}) else ASSIGN({b},{d}) => ASSIGN({b}, {a}?{c}:{d})\n");
                AstNodeAssign* ifp = VN_CAST(nodep->ifsp(), NodeAssign);
                AstNodeAssign* elsep = VN_CAST(nodep->elsesp(), NodeAssign);
                ifp->unlinkFrBack();
                AstNode* condp = nodep->condp()->unlinkFrBack();
                AstNode* truep = ifp->rhsp()->unlinkFrBack();
                AstNode* falsep = elsep->rhsp()->unlinkFrBack();
                ifp->rhsp(new AstCond(truep->fileline(), condp, truep, falsep));
                nodep->replaceWith(ifp);
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
            } else if (false  // Disabled, as vpm assertions are faster
                              // without due to short-circuiting
                       && operandIfIf(nodep)) {
                UINFO(9, "IF({a}) IF({b}) => IF({a} && {b})" << endl);
                AstNodeIf* lowerIfp = VN_CAST(nodep->ifsp(), NodeIf);
                AstNode* condp = nodep->condp()->unlinkFrBack();
                AstNode* lowerIfsp = lowerIfp->ifsp()->unlinkFrBackWithNext();
                AstNode* lowerCondp = lowerIfp->condp()->unlinkFrBackWithNext();
                nodep->condp(new AstLogAnd(lowerIfp->fileline(), condp, lowerCondp));
                lowerIfp->replaceWith(lowerIfsp);
                VL_DO_DANGLING(lowerIfp->deleteTree(), lowerIfp);
            } else if (operandBoolShift(nodep->condp())) {
                replaceBoolShift(nodep->condp());
            }
        }
    }

    virtual void visit(AstDisplay* nodep) override {
        // DISPLAY(SFORMAT(text1)),DISPLAY(SFORMAT(text2)) -> DISPLAY(SFORMAT(text1+text2))
        iterateChildren(nodep);
        if (stmtDisplayDisplay(nodep)) return;
    }
    bool stmtDisplayDisplay(AstDisplay* nodep) {
        // DISPLAY(SFORMAT(text1)),DISPLAY(SFORMAT(text2)) -> DISPLAY(SFORMAT(text1+text2))
        if (!m_modp) return false;  // Don't optimize under single statement
        AstDisplay* prevp = VN_CAST(nodep->backp(), Display);
        if (!prevp) return false;
        if (!((prevp->displayType() == nodep->displayType())
              || (prevp->displayType() == AstDisplayType::DT_WRITE
                  && nodep->displayType() == AstDisplayType::DT_DISPLAY)
              || (prevp->displayType() == AstDisplayType::DT_DISPLAY
                  && nodep->displayType() == AstDisplayType::DT_WRITE)))
            return false;
        if ((prevp->filep() && !nodep->filep()) || (!prevp->filep() && nodep->filep())
            || !prevp->filep()->sameTree(nodep->filep()))
            return false;
        if (!prevp->fmtp() || prevp->fmtp()->nextp() || !nodep->fmtp() || nodep->fmtp()->nextp())
            return false;
        AstSFormatF* pformatp = prevp->fmtp();
        if (!pformatp) return false;
        AstSFormatF* nformatp = nodep->fmtp();
        if (!nformatp) return false;
        // We don't merge scopeNames as can have only one and might be different scopes (late in
        // process) Also rare for real code to print %m multiple times in same message
        if (nformatp->scopeNamep() && pformatp->scopeNamep()) return false;
        // We don't early merge arguments as might need to later print warnings with
        // right line numbers, nor scopeNames as might be different scopes (late in process)
        if (!m_doCpp && pformatp->exprsp()) return false;
        if (!m_doCpp && nformatp->exprsp()) return false;
        // Avoid huge merges
        static constexpr int DISPLAY_MAX_MERGE_LENGTH = 500;
        if (pformatp->text().length() + nformatp->text().length() > DISPLAY_MAX_MERGE_LENGTH)
            return false;
        //
        UINFO(9, "DISPLAY(SF({a})) DISPLAY(SF({b})) -> DISPLAY(SF({a}+{b}))" << endl);
        // Convert DT_DISPLAY to DT_WRITE as may allow later optimizations
        if (prevp->displayType() == AstDisplayType::DT_DISPLAY) {
            prevp->displayType(AstDisplayType::DT_WRITE);
            pformatp->text(pformatp->text() + "\n");
        }
        // We can't replace prev() as the edit tracking iterators will get confused.
        // So instead we edit the prev note itself.
        if (prevp->addNewline()) pformatp->text(pformatp->text() + "\n");
        pformatp->text(pformatp->text() + nformatp->text());
        if (!prevp->addNewline() && nodep->addNewline()) pformatp->text(pformatp->text() + "\n");
        if (nformatp->exprsp()) pformatp->addExprsp(nformatp->exprsp()->unlinkFrBackWithNext());
        if (nformatp->scopeNamep())
            pformatp->scopeNamep(nformatp->scopeNamep()->unlinkFrBackWithNext());
        VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        return true;
    }
    virtual void visit(AstSFormatF* nodep) override {
        // Substitute constants into displays.  The main point of this is to
        // simplify assertion methodologies which call functions with display's.
        // This eliminates a pile of wide temps, and makes the C a whole lot more readable.
        iterateChildren(nodep);
        bool anyconst = false;
        for (AstNode* argp = nodep->exprsp(); argp; argp = argp->nextp()) {
            if (VN_IS(argp, Const)) {
                anyconst = true;
                break;
            }
        }
        if (m_doNConst && anyconst) {
            // UINFO(9,"  Display in  "<<nodep->text()<<endl);
            string newFormat;
            string fmt;
            bool inPct = false;
            AstNode* argp = nodep->exprsp();
            string text = nodep->text();
            for (const char ch : text) {
                if (!inPct && ch == '%') {
                    inPct = true;
                    fmt = ch;
                } else if (inPct && (isdigit(ch) || ch == '.' || ch == '-')) {
                    fmt += ch;
                } else if (inPct) {
                    inPct = false;
                    fmt += ch;
                    switch (tolower(ch)) {
                    case '%': break;  // %% - just output a %
                    case 'm': break;  // %m - auto insert "name"
                    case 'l': break;  // %l - auto insert "library"
                    case 't':  // FALLTHRU
                    case '^':  // %t/%^ - don't know $timeformat so can't constify
                        if (argp) argp = argp->nextp();
                        break;
                    default:  // Most operators, just move to next argument
                        if (argp) {
                            AstNode* nextp = argp->nextp();
                            if (VN_IS(argp, Const)) {  // Convert it
                                string out = VN_CAST(argp, Const)->num().displayed(nodep, fmt);
                                UINFO(9, "     DispConst: " << fmt << " -> " << out << "  for "
                                                            << argp << endl);
                                // fmt = out w/ replace % with %% as it must be literal.
                                fmt = VString::quotePercent(out);
                                VL_DO_DANGLING(argp->unlinkFrBack()->deleteTree(), argp);
                            }
                            argp = nextp;
                        }
                        break;
                    }  // switch
                    newFormat += fmt;
                } else {
                    newFormat += ch;
                }
            }
            if (newFormat != nodep->text()) {
                nodep->text(newFormat);
                UINFO(9, "  Display out " << nodep << endl);
            }
        }
        if (!nodep->exprsp() && nodep->name().find('%') == string::npos && !nodep->hidden()) {
            // Just a simple constant string - the formatting is pointless
            VL_DO_DANGLING(replaceConstString(nodep, nodep->name()), nodep);
        }
    }

    virtual void visit(AstFuncRef* nodep) override {
        iterateChildren(nodep);
        if (m_params) {  // Only parameters force us to do constant function call propagation
            replaceWithSimulation(nodep);
        }
    }
    virtual void visit(AstArg* nodep) override {
        // replaceWithSimulation on the Arg's parent FuncRef replaces these
        iterateChildren(nodep);
    }
    virtual void visit(AstWhile* nodep) override {
        bool oldHasJumpDelay = m_hasJumpDelay;
        m_hasJumpDelay = false;
        { iterateChildren(nodep); }
        bool thisWhileHasJumpDelay = m_hasJumpDelay;
        m_hasJumpDelay = thisWhileHasJumpDelay || oldHasJumpDelay;
        if (m_doNConst) {
            if (nodep->condp()->isZero()) {
                UINFO(4, "WHILE(0) => nop " << nodep << endl);
                if (nodep->precondsp()) {
                    nodep->replaceWith(nodep->precondsp());
                } else {
                    nodep->unlinkFrBack();
                }
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
            } else if (nodep->condp()->isNeqZero()) {
                if (!thisWhileHasJumpDelay) {
                    nodep->v3warn(INFINITELOOP, "Infinite loop (condition always true)");
                    nodep->fileline()->modifyWarnOff(V3ErrorCode::INFINITELOOP,
                                                     true);  // Complain just once
                }
            } else if (operandBoolShift(nodep->condp())) {
                replaceBoolShift(nodep->condp());
            }
        }
    }
    virtual void visit(AstInitArray* nodep) override { iterateChildren(nodep); }
    virtual void visit(AstInitItem* nodep) override { iterateChildren(nodep); }
    virtual void visit(AstUnbounded* nodep) override { iterateChildren(nodep); }
    // These are converted by V3Param.  Don't constify as we don't want the
    // from() VARREF to disappear, if any.
    // If output of a presel didn't get consted, chances are V3Param didn't visit properly
    virtual void visit(AstNodePreSel*) override {}

    // Ignored, can eliminate early
    virtual void visit(AstSysIgnore* nodep) override {
        iterateChildren(nodep);
        if (m_doNConst) VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
    }

    // Simplify
    virtual void visit(AstBasicDType* nodep) override {
        iterateChildren(nodep);
        nodep->cvtRangeConst();
    }

    //-----
    // Jump elimination

    virtual void visit(AstDelay* nodep) override {
        iterateChildren(nodep);
        m_hasJumpDelay = true;
    }
    virtual void visit(AstJumpGo* nodep) override {
        iterateChildren(nodep);
        // Jump to label where label immediately follows label is not useful
        if (nodep->labelp() == VN_CAST(nodep->nextp(), JumpLabel)) {
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            // Keep the label, might be other jumps pointing to it, gets cleaned later
            return;
        }
        if (m_doExpensive) {
            // Any non-label statements (at this statement level) can never execute
            while (nodep->nextp() && !VN_IS(nodep->nextp(), JumpLabel)) {
                nodep->nextp()->unlinkFrBack()->deleteTree();
            }
            // If last statement in a jump label we have JumpLabel(...., JumpGo)
            // Often caused by "return" in a Verilog function.  The Go is pointless, remove.
            if (!nodep->nextp()) {
                if (AstJumpBlock* aboveBlockp = VN_CAST(nodep->abovep(), JumpBlock)) {
                    if (aboveBlockp == nodep->labelp()->blockp()) {
                        if (aboveBlockp->endStmtsp() == nodep->labelp()) {
                            UINFO(4, "JUMPGO => last remove " << nodep << endl);
                            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
                            return;
                        }
                    }
                }
            }
            nodep->labelp()->blockp()->user4(true);
        }
        m_hasJumpDelay = true;
    }

    virtual void visit(AstJumpBlock* nodep) override {
        // Because JumpLabels disable many optimizations,
        // remove JumpLabels that are not pointed to by any AstJumpGos
        // Note this assumes all AstJumpGos are underneath the given label; V3Broken asserts this
        iterateChildren(nodep);
        // AstJumpGo's below here that point to this node will set user4
        if (m_doExpensive && !nodep->user4()) {
            UINFO(4, "JUMPLABEL => unused " << nodep << endl);
            AstNode* underp = nullptr;
            if (nodep->stmtsp()) underp = nodep->stmtsp()->unlinkFrBackWithNext();
            if (underp) {
                nodep->replaceWith(underp);
            } else {
                nodep->unlinkFrBack();
            }
            nodep->labelp()->unlinkFrBack()->deleteTree();
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }

    //-----
    // Below lines are magic expressions processed by astgen
    //  TREE_SKIP_VISIT("AstNODETYPE")    # Rename normal visit to visitGen and don't iterate
    //-----
    // clang-format off
    TREE_SKIP_VISIT("ArraySel");

    //-----
    //  "AstNODETYPE {             # bracket not paren
    //                $accessor_name, ...
    //                             # .castFoo is the test VN_IS(object,Foo)
    //                             # ,, gets replaced with a , rather than &&
    //               }"            # bracket not paren
    //    ,"what to call"
    //
    // Where "what_to_call" is:
    //          "function to call"
    //          "AstREPLACEMENT_TYPE{ $accessor }"
    //          "!              # Print line number when matches, so can see operations
    //          "NEVER"         # Print error message
    //          "DONE"          # Process of matching did the transform already

    // In the future maybe support more complicated match & replace:
    //   ("AstOr  {%a, AstAnd{AstNot{%b}, %c}} if %a.width1 if %a==%b", "AstOr{%a,%c}; %b.delete");
    // Lhs/rhs would be implied; for non math operations you'd need $lhsp etc.

    //    v--- * * This op done on Verilog or C+++ mode, in all non-m_doConst stages
    //    v--- *1* These ops are always first, as we warn before replacing
    //    v--- *C* This op is a (C)++ op, only in m_doCpp mode
    //    v--- *V* This op is a (V)erilog op, only in m_doV mode
    //    v--- *A* This op works on (A)ll constant children, allowed in m_doConst mode
    //    v--- *S* This op specifies a type should use (S)hort-circuiting of its lhs op

    TREEOP1("AstSel{warnSelect(nodep)}",        "NEVER");
    // Generic constants on both side.  Do this first to avoid other replacements
    TREEOPA("AstNodeBiop {$lhsp.castConst, $rhsp.castConst, nodep->isPredictOptimizable()}",  "replaceConst(nodep)");
    TREEOPA("AstNodeUniop{$lhsp.castConst, !nodep->isOpaque(), nodep->isPredictOptimizable()}",  "replaceConst(nodep)");
    TREEOPA("AstNodeQuadop{$lhsp.castConst, $rhsp.castConst, $thsp.castConst, $fhsp.castConst}",  "replaceConst(nodep)");
    // Zero on one side or the other
    TREEOP ("AstAdd   {$lhsp.isZero, $rhsp}",   "replaceWRhs(nodep)");
    TREEOP ("AstAnd   {$lhsp.isZero, $rhsp, isTPure($rhsp)}",   "replaceZero(nodep)");  // Can't use replaceZeroChkPure as we make this pattern in ChkPure
    // This visit function here must allow for short-circuiting.
    TREEOPS("AstLogAnd   {$lhsp.isZero}",       "replaceZero(nodep)");
    TREEOP ("AstLogAnd{$lhsp.isZero, $rhsp}",   "replaceZero(nodep)");
    // This visit function here must allow for short-circuiting.
    TREEOPS("AstLogOr   {$lhsp.isOne}",         "replaceNum(nodep, 1)");
    TREEOP ("AstLogOr {$lhsp.isZero, $rhsp}",   "replaceWRhs(nodep)");
    TREEOP ("AstDiv   {$lhsp.isZero, $rhsp}",   "replaceZeroChkPure(nodep,$rhsp)");
    TREEOP ("AstDivS  {$lhsp.isZero, $rhsp}",   "replaceZeroChkPure(nodep,$rhsp)");
    TREEOP ("AstMul   {$lhsp.isZero, $rhsp}",   "replaceZeroChkPure(nodep,$rhsp)");
    TREEOP ("AstMulS  {$lhsp.isZero, $rhsp}",   "replaceZeroChkPure(nodep,$rhsp)");
    TREEOP ("AstPow   {$rhsp.isZero}",          "replaceNum(nodep, 1)");  // Overrides lhs zero rule
    TREEOP ("AstPowSS {$rhsp.isZero}",          "replaceNum(nodep, 1)");  // Overrides lhs zero rule
    TREEOP ("AstPowSU {$rhsp.isZero}",          "replaceNum(nodep, 1)");  // Overrides lhs zero rule
    TREEOP ("AstPowUS {$rhsp.isZero}",          "replaceNum(nodep, 1)");  // Overrides lhs zero rule
    TREEOP ("AstPow   {$lhsp.isZero, !$rhsp.isZero}",   "replaceZeroChkPure(nodep,$rhsp)");
    TREEOP ("AstPowSU {$lhsp.isZero, !$rhsp.isZero}",   "replaceZeroChkPure(nodep,$rhsp)");
    TREEOP ("AstPowUS {$lhsp.isZero, !$rhsp.isZero}",   "replaceZeroChkPure(nodep,$rhsp)");
    TREEOP ("AstPowSU {$lhsp.isZero, !$rhsp.isZero}",   "replaceZeroChkPure(nodep,$rhsp)");
    TREEOP ("AstOr    {$lhsp.isZero, $rhsp}",   "replaceWRhs(nodep)");
    TREEOP ("AstShiftL{$lhsp.isZero, $rhsp}",   "replaceZeroChkPure(nodep,$rhsp)");
    TREEOP ("AstShiftR{$lhsp.isZero, $rhsp}",   "replaceZeroChkPure(nodep,$rhsp)");
    TREEOP ("AstShiftRS{$lhsp.isZero, $rhsp}",  "replaceZeroChkPure(nodep,$rhsp)");
    TREEOP ("AstXor   {$lhsp.isZero, $rhsp}",   "replaceWRhs(nodep)");
    TREEOP ("AstSub   {$lhsp.isZero, $rhsp}",   "AstNegate{$rhsp}");
    TREEOP ("AstAdd   {$lhsp, $rhsp.isZero}",   "replaceWLhs(nodep)");
    TREEOP ("AstAnd   {$lhsp, $rhsp.isZero}",   "replaceZeroChkPure(nodep,$lhsp)");
    TREEOP ("AstLogAnd{$lhsp, $rhsp.isZero}",   "replaceZeroChkPure(nodep,$lhsp)");
    TREEOP ("AstLogOr {$lhsp, $rhsp.isZero}",   "replaceWLhs(nodep)");
    TREEOP ("AstMul   {$lhsp, $rhsp.isZero}",   "replaceZeroChkPure(nodep,$lhsp)");
    TREEOP ("AstMulS  {$lhsp, $rhsp.isZero}",   "replaceZeroChkPure(nodep,$lhsp)");
    TREEOP ("AstOr    {$lhsp, $rhsp.isZero}",   "replaceWLhs(nodep)");
    TREEOP ("AstShiftL{$lhsp, $rhsp.isZero}",   "replaceWLhs(nodep)");
    TREEOP ("AstShiftR{$lhsp, $rhsp.isZero}",   "replaceWLhs(nodep)");
    TREEOP ("AstShiftRS{$lhsp, $rhsp.isZero}",  "replaceWLhs(nodep)");
    TREEOP ("AstSub   {$lhsp, $rhsp.isZero}",   "replaceWLhs(nodep)");
    TREEOP ("AstXor   {$lhsp, $rhsp.isZero}",   "replaceWLhs(nodep)");
    // Non-zero on one side or the other
    TREEOP ("AstAnd   {$lhsp.isAllOnes, $rhsp}",        "replaceWRhs(nodep)");
    TREEOP ("AstLogAnd{$lhsp.isNeqZero, $rhsp}",        "replaceWRhs(nodep)");
    TREEOP ("AstOr    {$lhsp.isAllOnes, $rhsp, isTPure($rhsp)}",        "replaceWLhs(nodep)");  //->allOnes
    TREEOP ("AstLogOr {$lhsp.isNeqZero, $rhsp}",        "replaceNum(nodep,1)");
    TREEOP ("AstAnd   {$lhsp, $rhsp.isAllOnes}",        "replaceWLhs(nodep)");
    TREEOP ("AstLogAnd{$lhsp, $rhsp.isNeqZero}",        "replaceWLhs(nodep)");
    TREEOP ("AstOr    {$lhsp, $rhsp.isAllOnes, isTPure($lhsp)}",        "replaceWRhs(nodep)");  //->allOnes
    TREEOP ("AstLogOr {$lhsp, $rhsp.isNeqZero, isTPure($lhsp)}",        "replaceNum(nodep,1)");
    TREEOP ("AstXor   {$lhsp.isAllOnes, $rhsp}",        "AstNot{$rhsp}");
    TREEOP ("AstMul   {$lhsp.isOne, $rhsp}",    "replaceWRhs(nodep)");
    TREEOP ("AstMulS  {$lhsp.isOne, $rhsp}",    "replaceWRhs(nodep)");
    TREEOP ("AstDiv   {$lhsp, $rhsp.isOne}",    "replaceWLhs(nodep)");
    TREEOP ("AstDivS  {$lhsp, $rhsp.isOne}",    "replaceWLhs(nodep)");
    TREEOP ("AstMul   {operandIsPowTwo($lhsp), operandsSameSize($lhsp,,$rhsp)}", "replaceMulShift(nodep)");  // a*2^n -> a<<n
    TREEOP ("AstDiv   {$lhsp, operandIsPowTwo($rhsp)}", "replaceDivShift(nodep)");  // a/2^n -> a>>n
    TREEOP ("AstModDiv{$lhsp, operandIsPowTwo($rhsp)}", "replaceModAnd(nodep)");  // a % 2^n -> a&(2^n-1)
    TREEOP ("AstPow   {operandIsTwo($lhsp), $rhsp}",    "replacePowShift(nodep)");  // 2**a == 1<<a
    TREEOP ("AstSub   {$lhsp.castAdd, operandSubAdd(nodep)}", "AstAdd{AstSub{$lhsp->castAdd()->lhsp(),$rhsp}, $lhsp->castAdd()->rhsp()}");  // ((a+x)-y) -> (a+(x-y))
    TREEOPC("AstAnd   {$lhsp.isOne, matchRedundantClean(nodep)}", "DONE")  // 1 & (a == b) -> (IData)(a == b)
    // Trinary ops
    // Note V3Case::Sel requires Cond to always be conditionally executed in C to prevent core dump!
    TREEOP ("AstNodeCond{$condp.isZero,       $expr1p, $expr2p}", "replaceWChild(nodep,$expr2p)");
    TREEOP ("AstNodeCond{$condp.isNeqZero,    $expr1p, $expr2p}", "replaceWChild(nodep,$expr1p)");
    TREEOPA("AstNodeCond{$condp.isZero,       $expr1p.castConst, $expr2p.castConst}", "replaceWChild(nodep,$expr2p)");
    TREEOPA("AstNodeCond{$condp.isNeqZero,    $expr1p.castConst, $expr2p.castConst}", "replaceWChild(nodep,$expr1p)");
    TREEOP ("AstNodeCond{$condp, operandsSame($expr1p,,$expr2p)}","replaceWChild(nodep,$expr1p)");
    // This visit function here must allow for short-circuiting.
    TREEOPS("AstCond {$lhsp.isZero}",           "replaceWIteratedThs(nodep)");
    TREEOPS("AstCond {$lhsp.isNeqZero}",        "replaceWIteratedRhs(nodep)");
    TREEOP ("AstCond{$condp.castNot,       $expr1p, $expr2p}", "AstCond{$condp->op1p(), $expr2p, $expr1p}");
    TREEOP ("AstNodeCond{$condp.width1, $expr1p.width1,   $expr1p.isAllOnes, $expr2p}", "AstLogOr {$condp, $expr2p}");  // a?1:b == a||b
    TREEOP ("AstNodeCond{$condp.width1, $expr1p.width1,   $expr1p,    $expr2p.isZero}", "AstLogAnd{$condp, $expr1p}");  // a?b:0 == a&&b
    TREEOP ("AstNodeCond{$condp.width1, $expr1p.width1,   $expr1p, $expr2p.isAllOnes}", "AstLogOr {AstNot{$condp}, $expr1p}");  // a?b:1 == ~a||b
    TREEOP ("AstNodeCond{$condp.width1, $expr1p.width1,   $expr1p.isZero,    $expr2p}", "AstLogAnd{AstNot{$condp}, $expr2p}");  // a?0:b == ~a&&b
    TREEOP ("AstNodeCond{!$condp.width1, operandBoolShift(nodep->condp())}", "replaceBoolShift(nodep->condp())");
    // Prefer constants on left, since that often needs a shift, it lets
    // constant red remove the shift
    TREEOP ("AstNodeBiCom{!$lhsp.castConst, $rhsp.castConst}",  "swapSides(nodep)");
    TREEOP ("AstNodeBiComAsv{operandAsvConst(nodep)}",  "replaceAsv(nodep)");
    TREEOP ("AstNodeBiComAsv{operandAsvSame(nodep)}",   "replaceAsv(nodep)");
    TREEOP ("AstNodeBiComAsv{operandAsvLUp(nodep)}",    "replaceAsvLUp(nodep)");
    TREEOP ("AstNodeBiComAsv{operandAsvRUp(nodep)}",    "replaceAsvRUp(nodep)");
    TREEOP ("AstLt   {!$lhsp.castConst,$rhsp.castConst}",       "AstGt  {$rhsp,$lhsp}");
    TREEOP ("AstLtS  {!$lhsp.castConst,$rhsp.castConst}",       "AstGtS {$rhsp,$lhsp}");
    TREEOP ("AstLte  {!$lhsp.castConst,$rhsp.castConst}",       "AstGte {$rhsp,$lhsp}");
    TREEOP ("AstLteS {!$lhsp.castConst,$rhsp.castConst}",       "AstGteS{$rhsp,$lhsp}");
    TREEOP ("AstGt   {!$lhsp.castConst,$rhsp.castConst}",       "AstLt  {$rhsp,$lhsp}");
    TREEOP ("AstGtS  {!$lhsp.castConst,$rhsp.castConst}",       "AstLtS {$rhsp,$lhsp}");
    TREEOP ("AstGte  {!$lhsp.castConst,$rhsp.castConst}",       "AstLte {$rhsp,$lhsp}");
    TREEOP ("AstGteS {!$lhsp.castConst,$rhsp.castConst}",       "AstLteS{$rhsp,$lhsp}");
    //    v--- *1* as These ops are always first, as we warn before replacing
    TREEOP1("AstLt   {$lhsp, $rhsp.isZero}",            "replaceNumSigned(nodep,0)");
    TREEOP1("AstGte  {$lhsp, $rhsp.isZero}",            "replaceNumSigned(nodep,1)");
    TREEOP1("AstGt   {$lhsp.isZero, $rhsp}",            "replaceNumSigned(nodep,0)");
    TREEOP1("AstLte  {$lhsp.isZero, $rhsp}",            "replaceNumSigned(nodep,1)");
    TREEOP1("AstGt   {$lhsp, $rhsp.isAllOnes, $lhsp->width()==$rhsp->width()}",  "replaceNumLimited(nodep,0)");
    TREEOP1("AstLte  {$lhsp, $rhsp.isAllOnes, $lhsp->width()==$rhsp->width()}",  "replaceNumLimited(nodep,1)");
    TREEOP1("AstLt   {$lhsp.isAllOnes, $rhsp, $lhsp->width()==$rhsp->width()}",  "replaceNumLimited(nodep,0)");
    TREEOP1("AstGte  {$lhsp.isAllOnes, $rhsp, $lhsp->width()==$rhsp->width()}",  "replaceNumLimited(nodep,1)");
    // Two level bubble pushing
    TREEOP ("AstNot   {$lhsp.castNot,  $lhsp->width()==VN_CAST($lhsp,,Not)->lhsp()->width()}", "replaceWChild(nodep, $lhsp->op1p())");  // NOT(NOT(x))->x
    TREEOP ("AstLogNot{$lhsp.castLogNot}",              "replaceWChild(nodep, $lhsp->op1p())");  // LOGNOT(LOGNOT(x))->x
    TREEOPV("AstNot   {$lhsp.castEqCase, $lhsp.width1}","AstNeqCase{$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castEqCase}",              "AstNeqCase{$lhsp->op1p(),$lhsp->op2p()}");
    TREEOPV("AstNot   {$lhsp.castNeqCase, $lhsp.width1}","AstEqCase {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castNeqCase}",             "AstEqCase {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOPV("AstNot   {$lhsp.castEqWild, $lhsp.width1}","AstNeqWild{$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castEqWild}",              "AstNeqWild{$lhsp->op1p(),$lhsp->op2p()}");
    TREEOPV("AstNot   {$lhsp.castNeqWild, $lhsp.width1}","AstEqWild {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castNeqWild}",             "AstEqWild {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOPV("AstNot   {$lhsp.castEq, $lhsp.width1}",    "AstNeq {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castEq}",                  "AstNeq {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOPV("AstNot   {$lhsp.castNeq, $lhsp.width1}",   "AstEq  {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castNeq}",                 "AstEq  {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOPV("AstNot   {$lhsp.castLt, $lhsp.width1}",    "AstGte {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castLt}",                  "AstGte {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOPV("AstNot   {$lhsp.castLtS, $lhsp.width1}",   "AstGteS{$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castLtS}",                 "AstGteS{$lhsp->op1p(),$lhsp->op2p()}");
    TREEOPV("AstNot   {$lhsp.castLte, $lhsp.width1}",   "AstGt  {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castLte}",                 "AstGt  {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOPV("AstNot   {$lhsp.castLteS, $lhsp.width1}",  "AstGtS {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castLteS}",                "AstGtS {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOPV("AstNot   {$lhsp.castGt, $lhsp.width1}",    "AstLte {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castGt}",                  "AstLte {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOPV("AstNot   {$lhsp.castGtS, $lhsp.width1}",   "AstLteS{$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castGtS}",                 "AstLteS{$lhsp->op1p(),$lhsp->op2p()}");
    TREEOPV("AstNot   {$lhsp.castGte, $lhsp.width1}",   "AstLt  {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castGte}",                 "AstLt  {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOPV("AstNot   {$lhsp.castGteS, $lhsp.width1}",  "AstLtS {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castGteS}",                "AstLtS {$lhsp->op1p(),$lhsp->op2p()}");
    // Not common, but avoids compiler warnings about over shifting
    TREEOP ("AstShiftL{operandHugeShiftL(nodep)}",      "replaceZero(nodep)");
    TREEOP ("AstShiftR{operandHugeShiftR(nodep)}",      "replaceZero(nodep)");
    TREEOP ("AstShiftL{operandShiftOp(nodep)}",         "replaceShiftOp(nodep)");
    TREEOP ("AstShiftR{operandShiftOp(nodep)}",         "replaceShiftOp(nodep)");
    TREEOP ("AstShiftL{operandShiftShift(nodep)}",      "replaceShiftShift(nodep)");
    TREEOP ("AstShiftR{operandShiftShift(nodep)}",      "replaceShiftShift(nodep)");
    TREEOP ("AstWordSel{operandWordOOB(nodep)}",        "replaceZero(nodep)");
    // Compress out EXTENDs to appease loop unroller
    TREEOPV("AstEq    {$rhsp.castExtend,operandBiExtendConstShrink(nodep)}",    "DONE");
    TREEOPV("AstNeq   {$rhsp.castExtend,operandBiExtendConstShrink(nodep)}",    "DONE");
    TREEOPV("AstGt    {$rhsp.castExtend,operandBiExtendConstShrink(nodep)}",    "DONE");
    TREEOPV("AstGte   {$rhsp.castExtend,operandBiExtendConstShrink(nodep)}",    "DONE");
    TREEOPV("AstLt    {$rhsp.castExtend,operandBiExtendConstShrink(nodep)}",    "DONE");
    TREEOPV("AstLte   {$rhsp.castExtend,operandBiExtendConstShrink(nodep)}",    "DONE");
    TREEOPV("AstEq    {$rhsp.castExtend,operandBiExtendConstOver(nodep)}",      "replaceZero(nodep)");
    TREEOPV("AstNeq   {$rhsp.castExtend,operandBiExtendConstOver(nodep)}",      "replaceNum(nodep,1)");
    TREEOPV("AstGt    {$rhsp.castExtend,operandBiExtendConstOver(nodep)}",      "replaceNum(nodep,1)");
    TREEOPV("AstGte   {$rhsp.castExtend,operandBiExtendConstOver(nodep)}",      "replaceNum(nodep,1)");
    TREEOPV("AstLt    {$rhsp.castExtend,operandBiExtendConstOver(nodep)}",      "replaceZero(nodep)");
    TREEOPV("AstLte   {$rhsp.castExtend,operandBiExtendConstOver(nodep)}",      "replaceZero(nodep)");
    // Identical operands on both sides
    // AstLogAnd/AstLogOr already converted to AstAnd/AstOr for these rules
    // AstAdd->ShiftL(#,1) but uncommon
    TREEOP ("AstAnd    {operandsSame($lhsp,,$rhsp)}",   "replaceWLhs(nodep)");
    TREEOP ("AstChangeXor{operandsSame($lhsp,,$rhsp)}", "replaceZero(nodep)");
    TREEOP ("AstDiv    {operandsSame($lhsp,,$rhsp)}",   "replaceNum(nodep,1)");
    TREEOP ("AstDivS   {operandsSame($lhsp,,$rhsp)}",   "replaceNum(nodep,1)");
    TREEOP ("AstOr     {operandsSame($lhsp,,$rhsp)}",   "replaceWLhs(nodep)");
    TREEOP ("AstSub    {operandsSame($lhsp,,$rhsp)}",   "replaceZero(nodep)");
    TREEOP ("AstXor    {operandsSame($lhsp,,$rhsp)}",   "replaceZero(nodep)");
    TREEOP ("AstEq     {operandsSame($lhsp,,$rhsp)}",   "replaceNum(nodep,1)");  // We let X==X -> 1, although in a true 4-state sim it's X.
    TREEOP ("AstEqD    {operandsSame($lhsp,,$rhsp)}",   "replaceNum(nodep,1)");  // We let X==X -> 1, although in a true 4-state sim it's X.
    TREEOP ("AstEqN    {operandsSame($lhsp,,$rhsp)}",   "replaceNum(nodep,1)");  // We let X==X -> 1, although in a true 4-state sim it's X.
    TREEOP ("AstEqCase {operandsSame($lhsp,,$rhsp)}",   "replaceNum(nodep,1)");
    TREEOP ("AstEqWild {operandsSame($lhsp,,$rhsp)}",   "replaceNum(nodep,1)");
    TREEOP ("AstGt     {operandsSame($lhsp,,$rhsp)}",   "replaceZero(nodep)");
    TREEOP ("AstGtD    {operandsSame($lhsp,,$rhsp)}",   "replaceZero(nodep)");
    TREEOP ("AstGtN    {operandsSame($lhsp,,$rhsp)}",   "replaceZero(nodep)");
    TREEOP ("AstGtS    {operandsSame($lhsp,,$rhsp)}",   "replaceZero(nodep)");
    TREEOP ("AstGte    {operandsSame($lhsp,,$rhsp)}",   "replaceNum(nodep,1)");
    TREEOP ("AstGteD   {operandsSame($lhsp,,$rhsp)}",   "replaceNum(nodep,1)");
    TREEOP ("AstGteN   {operandsSame($lhsp,,$rhsp)}",   "replaceNum(nodep,1)");
    TREEOP ("AstGteS   {operandsSame($lhsp,,$rhsp)}",   "replaceNum(nodep,1)");
    TREEOP ("AstLt     {operandsSame($lhsp,,$rhsp)}",   "replaceZero(nodep)");
    TREEOP ("AstLtD    {operandsSame($lhsp,,$rhsp)}",   "replaceZero(nodep)");
    TREEOP ("AstLtN    {operandsSame($lhsp,,$rhsp)}",   "replaceZero(nodep)");
    TREEOP ("AstLtS    {operandsSame($lhsp,,$rhsp)}",   "replaceZero(nodep)");
    TREEOP ("AstLte    {operandsSame($lhsp,,$rhsp)}",   "replaceNum(nodep,1)");
    TREEOP ("AstLteD   {operandsSame($lhsp,,$rhsp)}",   "replaceNum(nodep,1)");
    TREEOP ("AstLteN   {operandsSame($lhsp,,$rhsp)}",   "replaceNum(nodep,1)");
    TREEOP ("AstLteS   {operandsSame($lhsp,,$rhsp)}",   "replaceNum(nodep,1)");
    TREEOP ("AstNeq    {operandsSame($lhsp,,$rhsp)}",   "replaceZero(nodep)");
    TREEOP ("AstNeqD   {operandsSame($lhsp,,$rhsp)}",   "replaceZero(nodep)");
    TREEOP ("AstNeqN   {operandsSame($lhsp,,$rhsp)}",   "replaceZero(nodep)");
    TREEOP ("AstNeqCase{operandsSame($lhsp,,$rhsp)}",   "replaceZero(nodep)");
    TREEOP ("AstNeqWild{operandsSame($lhsp,,$rhsp)}",   "replaceZero(nodep)");
    TREEOP ("AstLogAnd {operandsSame($lhsp,,$rhsp), $lhsp.width1}",     "replaceWLhs(nodep)");
    TREEOP ("AstLogOr  {operandsSame($lhsp,,$rhsp), $lhsp.width1}",     "replaceWLhs(nodep)");
    ///=== Verilog operators
    // Comparison against 1'b0/1'b1; must be careful about widths.
    // These use Not, so must be Verilog only
    TREEOPV("AstEq    {$rhsp.width1, $lhsp.isZero,    $rhsp}",  "AstNot{$rhsp}");
    TREEOPV("AstEq    {$lhsp.width1, $lhsp, $rhsp.isZero}",     "AstNot{$lhsp}");
    TREEOPV("AstEq    {$rhsp.width1, $lhsp.isAllOnes, $rhsp}",  "replaceWRhs(nodep)");
    TREEOPV("AstEq    {$lhsp.width1, $lhsp, $rhsp.isAllOnes}",  "replaceWLhs(nodep)");
    TREEOPV("AstNeq   {$rhsp.width1, $lhsp.isZero,    $rhsp}",  "replaceWRhs(nodep)");
    TREEOPV("AstNeq   {$lhsp.width1, $lhsp, $rhsp.isZero}",     "replaceWLhs(nodep)");
    TREEOPV("AstNeq   {$rhsp.width1, $lhsp.isAllOnes, $rhsp}",  "AstNot{$rhsp}");
    TREEOPV("AstNeq   {$lhsp.width1, $lhsp, $rhsp.isAllOnes}",  "AstNot{$lhsp}");
    TREEOPV("AstLt    {$rhsp.width1, $lhsp.isZero,    $rhsp}",  "replaceWRhs(nodep)");  // Because not signed #s
    TREEOPV("AstGt    {$lhsp.width1, $lhsp, $rhsp.isZero}",     "replaceWLhs(nodep)");  // Because not signed #s
    // Useful for CONDs added around ARRAYSEL's in V3Case step
    TREEOPV("AstLte   {$lhsp->width()==$rhsp->width(), $rhsp.isAllOnes}", "replaceNum(nodep,1)");
    // Simplify reduction operators
    // This also gets &{...,0,....} => const 0  (Common for unused_ok signals)
    TREEOPV("AstRedAnd{$lhsp, $lhsp.width1}",   "replaceWLhs(nodep)");
    TREEOPV("AstRedOr {$lhsp, $lhsp.width1}",   "replaceWLhs(nodep)");
    TREEOPV("AstRedXor{$lhsp, $lhsp.width1}",   "replaceWLhs(nodep)");
    TREEOPV("AstRedAnd{$lhsp.castConcat}",      "AstAnd{AstRedAnd{$lhsp->castConcat()->lhsp()}, AstRedAnd{$lhsp->castConcat()->rhsp()}}");  // &{a,b} => {&a}&{&b}
    TREEOPV("AstRedOr {$lhsp.castConcat}",      "AstOr {AstRedOr {$lhsp->castConcat()->lhsp()}, AstRedOr {$lhsp->castConcat()->rhsp()}}");  // |{a,b} => {|a}|{|b}
    TREEOPV("AstRedXor{$lhsp.castConcat}",      "AstXor{AstRedXor{$lhsp->castConcat()->lhsp()}, AstRedXor{$lhsp->castConcat()->rhsp()}}");  // ^{a,b} => {^a}^{^b}
    TREEOPV("AstRedAnd{$lhsp.castExtend, $lhsp->width() > VN_CAST($lhsp,,Extend)->lhsp()->width()}", "replaceZero(nodep)");  // &{0,...} => 0  Prevents compiler limited range error
    TREEOPV("AstRedOr {$lhsp.castExtend}",      "AstRedOr {$lhsp->castExtend()->lhsp()}");
    TREEOPV("AstRedXor{$lhsp.castExtend}",      "AstRedXor{$lhsp->castExtend()->lhsp()}");
    TREEOP ("AstRedXor{$lhsp.castXor, VN_IS(VN_CAST($lhsp,,Xor)->lhsp(),,Const)}", "AstXor{AstRedXor{$lhsp->castXor()->lhsp()}, AstRedXor{$lhsp->castXor()->rhsp()}}");  // ^(const ^ a) => (^const)^(^a)
    TREEOPC("AstAnd {nodep->widthMin() == 1, $lhsp.castConst, $rhsp.castRedXor, matchBitOpTree(nodep)}", "DONE");
    TREEOPV("AstOneHot{$lhsp.width1}",          "replaceWLhs(nodep)");
    TREEOPV("AstOneHot0{$lhsp.width1}",         "replaceNum(nodep,1)");
    // Binary AND/OR is faster than logical and/or (usually)
    TREEOPV("AstLogAnd{$lhsp.width1, $rhsp.width1, isTPure($lhsp), isTPure($rhsp)}", "AstAnd{$lhsp,$rhsp}");
    TREEOPV("AstLogOr {$lhsp.width1, $rhsp.width1, isTPure($lhsp), isTPure($rhsp)}", "AstOr{$lhsp,$rhsp}");
    TREEOPV("AstLogNot{$lhsp.width1, isTPure($lhsp)}",  "AstNot{$lhsp}");
    // CONCAT(CONCAT({a},{b}),{c}) -> CONCAT({a},CONCAT({b},{c}))
    // CONCAT({const},CONCAT({const},{c})) -> CONCAT((constifiedCONC{const|const},{c}))
    TREEOPV("AstConcat{operandConcatMove(nodep)}",      "moveConcat(nodep)");
    TREEOPV("AstConcat{$lhsp.isZero, $rhsp}",           "replaceExtend(nodep, nodep->rhsp())");
    // CONCAT(a[1],a[0]) -> a[1:0]
    TREEOPV("AstConcat{$lhsp.castSel, $rhsp.castSel, ifAdjacentSel(VN_CAST($lhsp,,Sel),,VN_CAST($rhsp,,Sel))}",  "replaceConcatSel(nodep)");
    TREEOPV("AstConcat{ifConcatMergeableBiop($lhsp), concatMergeable($lhsp,,$rhsp)}", "replaceConcatMerge(nodep)");
    // Common two-level operations that can be simplified
    TREEOP ("AstAnd {$lhsp.castConst,matchAndCond(nodep)}",           "DONE");
    TREEOP ("AstAnd {$lhsp.castOr, $rhsp.castOr, operandAndOrSame(nodep)}",     "replaceAndOr(nodep)");
    TREEOP ("AstOr  {$lhsp.castAnd,$rhsp.castAnd,operandAndOrSame(nodep)}",     "replaceAndOr(nodep)");
    TREEOP ("AstOr  {matchOrAndNot(nodep)}",            "DONE");
    TREEOP ("AstAnd {operandShiftSame(nodep)}",         "replaceShiftSame(nodep)");
    TREEOP ("AstOr  {operandShiftSame(nodep)}",         "replaceShiftSame(nodep)");
    TREEOP ("AstXor {operandShiftSame(nodep)}",         "replaceShiftSame(nodep)");
    TREEOPC("AstAnd {nodep->widthMin() == 1, matchBitOpTree(nodep)}", "DONE");
    TREEOPC("AstOr  {nodep->widthMin() == 1, matchBitOpTree(nodep)}", "DONE");
    TREEOPC("AstXor {nodep->widthMin() == 1, matchBitOpTree(nodep)}", "DONE");
    // Note can't simplify a extend{extends}, extends{extend}, as the sign
    // bits end up in the wrong places
    TREEOPV("AstExtend {$lhsp.castExtend}",  "replaceExtend(nodep, VN_CAST(nodep->lhsp(), Extend)->lhsp())");
    TREEOPV("AstExtendS{$lhsp.castExtendS}", "replaceExtend(nodep, VN_CAST(nodep->lhsp(), ExtendS)->lhsp())");
    TREEOPV("AstReplicate{$lhsp, $rhsp.isOne, $lhsp->width()==nodep->width()}", "replaceWLhs(nodep)");  // {1{lhs}}->lhs
    TREEOPV("AstReplicateN{$lhsp, $rhsp.isOne, $lhsp->width()==nodep->width()}", "replaceWLhs(nodep)");  // {1{lhs}}->lhs
    TREEOPV("AstReplicate{$lhsp.castReplicate, operandRepRep(nodep)}", "DONE");  // {2{3{lhs}}}->{6{lhs}}
    TREEOPV("AstConcat{operandConcatSame(nodep)}", "DONE");  // {a,a}->{2{a}}, {a,2{a}}->{3{a}, etc
    // Next rule because AUTOINST puts the width of bits in
    // to pins, even when the widths are exactly the same across the hierarchy.
    TREEOPV("AstSel{operandSelExtend(nodep)}",  "DONE");
    TREEOPV("AstSel{operandSelFull(nodep)}",    "replaceWChild(nodep, nodep->fromp())");
    TREEOPV("AstSel{$fromp.castSel}",           "replaceSelSel(nodep)");
    TREEOPV("AstSel{$fromp.castAdd, operandSelBiLower(nodep)}", "DONE");
    TREEOPV("AstSel{$fromp.castAnd, operandSelBiLower(nodep)}", "DONE");
    TREEOPV("AstSel{$fromp.castOr,  operandSelBiLower(nodep)}", "DONE");
    TREEOPV("AstSel{$fromp.castSub, operandSelBiLower(nodep)}", "DONE");
    TREEOPV("AstSel{$fromp.castXor, operandSelBiLower(nodep)}", "DONE");
    TREEOPV("AstSel{$fromp.castShiftR, operandSelShiftLower(nodep)}",   "DONE");
    TREEOPA("AstSel{$fromp.castConst, $lsbp.castConst, $widthp.castConst, }",   "replaceConst(nodep)");
    TREEOPV("AstSel{$fromp.castConcat, $lsbp.castConst, $widthp.castConst, }",  "replaceSelConcat(nodep)");
    TREEOPV("AstSel{$fromp.castReplicate, $lsbp.castConst, $widthp.castConst, operandSelReplicate(nodep) }",    "DONE");
    // V3Tristate requires selects below BufIf1.
    // Also do additional operators that are bit-independent, but only definite
    // win if bit select is a constant (otherwise we may need to compute bit index several times)
    TREEOPV("AstSel{$fromp.castBufIf1}",                "replaceSelIntoBiop(nodep)");
    TREEOPV("AstSel{$fromp.castNot}",                   "replaceSelIntoUniop(nodep)");
    TREEOPV("AstSel{$fromp.castAnd,$lhsp.castConst}",   "replaceSelIntoUniop(nodep)");
    TREEOPV("AstSel{$fromp.castOr,$lhsp.castConst}",    "replaceSelIntoUniop(nodep)");
    TREEOPV("AstSel{$fromp.castXor,$lhsp.castConst}",   "replaceSelIntoUniop(nodep)");
    // This visit function here must allow for short-circuiting.
    TREEOPS("AstLogIf{$lhsp.isZero}",  "replaceNum(nodep, 1)");
    TREEOPV("AstLogIf{$lhsp, $rhsp}",  "AstLogOr{AstLogNot{$lhsp},$rhsp}");
    TREEOPV("AstLogEq{$lhsp, $rhsp}",  "replaceLogEq(nodep)");
    // Strings
    TREEOPA("AstPutcN{$lhsp.castConst, $rhsp.castConst, $thsp.castConst}",  "replaceConst(nodep)");
    TREEOPA("AstSubstrN{$lhsp.castConst, $rhsp.castConst, $thsp.castConst}",  "replaceConst(nodep)");
    TREEOPA("AstCvtPackString{$lhsp.castConst}", "replaceConstString(nodep, VN_CAST(nodep->lhsp(), Const)->num().toString())");
    // Custom
    // Implied by AstIsUnbounded::numberOperate: V("AstIsUnbounded{$lhsp.castConst}", "replaceNum(nodep, 0)");
    TREEOPV("AstIsUnbounded{$lhsp.castUnbounded}", "replaceNum(nodep, 1)");
    // clang-format on

    // Possible futures:
    // (a?(b?y:x):y) -> (a&&!b)?x:y
    // (a?(b?x:y):y) -> (a&&b)?x:y
    // (a?x:(b?x:y)) -> (a||b)?x:y
    // (a?x:(b?y:x)) -> (a||!b)?x:y

    // Note we can't convert EqCase/NeqCase to Eq/Neq here because that would break 3'b1x1==3'b101

    //-----
    virtual void visit(AstNode* nodep) override {
        // Default: Just iterate
        if (m_required) {
            if (VN_IS(nodep, NodeDType) || VN_IS(nodep, Range)) {
                // Ignore dtypes for parameter type pins
            } else {
                nodep->v3error("Expecting expression to be constant, but can't convert a "
                               << nodep->prettyTypeName() << " to constant.");
            }
        } else {
            // Calculate the width of this operation
            if (m_params && !nodep->width()) nodep = V3Width::widthParamsEdit(nodep);
            iterateChildren(nodep);
        }
    }

public:
    // Processing Mode Enum
    enum ProcMode : uint8_t {
        PROC_PARAMS,
        PROC_GENERATE,
        PROC_LIVE,
        PROC_V_WARN,
        PROC_V_NOWARN,
        PROC_V_EXPENSIVE,
        PROC_CPP
    };

    // CONSTRUCTORS
    explicit ConstVisitor(ProcMode pmode) {
        // clang-format off
        switch (pmode) {
        case PROC_PARAMS:       m_doV = true;  m_doNConst = true; m_params = true;
                                m_required = true; break;
        case PROC_GENERATE:     m_doV = true;  m_doNConst = true; m_params = true;
                                m_required = true; m_doGenerate = true; break;
        case PROC_LIVE:         break;
        case PROC_V_WARN:       m_doV = true;  m_doNConst = true; m_warn = true; break;
        case PROC_V_NOWARN:     m_doV = true;  m_doNConst = true; break;
        case PROC_V_EXPENSIVE:  m_doV = true;  m_doNConst = true; m_doExpensive = true; break;
        case PROC_CPP:          m_doV = false; m_doNConst = true; m_doCpp = true; break;
        default:                v3fatalSrc("Bad case"); break;
        }
        // clang-format on
    }
    virtual ~ConstVisitor() override {
        if (m_doCpp) {
            V3Stats::addStat("Optimizations, Const bit op reduction", m_statBitOpReduction);
        }
    }

    AstNode* mainAcceptEdit(AstNode* nodep) {
        // Operate starting at a random place
        return iterateSubtreeReturnEdits(nodep);
    }
};

//######################################################################
// Const class functions

//! Force this cell node's parameter list to become a constant
//! @return  Pointer to the edited node.
AstNode* V3Const::constifyParamsEdit(AstNode* nodep) {
    // if (debug() > 0) nodep->dumpTree(cout, "  forceConPRE : ");
    // Resize even if the node already has a width, because buried in the tree
    // we may have a node we just created with signing, etc, that isn't sized yet.

    // Make sure we've sized everything first
    nodep = V3Width::widthParamsEdit(nodep);
    ConstVisitor visitor(ConstVisitor::PROC_PARAMS);
    if (AstVar* varp = VN_CAST(nodep, Var)) {
        // If a var wants to be constified, it's really a param, and
        // we want the value to be constant.  We aren't passed just the
        // init value because we need widthing above to handle the var's type.
        if (varp->valuep()) visitor.mainAcceptEdit(varp->valuep());
    } else {
        nodep = visitor.mainAcceptEdit(nodep);
    }
    // Because we do edits, nodep links may get trashed and core dump this.
    // if (debug() > 0) nodep->dumpTree(cout, "  forceConDONE: ");
    return nodep;
}

//! Force this cell node's parameter list to become a constant inside generate.
//! If we are inside a generated "if", "case" or "for", we don't want to
//! trigger warnings when we deal with the width. It is possible that these
//! are spurious, existing within sub-expressions that will not actually be
//! generated. Since such occurrences, must be constant, in order to be
//! something a generate block can depend on, we can wait until later to do the
//! width check.
//! @return  Pointer to the edited node.
AstNode* V3Const::constifyGenerateParamsEdit(AstNode* nodep) {
    // if (debug() > 0) nodep->dumpTree(cout, "  forceConPRE : ");
    // Resize even if the node already has a width, because buried in the tree
    // we may have a node we just created with signing, etc, that isn't sized
    // yet.

    // Make sure we've sized everything first
    nodep = V3Width::widthGenerateParamsEdit(nodep);
    ConstVisitor visitor(ConstVisitor::PROC_GENERATE);
    if (AstVar* varp = VN_CAST(nodep, Var)) {
        // If a var wants to be constified, it's really a param, and
        // we want the value to be constant.  We aren't passed just the
        // init value because we need widthing above to handle the var's type.
        if (varp->valuep()) visitor.mainAcceptEdit(varp->valuep());
    } else {
        nodep = visitor.mainAcceptEdit(nodep);
    }
    // Because we do edits, nodep links may get trashed and core dump this.
    // if (debug() > 0) nodep->dumpTree(cout, "  forceConDONE: ");
    return nodep;
}

void V3Const::constifyAllLint(AstNetlist* nodep) {
    // Only call from Verilator.cpp, as it uses user#'s
    UINFO(2, __FUNCTION__ << ": " << endl);
    {
        ConstVisitor visitor(ConstVisitor::PROC_V_WARN);
        (void)visitor.mainAcceptEdit(nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("const", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}

void V3Const::constifyCpp(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    {
        ConstVisitor visitor(ConstVisitor::PROC_CPP);
        (void)visitor.mainAcceptEdit(nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("const_cpp", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}

AstNode* V3Const::constifyEdit(AstNode* nodep) {
    ConstVisitor visitor(ConstVisitor::PROC_V_NOWARN);
    nodep = visitor.mainAcceptEdit(nodep);
    return nodep;
}

void V3Const::constifyAllLive(AstNetlist* nodep) {
    // Only call from Verilator.cpp, as it uses user#'s
    // This only pushes constants up, doesn't make any other edits
    // IE doesn't prune dead statements, as we need to do some usability checks after this
    UINFO(2, __FUNCTION__ << ": " << endl);
    {
        ConstVisitor visitor(ConstVisitor::PROC_LIVE);
        (void)visitor.mainAcceptEdit(nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("const", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}

void V3Const::constifyAll(AstNetlist* nodep) {
    // Only call from Verilator.cpp, as it uses user#'s
    UINFO(2, __FUNCTION__ << ": " << endl);
    {
        ConstVisitor visitor(ConstVisitor::PROC_V_EXPENSIVE);
        (void)visitor.mainAcceptEdit(nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("const", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}

AstNode* V3Const::constifyExpensiveEdit(AstNode* nodep) {
    ConstVisitor visitor(ConstVisitor::PROC_V_EXPENSIVE);
    nodep = visitor.mainAcceptEdit(nodep);
    return nodep;
}
