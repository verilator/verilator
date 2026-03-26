// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: covergroup @@ event lowering
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3CoverAtat.h"

#include "V3ParseGrammar.h"
#include "V3Stats.h"

#include <unordered_map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

struct RegisteredHook final {
    std::string moduleName;
    std::string target;
    bool begin = false;
    AstNode* stmtp = nullptr;
};

std::vector<RegisteredHook>& registeredHooks() {
    static std::vector<RegisteredHook> s_hooks;
    return s_hooks;
}

class ParseRefResolverVisitor final : public VNVisitor {
    AstNodeModule* const m_modp;

    static AstVar* findModuleVar(AstNodeModule* modp, const string& name) {
        if (!modp) return nullptr;
        for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            AstVar* const varp = VN_CAST(nodep, Var);
            if (varp && varp->name() == name) return varp;
        }
        return nullptr;
    }

public:
    ParseRefResolverVisitor(AstNodeModule* modp, AstNode* nodep)
        : m_modp{modp} {
        iterate(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }
    void visit(AstParseRef* nodep) override {
        if (nodep->lhsp() || nodep->ftaskrefp()) return;
        AstVar* const varp = findModuleVar(m_modp, nodep->name());
        if (!varp) return;
        AstVarRef* const refp = new AstVarRef{nodep->fileline(), varp, VAccess::READ};
        nodep->replaceWith(refp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
};

class CoverAtatVisitor final : public VNVisitor {
    struct HookBodies final {
        std::vector<AstNode*> beginps;
        std::vector<AstNode*> endps;
    };
    struct PendingRewrite final {
        AstStmtExpr* nodep = nullptr;
        const HookBodies* hooksp = nullptr;
    };

    AstNodeModule* m_modp = nullptr;
    std::unordered_map<std::string, HookBodies> m_hooks;
    std::vector<PendingRewrite> m_pending;
    VDouble0 m_statHooks;
    VDouble0 m_statSamples;

    static AstNodeFTaskRef* stmtCallRefp(AstStmtExpr* nodep) {
        if (!nodep) return nullptr;
        if (AstNodeFTaskRef* const ftaskrefp = VN_CAST(nodep->exprp(), NodeFTaskRef)) return ftaskrefp;
        if (AstDot* const dotp = VN_CAST(nodep->exprp(), Dot)) {
            return VN_CAST(dotp->rhsp(), NodeFTaskRef);
        }
        return nullptr;
    }
    static AstNode* cloneStmtList(const std::vector<AstNode*>& templates) {
        AstNode* outp = nullptr;
        AstNode* tailp = nullptr;
        for (AstNode* const templatep : templates) {
            AstNode* const clonep = templatep->cloneTree(true);
            if (!outp) {
                outp = clonep;
            } else {
                tailp->addNextHere(clonep);
            }
            tailp = clonep;
            while (tailp->nextp()) tailp = tailp->nextp();
        }
        return outp;
    }
    void clearHooks() {
        for (auto& pair : m_hooks) {
            for (AstNode* const nodep : pair.second.beginps) VL_DO_DANGLING(nodep->deleteTree(), nodep);
            for (AstNode* const nodep : pair.second.endps) VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
        m_hooks.clear();
    }
    void loadHooks() {
        for (AstNode* nodep = m_modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            AstVar* const varp = VN_CAST(nodep, Var);
            if (!varp) continue;
            std::vector<std::pair<std::string, bool>> hookSpecs;
            AstNode* stmtp = nullptr;
            if (!V3ParseGrammar::makeCovergroupAtAtSampleStmt(varp, hookSpecs, stmtp)) continue;
            ParseRefResolverVisitor{m_modp, stmtp};
            for (const auto& hook : hookSpecs) {
                HookBodies& hooks = m_hooks[hook.first];
                AstNode* const clonep = stmtp->cloneTree(true);
                if (hook.second) {
                    hooks.beginps.push_back(clonep);
                } else {
                    hooks.endps.push_back(clonep);
                }
                ++m_statHooks;
            }
            VL_DO_DANGLING(stmtp->deleteTree(), stmtp);
        }

    }

public:
    explicit CoverAtatVisitor(AstNetlist* rootp) {
        iterate(rootp);
        clearHooks();
        V3Stats::addStat("Covergroup @@ hooks", m_statHooks);
        V3Stats::addStat("Covergroup @@ samples", m_statSamples);
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }
    void visit(AstNodeModule* nodep) override {
        if (VN_IS(nodep, Class)) return;
        VL_RESTORER(m_modp);
        auto savedHooks = std::move(m_hooks);
        m_modp = nodep;
        m_hooks.clear();
        m_pending.clear();
        loadHooks();
        iterateChildren(nodep);
        for (const PendingRewrite& rewrite : m_pending) {
            AstStmtExpr* const stmtp = rewrite.nodep;
            const HookBodies& hooks = *rewrite.hooksp;
            VNRelinker relinkHandle;
            stmtp->unlinkFrBack(&relinkHandle);
            AstBegin* const beginp = new AstBegin{stmtp->fileline(), "", nullptr, false};
            if (!hooks.beginps.empty()) {
                beginp->addStmtsp(cloneStmtList(hooks.beginps));
                m_statSamples += hooks.beginps.size();
            }
            beginp->addStmtsp(stmtp);
            if (!hooks.endps.empty()) {
                beginp->addStmtsp(cloneStmtList(hooks.endps));
                m_statSamples += hooks.endps.size();
            }
            relinkHandle.relink(beginp);
        }
        m_pending.clear();
        clearHooks();
        m_hooks = std::move(savedHooks);
    }
    void visit(AstStmtExpr* nodep) override {
        iterateChildren(nodep);
        AstNodeFTaskRef* const callp = stmtCallRefp(nodep);
        if (!callp) return;
        const auto it = m_hooks.find(callp->name());
        if (it == m_hooks.end()) return;
        m_pending.push_back(PendingRewrite{nodep, &it->second});
    }
};

}  // namespace

void V3CoverAtat::registerHook(AstNodeModule* modp, const string& target, bool begin, AstNode* stmtp) {
    if (!stmtp) return;
    if (target.empty()) {
        if (stmtp) VL_DO_DANGLING(stmtp->deleteTree(), stmtp);
        return;
    }
    registeredHooks().push_back(RegisteredHook{modp ? modp->name() : "", target, begin, stmtp});
}

void V3CoverAtat::coverAtat(AstNetlist* rootp) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    V3Stats::addStat("Covergroup @@ registered", static_cast<VDouble0>(registeredHooks().size()));
    { CoverAtatVisitor{rootp}; }

    for (RegisteredHook& reg : registeredHooks()) {
        if (reg.stmtp) VL_DO_DANGLING(reg.stmtp->deleteTree(), reg.stmtp);
    }
    registeredHooks().clear();
}
