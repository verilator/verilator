// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Insert DPI hooks at configured signal targets
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
// V3InsertDPIHook's Transformations:
// The hook-insertion configuration map is populated with the relevant nodes, as defined by the
// target string specified in the hook-insertion configuration within the .vlt file.
// Additionally, the AST (Abstract Syntax Tree) is modified to insert the necessary extra nodes
// required for calling the DPI hooks.
// Furthermore, the links between Module, Cell, and Var nodes are adjusted to ensure correct
// connectivity for the DPI hook purposes.
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3InsertDPIHook.h"

#include "V3Control.h"

#include <optional>

VL_DEFINE_DEBUG_FUNCTIONS;

static int dpiHookSlots() {
    size_t slots = 0;
    for (const auto& targetCfg : V3Control::getHookInsertCfg()) slots += targetCfg.second.size();
    return static_cast<int>(slots);
}
struct DTypeCache final {
    AstBasicDType* stringDTypep = nullptr;  // String dtype used for path parts
    AstBasicDType* intDTypep = nullptr;  // Signed-int dtype used for path-filter loop index
    AstUnpackArrayDType* partSelDTypep = nullptr;  // Dtype used for one path slot (hookPath[i])
};
// A target path names an element by its declared index (`m[5]` of `m[4:7]`)
static bool isElemIndexInRange(const AstNodeArrayDType* adtypep, uint32_t index) {
    return static_cast<int>(index) >= adtypep->lo() && static_cast<int>(index) <= adtypep->hi();
}
static uint32_t elemPos(const AstNodeArrayDType* adtypep, uint32_t index) {
    return index - static_cast<uint32_t>(adtypep->lo());
}
static bool isHookableBasic(const AstBasicDType* basicp) {
    return basicp && basicp->isLiteralType() && !basicp->isDouble();
}

static bool isDynamicContainer(const AstNodeDType* dtypep) {
    return dtypep->isDynamicallySized() && !VN_IS(dtypep, BasicDType);
}
// The first leaf of an unpacked aggregate a hook cannot carry, nullptr if there is none
static AstNodeDType* unhookableLeafDTypep(AstNodeDType* dtypep, string& path) {
    dtypep = dtypep->skipRefp();
    const AstStructDType* const structp = VN_CAST(dtypep, StructDType);
    if (structp && !structp->packed()) {
        for (AstMemberDType* memberp = structp->membersp(); memberp;
             memberp = VN_CAST(memberp->nextp(), MemberDType)) {
            if (AstNodeDType* const leafDTypep
                = unhookableLeafDTypep(memberp->subDTypep(), path)) {
                path = "." + memberp->name() + path;
                return leafDTypep;
            }
        }
        return nullptr;
    }
    if (const AstUnpackArrayDType* const adtypep = VN_CAST(dtypep, UnpackArrayDType)) {
        AstNodeDType* const leafDTypep = unhookableLeafDTypep(adtypep->subDTypep(), path);
        if (leafDTypep) path = "[" + std::to_string(adtypep->left()) + "]" + path;
        return leafDTypep;
    }
    return isHookableBasic(dtypep->basicp()) && !isDynamicContainer(dtypep) ? nullptr : dtypep;
}
// Width and leaf count of an unpacked aggregate whose leaves a hook can carry
static int aggregateBitWidth(AstNodeDType* dtypep) {
    dtypep = dtypep->skipRefp();
    if (const AstStructDType* const structp = VN_CAST(dtypep, StructDType)) {
        if (structp->packed()) return dtypep->width();
        int w = 0;
        for (AstMemberDType* memberp = structp->membersp(); memberp;
             memberp = VN_CAST(memberp->nextp(), MemberDType))
            w += aggregateBitWidth(memberp->subDTypep());
        return w;
    }
    if (const AstUnpackArrayDType* const adtypep = VN_CAST(dtypep, UnpackArrayDType))
        return adtypep->elementsConst() * aggregateBitWidth(adtypep->subDTypep());
    return dtypep->width();  // Basic or packed leaf
}
static int aggregateLeafCount(AstNodeDType* dtypep) {
    dtypep = dtypep->skipRefp();
    if (const AstStructDType* const structp = VN_CAST(dtypep, StructDType)) {
        if (structp->packed()) return 1;
        int n = 0;
        for (AstMemberDType* memberp = structp->membersp(); memberp;
             memberp = VN_CAST(memberp->nextp(), MemberDType))
            n += aggregateLeafCount(memberp->subDTypep());
        return n;
    }
    if (const AstUnpackArrayDType* const adtypep = VN_CAST(dtypep, UnpackArrayDType))
        return adtypep->elementsConst() * aggregateLeafCount(adtypep->subDTypep());
    return 1;
}
static bool isAggregateLeafDType(AstNodeDType* dtypep) {
    dtypep = dtypep->skipRefp();
    if (const AstStructDType* const structp = VN_CAST(dtypep, StructDType))
        return structp->packed();
    if (VN_IS(dtypep, UnpackArrayDType)) return false;
    return dtypep->basicp() && !isDynamicContainer(dtypep);
}
struct HookInsertEntry final {
    string callback;  // Name of the DPI callback function to insert
    string varTarget;  // Target variable name within the module
    AccessPath accessPath;  // Member/index steps into the target var ("a.b[i]"); empty for scalars
    AstVar* origVarp = nullptr;  // Original variable pointer
    AstVar* hookedVarp = nullptr;  // Cloned variable pointer from original with edits
    string hookedName;
    AstNodeDType* hookedDTypep = nullptr;
    std::vector<AstNodeAssign*> assignps;  // Assign nodes which should be edited later on
    std::vector<AstNodeVarRef*> readRefps;  // Read refs to redirect (VarRef or cross-ref VarXRef)
    std::vector<AstNodeVarRef*> writeRefps;  // Driver refs of an interface signal
    std::vector<AstVarXRef*> readXrefps;  // Cross-module read refs from an enclosing module
    bool found = false;  // Whether the target variable was found during data finder pass
    bool done = false;  // Whether the hook insertion has been completed for a signal
    bool isAggregateMirror = false;  // Whether origVarp is the packed mirror of aggregateVarp
    AstVar* aggregateVarp = nullptr;  // The original unpacked aggregate var
    string genScope;  // Generate-block prefix in source notation ("lane[0]")
    string origTarget;  // Target as the user specified
    std::optional<uint32_t> elemIndex() const {
        if (accessPath.size() == 1 && accessPath.front().isIndex) return accessPath.front().index;
        return std::nullopt;
    }
    bool hasMemberStep() const {
        for (const StepIntoTarget& step : accessPath)
            if (!step.isIndex) return true;
        return false;
    }
    // Access path in source notation (".a", "[2].x"), used for messages
    string accessPathText() const {
        string s;
        for (const StepIntoTarget& step : accessPath)
            s += step.isIndex ? ("[" + std::to_string(step.index) + "]") : ("." + step.member);
        return s;
    }
    // Name-safe suffix encoding for access path ("_a", "_arr_2_x")
    // Keeps per-leaf hook var names unique when several members of one struct var are hooked
    string accessPathSuffix() const {
        string s;
        for (const StepIntoTarget& step : accessPath)
            s += step.isIndex ? ("_" + std::to_string(step.index)) : ("_" + step.member);
        return s;
    }
    // Generate name-safe suffix for generate-block scope ("lane[0]" -> "_lane_0")
    // Keeps hook var names unique across unrolled generate copies
    string genScopeSuffix() const {
        if (genScope.empty()) return "";
        string s = "_";
        for (const char c : genScope) {
            if ((c >= '0' && c <= '9') || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')) {
                s += c;
            } else if (c == '[' || c == '.') {
                s += '_';
            }
        }
        return s;
    }
};
struct HookInsertTarget final {
    AstModule* origModp = nullptr;  // Original module pointer containing target var
    AstIface* ifacep = nullptr;  // Interface holding the target signals
    AstVar* dpiTriggerVarp = nullptr;  // Trigger for the DPI function/task
    bool error = false;  // Whether an error occurred during the finder visitor
    std::vector<AstCell*> cellps;  // Cells that need to have hook inputs
    std::vector<AstNodeModule*> modps;  // Modules and interfaces that need to have hook inputs
    std::vector<HookInsertEntry> entries;  // All hook insertion entries for this target
    AstNodeModule* hookLogicContainerp() const {
        return ifacep ? static_cast<AstNodeModule*>(ifacep)
                      : static_cast<AstNodeModule*>(origModp);
    }  // The container receiving the hook logic
};

//######################################################################
// Shared builder for the "path filter" always-block emitted by path router
// (HookPathRouter::insertPathFilter) and override builder
// (DpiOverrideBuilder::insertTargetFilterp).

struct PathFilterConfig final {
    AstNodeModule* modp = nullptr;  // Module/iface receiving the always block (also fileline src)
    AstBasicDType* intDTypep = nullptr;  // Signed-int dtype for the loop index (pre-registered)
    AstBasicDType* stringDTypep = nullptr;  // String dtype for the decoded part (pre-registered)
    AstVar* hookPathVarp = nullptr;  // DPIHOOK_PATH input being decoded
    string targetVarName;  // Name of the decoded-part variable
    VLifetime targetVarLifetime;  // Lifetime of the decoded-part variable
    bool targetVarHasUserInit = false;  // Whether to mark the decoded-part var hasUserInit
    bool declTargetInLoopBody = false;  // Declare targetVar in the loop body (true) or the
                                        // always body (false)
    string alwaysName;  // Name given to the generated begin/always block
    std::unordered_map<AstNodeModule*, AstCase*>* caseCachep
        = nullptr;  // Cache to register case in
    std::unordered_map<AstNodeModule*, AstVar*>* loopVarCachep
        = nullptr;  // Cache to register loop index var in, keyed by module.
};
struct PathFilterResult final {
    AstCase* casep = nullptr;  // The (still item-less) case statement
    AstVar* loopVarp = nullptr;  // Loop index, for case-item building
    AstArraySel* partSelp = nullptr;  // Inner arraysel: hookPath[i]
    AstArraySel* targetSelp = nullptr;  // Outer arraysel: hookPath[i][0]
};
static PathFilterResult buildPathFilter(const PathFilterConfig& cfg) {
    AstNodeModule* const modp = cfg.modp;
    FileLine* const fl = modp->fileline();
    // Create the loop variable index
    AstVar* const loopVarp = new AstVar{fl, VVarType::VAR, "__Vdpihook_i", cfg.intDTypep};
    loopVarp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
    loopVarp->usedLoopIdx(true);
    (*cfg.loopVarCachep)[modp] = loopVarp;
    // Create target path variable for the case selection and assignment
    AstVar* const targetVarp = new AstVar{fl, VVarType::VAR, cfg.targetVarName, cfg.stringDTypep};
    targetVarp->hasUserInit(cfg.targetVarHasUserInit);
    targetVarp->lifetime(cfg.targetVarLifetime);
    AstVarRef* const targetWriteRefp = new AstVarRef{fl, targetVarp, VAccess::WRITE};
    AstVarRef* const targetReadRefp = new AstVarRef{fl, targetVarp, VAccess::READ};
    // Create Case (items are added by the caller)
    AstCase* const casep = new AstCase{fl, VCaseType::CT_CASE, targetReadRefp, nullptr};
    cfg.caseCachep->insert({modp, casep});
    // Create Assign decoding hookPath[i][0] into the target path variable
    AstVarRef* const hookPathRefp = new AstVarRef{fl, cfg.hookPathVarp, VAccess::READ};
    AstArraySel* const partSelp
        = new AstArraySel{fl, hookPathRefp, new AstVarRef{fl, loopVarp, VAccess::READ}};
    AstArraySel* const targetSelp = new AstArraySel{fl, partSelp, new AstConst{fl, 0}};
    AstAssign* const caseAssignp = new AstAssign{fl, targetWriteRefp, targetSelp};
    // Create the begin for the Case selection
    AstBegin* const pathFilterBeginp = new AstBegin{fl, "", nullptr, false};
    if (cfg.declTargetInLoopBody) pathFilterBeginp->addDeclsp(targetVarp);
    pathFilterBeginp->addStmtsp(caseAssignp);
    pathFilterBeginp->addStmtsp(casep);
    // Create Loop to iterate over the different paths
    AstLoop* const loopp = new AstLoop{fl, nullptr};
    AstLtS* const ltsp = new AstLtS{fl, new AstVarRef{fl, loopVarp, VAccess::READ},
                                    new AstConst{fl, static_cast<uint32_t>(dpiHookSlots())}};
    AstLoopTest* const loopTestp = new AstLoopTest{fl, loopp, ltsp};
    AstAdd* const addp
        = new AstAdd{fl, new AstVarRef{fl, loopVarp, VAccess::READ}, new AstConst{fl, 1}};
    AstVarRef* const loopWriteRefp = new AstVarRef{fl, loopVarp, VAccess::WRITE};
    AstAssign* const loopIncAssignp = new AstAssign{fl, loopWriteRefp, addp};
    loopp->addStmtsp(loopTestp);
    loopp->addStmtsp(pathFilterBeginp);
    loopp->addStmtsp(loopIncAssignp);
    // Create Assign for the loop variable (0 in beginning)
    AstAssign* const loopInitAssignp
        = new AstAssign{fl, loopWriteRefp->cloneTree(false), new AstConst{fl, 0}};
    // Create the loop
    AstBegin* const loopBeginp = new AstBegin{fl, "", nullptr, true};
    loopBeginp->addDeclsp(loopVarp);
    loopBeginp->addStmtsp(loopInitAssignp);
    loopBeginp->addStmtsp(loopp);
    // Create the always block
    AstBegin* const beginp = new AstBegin{fl, "", nullptr, false};
    if (VN_IS(modp, Iface)) {
        AstDelay* const delayp
            = new AstDelay{fl, new AstConst{fl, AstConst::WidthedValue{}, 64, 0}, false};
        delayp->timeunit(v3Global.rootp()->timeunit());
        beginp->addStmtsp(delayp);
    }
    beginp->addStmtsp(loopBeginp);
    if (!cfg.declTargetInLoopBody) beginp->addDeclsp(targetVarp);
    beginp->name(cfg.alwaysName);
    // Evaluate the binding ONCE, at time zero. The path ports are written by the
    // wrapper before the first eval(), which is the ordering Verilator documents
    // for any input. A 'changed' sensitivity would instead make Verilator compare
    // and copy the whole string array on every eval, for the entire run.
    modp->addStmtsp(new AstInitial{fl, beginp});
    return PathFilterResult{casep, loopVarp, partSelp, targetSelp};
}

//######################################################################
// Shared helpers for naming generate-block scopes and the cells inside them

static AstNode* getParentp(const AstNode* nodep) {
    while (AstNode* const backp = nodep->backp()) {
        if (backp->nextp() == nodep) {
            nodep = backp;
            continue;
        }
        return backp;
    }
    return nullptr;
}
using InstPathKey = std::pair<const AstNodeModule*, string>;
using InstPathMap = std::map<InstPathKey, AstVar*>;
static AstNodeModule* cellOwnerModp(const AstCell* cellp) {
    for (AstNode* parentp = getParentp(cellp); parentp; parentp = getParentp(parentp))
        if (AstNodeModule* const modp = VN_CAST(parentp, NodeModule)) return modp;
    return nullptr;
}
static string cellFlatName(const AstCell* cellp) {
    string name = cellp->name();
    for (AstNode* parentp = getParentp(cellp); parentp; parentp = getParentp(parentp)) {
        if (VN_IS(parentp, NodeModule)) break;
        if (const AstGenBlock* const genBlockp = VN_CAST(parentp, GenBlock))
            if (!genBlockp->implied()) name = genBlockp->name() + "__DOT__" + name;
    }
    return name;
}
static AstGenBlock* cellGenBlockp(const AstCell* cellp) {
    for (AstNode* parentp = getParentp(cellp); parentp; parentp = getParentp(parentp)) {
        if (VN_IS(parentp, NodeModule)) break;
        if (AstGenBlock* const genBlockp = VN_CAST(parentp, GenBlock))
            if (!genBlockp->implied()) return genBlockp;
    }
    return nullptr;
}
static string flatNameTail(const string& flatName) {
    const size_t pos = flatName.rfind("__DOT__");
    return pos == string::npos ? flatName : flatName.substr(pos + 7);
}
// One select of the AST chain from a target variable to the leaf its access path addresses
struct ChainStep final {
    enum Kind : uint8_t { ARRAYSEL, STRUCTSEL, BITSEL } kind = ARRAYSEL;
    uint32_t index = 0;  // ARRAYSEL
    string member;  // STRUCTSEL
    int lsb = 0;  // BITSEL
    int width = 0;  // BITSEL
    AstNodeDType* dtypep = nullptr;  // Type of selected part
};
// The selects `path` applies to `rootVarp`, when the path is already checked against its type
static std::vector<ChainStep> accessChainSteps(const AstVar* rootVarp, const AccessPath& path) {
    std::vector<ChainStep> steps;
    AstNodeDType* dtypep = rootVarp->dtypep()->skipRefp();
    for (const StepIntoTarget& step : path) {
        ChainStep out;
        if (step.isIndex) {
            AstUnpackArrayDType* const adtypep = VN_AS(dtypep, UnpackArrayDType);
            out.kind = ChainStep::ARRAYSEL;
            out.index = elemPos(adtypep, step.index);
            out.dtypep = adtypep->subDTypep();
        } else {
            AstStructDType* const structp = VN_AS(dtypep, StructDType);
            AstNodeDType* memberDTypep = nullptr;
            int msbOff = 0;
            for (AstMemberDType* memberp = structp->membersp(); memberp;
                 memberp = VN_CAST(memberp->nextp(), MemberDType)) {
                if (memberp->name() == step.member) {
                    memberDTypep = memberp->subDTypep();
                    break;
                }
                msbOff += aggregateBitWidth(memberp->subDTypep());
            }
            out.dtypep = memberDTypep;
            if (structp->packed()) {
                out.kind = ChainStep::BITSEL;
                out.width = memberDTypep->width();
                out.lsb = structp->width() - msbOff - out.width;
            } else {
                out.kind = ChainStep::STRUCTSEL;
                out.member = step.member;
            }
        }
        dtypep = out.dtypep->skipRefp();
        steps.push_back(out);
    }
    return steps;
}
// Whether the reference `refp` reaches the leaf that `steps` select. It does when the selects
// over it agree with `steps` as far as they go (a non-constant index agrees with any index)
static bool reachesLeaf(const AstNodeVarRef* refp, const std::vector<ChainStep>& steps) {
    const AstNode* curp = refp;
    for (const ChainStep& step : steps) {
        const AstNode* const parentp = curp->backp();
        switch (step.kind) {
        case ChainStep::ARRAYSEL: {
            const AstArraySel* const arraySelp = VN_CAST(parentp, ArraySel);
            if (!arraySelp || arraySelp->fromp() != curp) return true;  // The whole array
            const AstConst* const idxConstp = VN_CAST(arraySelp->bitp(), Const);
            if (idxConstp && idxConstp->toUInt() != step.index) return false;
            break;
        }
        case ChainStep::STRUCTSEL: {
            const AstStructSel* const structSelp = VN_CAST(parentp, StructSel);
            if (!structSelp || structSelp->fromp() != curp) return true;  // The whole struct
            if (structSelp->name() != step.member) return false;
            break;
        }
        case ChainStep::BITSEL: {
            const AstSel* const bitSelp = VN_CAST(parentp, Sel);
            if (!bitSelp || bitSelp->fromp() != curp) return true;  // The whole packed value
            const AstConst* const lsbp = VN_CAST(bitSelp->lsbp(), Const);
            if (!lsbp) return true;
            const int lsb = lsbp->toSInt();
            return lsb < step.lsb + step.width && step.lsb < lsb + bitSelp->widthConst();
        }
        }
        curp = parentp;
    }
    return true;
}

//######################################################################
// Report whether a variable, or the leaf of it the steps select, is used as a clock (or an
// asynchronous reset) or in an event control

class ClockUseVisitor final : public VNVisitorConst {
    const AstVar* const m_targetVarp;  // Variable being checked
    const std::vector<ChainStep> m_steps;  // Selects from the variable to the hooked leaf
    const AstSenItem* m_senItemp = nullptr;  // Event control item being iterated
    bool m_isClock = false;  // Target found in an edge-sensitive sen item
    bool m_isEvent = false;  // Target found in a sen item without an edge (`always @(a or b)`)

    void visit(AstSenItem* nodep) override {
        VL_RESTORER(m_senItemp);
        m_senItemp = (nodep->isClocked() && nodep->sensp()) ? nodep : nullptr;
        iterateChildrenConst(nodep);
    }
    void visit(AstNodeVarRef* nodep) override {
        if (m_senItemp && nodep->varp() == m_targetVarp && reachesLeaf(nodep, m_steps)) {
            if (m_senItemp->edgeType().anEdge()) {
                m_isClock = true;
            } else {
                m_isEvent = true;
            }
        }
        iterateChildrenConst(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    ClockUseVisitor(AstNetlist* netlistp, const AstVar* targetVarp,
                    const std::vector<ChainStep>& steps)
        : m_targetVarp{targetVarp}
        , m_steps{steps} {
        iterateConst(netlistp);
    }
    ~ClockUseVisitor() override = default;
    bool isClock() const { return m_isClock; }
    bool isEventControl() const { return m_isEvent; }
};

static void collectLeafAccesses(AstNodeExpr* accessp, AstNodeDType* dtypep,
                                std::vector<AstNodeExpr*>& leafps, std::vector<int>& widths) {
    AstNodeDType* const skippedDTypep = dtypep->skipRefp();
    FileLine* const fl = accessp->fileline();
    if (isAggregateLeafDType(skippedDTypep)) {
        accessp->dtypep(skippedDTypep);
        leafps.push_back(accessp);
        widths.push_back(skippedDTypep->width());
        return;
    }
    if (AstStructDType* const structp = VN_CAST(skippedDTypep, StructDType)) {
        for (AstMemberDType* memberp = structp->membersp(); memberp;
             memberp = VN_CAST(memberp->nextp(), MemberDType)) {
            AstStructSel* const selp
                = new AstStructSel{fl, accessp->cloneTree(false), memberp->name()};
            selp->dtypep(memberp->subDTypep());
            collectLeafAccesses(selp, memberp->subDTypep(), leafps, widths);
        }
    } else if (AstUnpackArrayDType* const adtypep = VN_CAST(skippedDTypep, UnpackArrayDType)) {
        const int n = adtypep->elementsConst();
        for (int i = 0; i < n; ++i) {
            AstArraySel* const selp = new AstArraySel{fl, accessp->cloneTree(false),
                                                      new AstConst{fl, static_cast<uint32_t>(i)}};
            selp->dtypep(adtypep->subDTypep());
            collectLeafAccesses(selp, adtypep->subDTypep(), leafps, widths);
        }
    }
    VL_DO_DANGLING(accessp->deleteTree(), accessp);
}

//######################################################################
// Collect nodes and data from the AST for hook-insertion

class HookInsertTargetFinder final {
    AstNetlist* const m_netlistp;  // Netlist the targets are resolved in
    std::map<string, HookInsertTarget>&
        m_insertCfg;  // Target configs, completed with the resolved nodes
    AstModule* m_targetModp = nullptr;  // Module declaring the target being resolved
    AstNode* m_targetScopep = nullptr;  // Innermost scope holding the target var
    bool m_error = false;  // Resolving the current target failed
    bool m_foundVar = false;  // Found targeted variable of the current config
    int m_errCountAtTarget = 0;  // Error count when resolving the current target started
    string m_curHier;  // Instance path resolved so far
    string m_target;  // Current config key
    HookInsertTarget* m_targetp = nullptr;  // Config of the current key

    // Collect `assignp` if it reads the resolved target variable, with matching done by
    // variable identity, not by name. An output target is driven from its hook instead,
    // so its reads need no redirect.
    void collectAssign(AstNodeAssign* assignp, const AstVar* targetVarp, const string& varName) {
        const auto readsTarget = [&](const AstNodeVarRef* refp) {
            return refp->varp() == targetVarp && refp->access().isReadOnly()
                   && !refp->varp()->isFuncLocal();
        };
        if (assignp->rhsp()->exists(readsTarget) || assignp->lhsp()->exists(readsTarget))
            addAssign(assignp, varName);
    }
    void setVarAt(size_t entryIdx, AstVar* origVarp, const string& hookedName,
                  AstNodeDType* hookedDTypep) {
        HookInsertEntry& entry = m_targetp->entries[entryIdx];
        entry.origVarp = origVarp;
        entry.hookedName = hookedName;
        entry.hookedDTypep = hookedDTypep;
        entry.found = true;
    }
    void addAssign(AstNodeAssign* assignp, const string& varName) {
        for (auto& entry : m_targetp->entries) {
            if (varName == entry.varTarget) {
                entry.assignps.push_back(assignp);
                return;
            }
        }
    }
    void addReadRef(AstNodeVarRef* readRefp, const string& varName) {
        for (auto& entry : m_targetp->entries) {
            if (varName == entry.varTarget) {
                entry.readRefps.push_back(readRefp);
                return;
            }
        }
    }
    static string genBlockName(const string& name, uint32_t idx) {
        return name + "__BRA__" + std::to_string(idx) + "__KET__";
    }
    static AstNode* scopeDeclsp(AstNode* scopep) {
        if (AstNodeModule* const modp = VN_CAST(scopep, NodeModule)) return modp->stmtsp();
        if (AstGenBlock* const genBlockp = VN_CAST(scopep, GenBlock)) return genBlockp->itemsp();
        return nullptr;
    }
    static AstCell* scopeChildCellp(AstNode* scopep, const string& name) {
        for (AstNode* declp = scopeDeclsp(scopep); declp; declp = declp->nextp()) {
            if (AstCell* const cellp = VN_CAST(declp, Cell))
                if (cellp->name() == name) return cellp;
            if (AstGenBlock* const genBlockp = VN_CAST(declp, GenBlock))
                if (genBlockp->implied())
                    if (AstCell* const foundCellp = scopeChildCellp(genBlockp, name))
                        return foundCellp;
        }
        return nullptr;
    }
    // Element cell of an instance array, e.g. "arr[1]". Elaboration fully expands
    // instance arrays, so by the time this pass runs the element is an ordinary
    // cell carrying the encoded name and there is no AstRange left to walk. An
    // index outside the declared range simply finds no cell.
    static AstCell* arrayedInstCellp(AstNode* scopep, const string& name, uint32_t index) {
        return scopeChildCellp(scopep, name + "__BRA__"
                                           + AstNode::encodeNumber(static_cast<int64_t>(index))
                                           + "__KET__");
    }
    // Only interface arrays are addressable; see the module-array rejection below.
    static AstCell* arrayedIfaceCellp(AstNode* scopep, const string& name, uint32_t index) {
        AstCell* const cellp = arrayedInstCellp(scopep, name, index);
        return (cellp && VN_IS(cellp->modp(), Iface)) ? cellp : nullptr;
    }
    static AstVar* scopeChildVarp(AstNode* scopep, const string& name) {
        for (AstNode* declp = scopeDeclsp(scopep); declp; declp = declp->nextp())
            if (AstVar* const varp = VN_CAST(declp, Var))
                if (varp->name() == name) return varp;
        return nullptr;
    }
    static AstGenBlock* childGenBlockp(AstNode* nodep, const string& name) {
        for (AstNode* itemp = nodep; itemp; itemp = itemp->nextp()) {
            if (AstGenBlock* const genBlockp = VN_CAST(itemp, GenBlock)) {
                if (genBlockp->name() == name) return genBlockp;
                if (genBlockp->implied())
                    if (AstGenBlock* const foundGenBlockp
                        = childGenBlockp(genBlockp->itemsp(), name))
                        return foundGenBlockp;
            }
        }
        return nullptr;
    }
    // Split path component into its name and optional array index
    // "arr[2]" -> {"arr", 2}, "u" -> {"u", nullopt}
    static std::pair<string, std::optional<uint32_t>> parseComponent(const string& part) {
        const auto open = part.find('[');
        if (open == string::npos || part.back() != ']') return {part, std::nullopt};
        const string index = part.substr(open + 1, part.size() - open - 2);
        if (!isDpiHookConfigNumber(index)) return {part, std::nullopt};
        return {part.substr(0, open), static_cast<uint32_t>(std::stoul(index))};
    }
    static bool isPartOfAssign(const AstNode* nodep) {
        for (const AstNode* curp = nodep; curp->backp(); curp = curp->backp()) {
            const AstNode* const backp = curp->backp();
            if (backp->nextp() != curp && VN_IS(backp, NodeAssign)) return true;
        }
        return false;
    }
    void navigateToTarget() {
        const std::deque<string> targetParts = VString::split(m_target, '.');
        AstNodeModule* const topModp = m_netlistp->topModulep();
        if (targetParts.empty() || targetParts.front() != topModp->name()) {
            topModp->fileline()->v3error("DPI-hook insertion of target '"
                                         << m_target
                                         << "' could not find initial 'module' in "
                                            "'topModule.instance.__'");
            m_error = true;
            return;
        }
        AstNodeModule* curModp = topModp;
        AstNode* curScopep = topModp;
        string genScope;
        m_curHier = targetParts.front();
        for (size_t i = 1; i < targetParts.size(); ++i) {
            const auto [partName, partIdx] = parseComponent(targetParts[i]);
            AstCell* const targetCellp
                = partIdx ? arrayedIfaceCellp(curScopep, partName, partIdx.value())
                          : scopeChildCellp(curScopep, partName);
            if (targetCellp && targetCellp->modp()) {
                AstNodeModule* const childModp = targetCellp->modp();
                m_targetp->modps.push_back(curModp);
                curModp->foreach([&](AstNode* nodep) {
                    if (AstCell* const cellp = VN_CAST(nodep, Cell))
                        if (cellp->modp() == childModp && cellOwnerModp(cellp) == curModp)
                            m_targetp->cellps.push_back(cellp);
                });
                m_curHier += "." + targetParts[i];
                curModp = childModp;
                curScopep = childModp;
                genScope.clear();  // crossed a module boundary
                continue;
            }
            // Not a cell: if it names a variable, this is the instance/var boundary
            // and the remaining components are a member/index access path into it
            if (scopeChildVarp(curScopep, partName)) {
                if (!genScope.empty()) {
                    curScopep->fileline()->v3error(
                        "DPI-hook insertion of target '"
                        << m_target
                        << "': a member path into a variable of a generate block is not"
                           " supported");
                    m_error = true;
                    return;
                }
                resolveMemberPath(curModp, targetParts, i);
                return;
            }
            // An indexed component may be an unrolled generate-loop iteration (e.g. "lane[0]")
            // Therefore descend into generate block and pin the var there
            if (AstGenBlock* const genBlockp
                = childGenBlockp(scopeDeclsp(curScopep),
                                 partIdx ? genBlockName(partName, partIdx.value()) : partName)) {
                curScopep = genBlockp;
                genScope += (genScope.empty() ? "" : ".") + targetParts[i];
                m_curHier += "." + targetParts[i];
                continue;
            }
            if (partIdx) {
                AstCell* const arrayCellp = arrayedInstCellp(curScopep, partName, partIdx.value());
                if (arrayCellp) {
                    arrayCellp->fileline()->v3error(
                        "DPI-hook insertion of target '"
                        << m_target << "': arrayed module instances are not supported");
                    m_error = true;
                    return;
                }
            }
            // Neither a cell nor a var -> missing instance
            if (i == 1) {
                curModp->fileline()->v3error("DPI-hook insertion of target '"
                                             << m_target
                                             << "' could not find initial 'instance' in "
                                                "'topModule.instance.__'");
            } else {
                curModp->fileline()->v3error("DPI-hook insertion of target '"
                                             << m_target
                                             << "' could not find 'instance' in "
                                                "'__.instance.__'");
            }
            m_error = true;
            return;
        }
        AstModule* const origModp = VN_CAST(curModp, Module);
        if (!origModp) {
            if (AstIface* const ifacep = VN_CAST(curModp, Iface)) {
                resolveInterfacePath(ifacep);
                return;
            }
            curModp->fileline()->v3error("DPI-hook insertion of target '"
                                         << m_target
                                         << "' resolves to a non-module container, which is not"
                                            " supported");
            m_error = true;
            return;
        }
        // Record the generate-block prefix in source notation ("lane[0]") so the run-time
        // bind key can distinguish the unrolled copies
        if (!genScope.empty()) {
            for (auto& entry : m_targetp->entries) entry.genScope = genScope;
        }
        m_targetp->origModp = origModp;
        m_targetScopep = curScopep;
        collectTargetsInModule(origModp);
    }
    void resolveMemberPath(AstNodeModule* modp, const std::deque<string>& parts,
                           size_t boundaryIdx) {
        AstModule* const origModp = VN_CAST(modp, Module);
        if (!origModp) {
            if (VN_IS(modp, Iface)) {
                modp->fileline()->v3error(
                    "DPI-hook insertion of target '"
                    << m_target
                    << "': a member path into an interface signal is not supported (target the"
                       " whole signal instead)");
            } else {
                modp->fileline()->v3error("DPI-hook insertion of target '"
                                          << m_target
                                          << "' resolves to a non-module container, which is not"
                                             " supported");
            }
            m_error = true;
            return;
        }
        const auto [varName, varIdx] = parseComponent(parts[boundaryIdx]);
        AccessPath prefixSteps;
        if (varIdx) prefixSteps.push_back(StepIntoTarget{true, varIdx.value(), ""});
        for (size_t j = boundaryIdx + 1; j < parts.size(); ++j) {
            const auto [memberName, memberIdx] = parseComponent(parts[j]);
            prefixSteps.push_back(StepIntoTarget{false, 0, memberName});
            if (memberIdx) prefixSteps.push_back(StepIntoTarget{true, memberIdx.value(), ""});
        }
        for (auto& entry : m_targetp->entries) {
            AccessPath full = prefixSteps;
            full.push_back(StepIntoTarget{false, 0, entry.varTarget});  // the original last part
            for (const StepIntoTarget& step : entry.accessPath) full.push_back(step);
            entry.varTarget = varName;
            entry.accessPath = std::move(full);
        }
        m_targetp->origModp = origModp;
        m_targetScopep = origModp;
        collectTargetsInModule(origModp);
    }
    // Handle "top.b.data" where the prefix "top.b" resolves to an interface
    // Target signal `data` lives in interface, and its reads/drivers are
    // spread across every module connected to it
    // Therfore collection must be netlist-wide instead of scanning a single owning module
    void resolveInterfacePath(AstIface* ifacep) {
        m_targetp->ifacep = ifacep;
        for (size_t ei = 0; ei < m_targetp->entries.size(); ++ei) {
            const HookInsertEntry& entry = m_targetp->entries[ei];
            AstVar* const sigVarp = scopeChildVarp(ifacep, entry.varTarget);
            if (!sigVarp) {
                ifacep->fileline()->v3error("DPI-hook insertion of target '"
                                            << m_target << "': signal '" << entry.varTarget
                                            << "' not found in interface '" << ifacep->name()
                                            << "'");
                m_error = true;
                return;
            }
            AstNodeDType* const dtypep = sigVarp->dtypep()->skipRefp();
            const AstStructDType* const structp = VN_CAST(dtypep, StructDType);
            if (entry.hasMemberStep() || (structp && !structp->packed())
                || VN_IS(dtypep, UnpackArrayDType)) {
                sigVarp->fileline()->v3error(
                    "DPI-hook insertion of target '"
                    << m_target << "." << entry.varTarget
                    << "': aggregate or member-addressed interface signals are not supported;"
                       " target a packed leaf signal");
                m_error = true;
                return;
            }
            processTargetVar(sigVarp, entry, ei);
        }
        if (!m_foundVar) {
            m_error = true;
            return;
        }
        collectIfaceRefs();
    }
    void collectIfaceRefs() {
        for (AstNodeModule* modp = m_netlistp->modulesp(); modp;
             modp = VN_AS(modp->nextp(), NodeModule)) {
            modp->foreach([&](AstNode* nodep) {
                AstNodeVarRef* const refp = VN_CAST(nodep, NodeVarRef);
                if (!refp) return;
                for (auto& entry : m_targetp->entries) {
                    if (!entry.origVarp || refp->varp() != entry.origVarp) continue;
                    if (refp->access().isRW()) {
                        refp->fileline()->v3error(
                            "DPI-hook insertion of target '"
                            << m_target << "." << entry.varTarget
                            << "': a read-write reference to an interface signal is not"
                               " supported");
                        m_error = true;
                    } else if (refp->access().isWriteOnly()) {
                        entry.writeRefps.push_back(refp);
                    } else {
                        entry.readRefps.push_back(refp);
                    }
                    return;
                }
            });
        }
        for (const auto& entry : m_targetp->entries) {
            UINFO(4, "Iface target '" << m_target << "." << entry.varTarget
                                      << "': " << entry.readRefps.size() << " read ref(s), "
                                      << entry.writeRefps.size() << " driver ref(s)" << endl);
        }
    }
    void collectTargetsInModule(AstModule* origModp) {
        m_targetModp = origModp;
        std::vector<AstVar*> targetVarps;
        for (AstNode* declp = scopeDeclsp(m_targetScopep); declp; declp = declp->nextp()) {
            AstVar* const varp = VN_CAST(declp, Var);
            if (!varp || varp->isFuncLocal()) continue;
            for (const auto& entry : m_targetp->entries)
                if (varp->name() == entry.varTarget) {
                    targetVarps.push_back(varp);
                    break;
                }
        }
        for (AstVar* const varp : targetVarps)
            for (size_t ei = 0; ei < m_targetp->entries.size(); ++ei)
                if (varp->name() == m_targetp->entries[ei].varTarget)
                    processTargetVar(varp, m_targetp->entries[ei], ei);
        origModp->foreach([&](AstNode* declp) {
            AstNodeAssign* const assignp = VN_CAST(declp, NodeAssign);
            if (!assignp) return;
            for (const auto& entry : m_targetp->entries)
                if (entry.origVarp && !entry.isAggregateMirror && !entry.hasMemberStep()
                    && !entry.origVarp->isOutputish())
                    collectAssign(assignp, entry.origVarp, entry.varTarget);
        });
        origModp->foreach([&](AstNode* declp) {
            AstNodeVarRef* const refp = VN_CAST(declp, NodeVarRef);
            if (!refp || refp->varp()->isFuncLocal() || refp->access() != VAccess::READ) return;
            if (isPartOfAssign(refp)) return;
            for (const auto& entry : m_targetp->entries) {
                if (entry.isAggregateMirror || entry.hasMemberStep()) continue;
                if (entry.origVarp && refp->varp() == entry.origVarp)
                    addReadRef(refp, entry.varTarget);
            }
        });
        for (AstNodeModule* modp = m_netlistp->modulesp(); modp;
             modp = VN_AS(modp->nextp(), NodeModule)) {
            if (modp == origModp) continue;
            modp->foreach([&](AstNode* declp) {
                AstVarXRef* const xrefp = VN_CAST(declp, VarXRef);
                if (!xrefp || xrefp->access() != VAccess::READ) return;
                for (auto& entry : m_targetp->entries) {
                    if (entry.isAggregateMirror || entry.hasMemberStep()) continue;
                    if (entry.origVarp && xrefp->varp() == entry.origVarp)
                        entry.readXrefps.push_back(xrefp);
                }
            });
        }
        if (!m_foundVar && V3Error::errorCount() == m_errCountAtTarget)
            origModp->fileline()->v3error("DPI-hook insertion of target '"
                                          << m_target
                                          << "' could not find 'var' in '__.instance.var'");
    }
    void buildAggregateMirror(AstVar* aggregateVarp, const std::vector<AstNodeExpr*>& leafps,
                              const std::vector<int>& widths, int totalW) {
        FileLine* const fl = aggregateVarp->fileline();
        AstNodeDType* const mirrorDTypep = aggregateVarp->findLogicRangeDType(
            VNumRange{totalW - 1, 0}, totalW, VSigning::NOSIGN);
        // Generate blocks are flattened into the module, so the scope keeps the mirrors of
        // same-named aggregates in different blocks apart
        string scopeSuffix;
        for (const auto& entry : m_targetp->entries)
            if (entry.varTarget == aggregateVarp->name()) scopeSuffix = entry.genScopeSuffix();
        AstVar* const mirrorVarp = new AstVar{
            fl, VVarType::VAR, aggregateVarp->name() + scopeSuffix + "__DPImirror", mirrorDTypep};
        mirrorVarp->lifetime(VLifetime::STATIC_IMPLICIT);
        mirrorVarp->trace(false);
        m_targetModp->addStmtsp(mirrorVarp);
        // Build pack concat {f0, f1, ...} with first-declared member as MSB (packed-struct conv.)
        // All dtypes are set manually because V3Width has already run and will not revisit
        AstNodeExpr* concatp = nullptr;
        int accW = 0;
        for (size_t k = leafps.size(); k-- > 0;) {
            accW += widths[k];
            if (!concatp) {
                concatp = leafps[k];
            } else {
                AstConcat* const newConcatp = new AstConcat{fl, leafps[k], concatp};
                newConcatp->dtypep(aggregateVarp->findLogicRangeDType(VNumRange{accW - 1, 0}, accW,
                                                                      VSigning::NOSIGN));
                concatp = newConcatp;
            }
        }
        AstAssignW* const packAssignp
            = new AstAssignW{fl, new AstVarRef{fl, mirrorVarp, VAccess::WRITE}, concatp};
        // Wrap continuous pack-assign in a CONT_ASSIGN always
        // Matches how element-view assign is emitted
        // Bare module-level AssignW is not used by V3Active -> leafps VarRefs outside any func
        m_targetModp->addStmtsp(new AstAlways{fl, VAlwaysKwd::CONT_ASSIGN, nullptr, packAssignp});
        for (auto& entry : m_targetp->entries) {
            if (entry.varTarget == aggregateVarp->name()) {
                entry.origVarp = mirrorVarp;
                entry.hookedName = "dpiHooked_" + mirrorVarp->name();
                entry.hookedDTypep = nullptr;
                entry.found = true;
                entry.isAggregateMirror = true;
                entry.aggregateVarp = aggregateVarp;
            }
        }
    }
    // Most leaves an unpacked aggregate may flatten to and still be hooked as a whole
    static constexpr int DPIHOOK_MAX_AGGREGATE_LEAVES = 256;
    void expandUnpackedAggregateToMirror(AstVar* aggregateVarp) {
        AstNodeDType* const dtypep = aggregateVarp->dtypep()->skipRefp();
        const int nLeaves = aggregateLeafCount(dtypep);
        if (nLeaves > DPIHOOK_MAX_AGGREGATE_LEAVES) {
            aggregateVarp->fileline()->v3error(
                "Target variable '"
                << aggregateVarp->name() << "' in '" << m_curHier << "' flattens to " << nLeaves
                << " leaves, too large to hook as a whole (limit " << DPIHOOK_MAX_AGGREGATE_LEAVES
                << "); target individual elements instead");
            return;
        }
        std::vector<AstNodeExpr*> leafps;
        std::vector<int> widths;
        collectLeafAccesses(new AstVarRef{aggregateVarp->fileline(), aggregateVarp, VAccess::READ},
                            dtypep, leafps, widths);
        buildAggregateMirror(aggregateVarp, leafps, widths, aggregateBitWidth(dtypep));
    }
    // Whether a hook can carry a value of `dtypep`, the type of the target `what` ("v", "u.a",
    // or a leaf of an aggregate)
    bool checkHookableType(AstVar* targetVarp, const string& what, AstNodeDType* dtypep) {
        const AstBasicDType* const basicp = dtypep->basicp();
        if (!basicp || isDynamicContainer(dtypep->skipRefp())) {
            targetVarp->fileline()->v3error(
                "Target variable '" << what << "' in '" << m_curHier
                                    << "' has an unpacked or aggregate type that cannot be hooked"
                                       " directly; only packed (bit-vector) types are supported");
            return false;
        }
        if (!basicp->isLiteralType()) {
            targetVarp->fileline()->v3error("Target variable '" << what << "' in '" << m_curHier
                                                                << "' must be a supported type");
            return false;
        }
        if (basicp->isDouble()) {
            targetVarp->fileline()->v3error("Target variable '"
                                            << what << "' in '" << m_curHier
                                            << "' is a floating-point type, which has no"
                                               " gate-level representation and cannot be hooked");
            return false;
        }
        return true;
    }
    bool isReadInSensitivity(AstVar* targetVarp, const HookInsertEntry& entry) {
        const string what = targetVarp->name() + entry.accessPathText();
        const ClockUseVisitor clockUse{m_netlistp, targetVarp,
                                       accessChainSteps(targetVarp, entry.accessPath)};
        if (clockUse.isClock()) {
            targetVarp->fileline()->v3error(
                "Target variable '"
                << what << "' in '" << m_curHier
                << "' is used as a clock or asynchronous reset (it appears in an"
                   " edge-sensitive sensitivity list); hooking such a signal is not"
                   " supported");
            return true;
        }
        if (clockUse.isEventControl()) {
            // The block would keep waiting on the unhooked value
            targetVarp->fileline()->v3error(
                "Target variable '" << what << "' in '" << m_curHier
                                    << "' is read in an event control without an edge"
                                       " (e.g. 'always @("
                                    << targetVarp->prettyName() << entry.accessPathText()
                                    << " or ...)'); hooking such a signal is not supported");
            return true;
        }
        return false;
    }
    AstNodeDType* resolveLeafDTypep(AstVar* varp, const AccessPath& path) {
        AstNodeDType* dtypep = varp->dtypep()->skipRefp();
        for (const StepIntoTarget& step : path) {
            if (step.isIndex) {
                AstUnpackArrayDType* const adtypep = VN_CAST(dtypep, UnpackArrayDType);
                if (!adtypep) {
                    varp->fileline()->v3error(
                        "DPI-hook target '"
                        << varp->name() << "' in '" << m_curHier << "': index [" << step.index
                        << "] applied to " << dtypep->prettyDTypeNameQ()
                        << "; element access is supported on unpacked arrays only");
                    return nullptr;
                }
                if (!isElemIndexInRange(adtypep, step.index)) {
                    varp->fileline()->v3error("DPI-hook target '"
                                              << varp->name() << "' in '" << m_curHier
                                              << "': element index " << step.index
                                              << " out of range (" << adtypep->elementsConst()
                                              << " elements)");
                    return nullptr;
                }
                dtypep = adtypep->subDTypep()->skipRefp();
            } else {
                AstStructDType* const structp = VN_CAST(dtypep, StructDType);
                if (!structp) {
                    varp->fileline()->v3error("DPI-hook target '"
                                              << varp->name() << "' in '" << m_curHier
                                              << "': member '." << step.member << "' of "
                                              << dtypep->prettyDTypeNameQ()
                                              << "; member access is supported on structs only");
                    return nullptr;
                }
                AstNodeDType* memberDTypep = nullptr;
                for (AstMemberDType* memberp = structp->membersp(); memberp && !memberDTypep;
                     memberp = VN_CAST(memberp->nextp(), MemberDType))
                    if (memberp->name() == step.member) memberDTypep = memberp->subDTypep();
                if (!memberDTypep) {
                    varp->fileline()->v3error("DPI-hook target '"
                                              << varp->name() << "' in '" << m_curHier
                                              << "': no member named '" << step.member << "'");
                    return nullptr;
                }
                dtypep = memberDTypep->skipRefp();
            }
        }
        return dtypep;
    }
    void processTargetVar(AstVar* targetVarp, const HookInsertEntry& entry, size_t entryIdx) {
        const string what = targetVarp->name() + entry.accessPathText();
        if (entry.hasMemberStep()) {
            AstNodeDType* const leafDTypep = resolveLeafDTypep(targetVarp, entry.accessPath);
            if (!leafDTypep) return;  // error already emitted
            if (!isAggregateLeafDType(leafDTypep)) {
                targetVarp->fileline()->v3error(
                    "DPI-hook target '"
                    << targetVarp->name() << "' in '" << m_curHier
                    << "': the addressed member is an unpacked aggregate, which is not"
                       " supported; target a scalar or packed leaf");
                return;
            }
            if (!checkHookableType(targetVarp, what, leafDTypep)) return;
            if (isReadInSensitivity(targetVarp, entry)) return;
            const string leafName = "dpiHooked_" + targetVarp->name() + entry.accessPathSuffix()
                                    + entry.genScopeSuffix();
            setVarAt(entryIdx, targetVarp, leafName, leafDTypep);
            m_foundVar = true;
            return;
        }
        AstNodeDType* const dtypep = targetVarp->dtypep()->skipRefp();
        AstStructDType* const structp = VN_CAST(dtypep, StructDType);
        const bool wholeAggregate
            = !entry.elemIndex()
              && ((structp && !structp->packed()) || VN_IS(dtypep, UnpackArrayDType));
        if (wholeAggregate) {
            string leafPath;
            if (AstNodeDType* const leafDTypep = unhookableLeafDTypep(dtypep, leafPath)) {
                checkHookableType(targetVarp, targetVarp->name() + leafPath, leafDTypep);
                return;
            }
            if (isReadInSensitivity(targetVarp, entry)) return;
            expandUnpackedAggregateToMirror(targetVarp);
            m_foundVar = true;
            return;
        }
        AstUnpackArrayDType* const adtypep = VN_CAST(dtypep, UnpackArrayDType);
        if (entry.elemIndex() && !adtypep) {
            targetVarp->fileline()->v3error(
                "DPI-hook target '" << targetVarp->name() << "' in '" << m_curHier << "': index ["
                                    << entry.elemIndex().value() << "] applied to "
                                    << targetVarp->dtypep()->skipRefp()->prettyDTypeNameQ()
                                    << "; element access is supported on unpacked arrays"
                                       " only. Hook the whole signal instead");
            return;
        }
        if (entry.elemIndex() && adtypep
            && !isElemIndexInRange(adtypep, entry.elemIndex().value())) {
            targetVarp->fileline()->v3error("Element index "
                                            << entry.elemIndex().value()
                                            << " is out of range for target variable '"
                                            << targetVarp->name() << "' in '" << m_curHier << "' ("
                                            << adtypep->elementsConst() << " elements)");
            return;
        }
        AstNodeDType* const valueDTypep = entry.elemIndex() ? adtypep->subDTypep() : dtypep;
        if (!checkHookableType(targetVarp, what, valueDTypep)) return;
        if (isReadInSensitivity(targetVarp, entry)) return;
        const string hookedName = "dpiHooked_" + targetVarp->name() + entry.accessPathSuffix()
                                  + entry.genScopeSuffix();
        setVarAt(entryIdx, targetVarp, hookedName,
                 entry.elemIndex() && adtypep ? adtypep->subDTypep() : nullptr);
        m_foundVar = true;
    }

public:
    // CONSTRUCTOR
    //-------------------------------------------------------------------------------
    explicit HookInsertTargetFinder(AstNetlist* netlistp,
                                    std::map<string, HookInsertTarget>& insertCfg)
        : m_netlistp{netlistp}
        , m_insertCfg{insertCfg} {
        for (auto& pair : m_insertCfg) {
            // Reset the per-target state
            m_target = pair.first;
            m_targetp = &pair.second;
            m_curHier = "";
            m_targetModp = nullptr;
            m_foundVar = false;
            m_error = false;
            m_errCountAtTarget = V3Error::errorCount();
            navigateToTarget();
            if (m_error) m_targetp->error = true;
        }
    }
    ~HookInsertTargetFinder() = default;
};

//######################################################################
// Do the hook-insertion transformations

class HookPathRouter final {
    // MEMBERS
    AstNetlist* m_netlistp = nullptr;  // Netlist being transformed
    DTypeCache& m_dtypeCache;  // Dtypes shared by all targets
    HookInsertTarget& m_insertTarget;  // Target whose control signals are routed
    std::unordered_map<AstNodeModule*, AstCase*>& m_caseCache;  // Path-filter case of each module
    std::unordered_map<AstNodeModule*, AstVar*>& m_loopVarCache;  // Shared path-filter loop idxs
    std::unordered_map<AstNodeModule*, std::set<string>>&
        m_caseChildCells;  // Instances (flat names) with a path-filter case item

    // METHODS
    AstLoop* finalizeLoopp(AstLoop* loopp, AstVar* dpiTriggerVarp) {
        AstVarRef* const triggerReadRefp
            = new AstVarRef{loopp->fileline(), dpiTriggerVarp, VAccess::READ};
        AstVarRef* const triggerWriteRefp
            = new AstVarRef{loopp->fileline(), dpiTriggerVarp, VAccess::WRITE};

        AstLogNot* const logNotp = new AstLogNot{loopp->fileline(), triggerReadRefp};
        AstAssign* const assignp = new AstAssign{loopp->fileline(), triggerWriteRefp, logNotp};
        AstBegin* const initialBeginp = new AstBegin{loopp->fileline(), "", assignp, false};
        // The trigger re-evaluates time-based faults every `step` time units
        const uint32_t step = static_cast<uint32_t>(v3Global.opt.dpiHookTriggerStep());
        AstConst* const timeStepConstp
            = new AstConst{loopp->fileline(), AstConst::WidthedValue{}, 64, step};
        AstDelay* const delayp = new AstDelay{loopp->fileline(), timeStepConstp, false};
        delayp->timeunit(m_netlistp->timeunit());
        initialBeginp->addStmtsp(delayp);
        loopp->addStmtsp(initialBeginp);
        return loopp;
    }
    AstVar* insertCaseIdInputVarp(AstNodeModule* modp) {
        AstTypeTable* const typeTablep = VN_CAST(m_netlistp->miscsp(), TypeTable);
        AstBasicDType* const elemDTypep
            = new AstBasicDType{modp->fileline(), VBasicDTypeKwd::INT, VSigning::SIGNED};
        elemDTypep->generic(true);
        typeTablep->addTypesp(elemDTypep);
        AstUnpackArrayDType* const arrDTypep = new AstUnpackArrayDType{
            modp->fileline(), elemDTypep, new AstRange{modp->fileline(), dpiHookSlots() - 1, 0}};
        typeTablep->addTypesp(arrDTypep);
        const bool isIface = VN_IS(modp, Iface);
        AstVar* const caseIdInputVarp
            = new AstVar{modp->fileline(), isIface ? VVarType::VAR : VVarType::PORT,
                         "DPIHOOK_CASE_ID", arrDTypep};
        caseIdInputVarp->lifetime(VLifetime::STATIC_IMPLICIT);
        if (!isIface) caseIdInputVarp->direction(VDirection::INPUT);
        caseIdInputVarp->trace(false);
        modp->addStmtsp(caseIdInputVarp);
        return caseIdInputVarp;
    }
    AstVar* insertHookPathVarp(AstNodeModule* modp, int idx) {
        const bool isInitMod
            = !m_insertTarget.modps.empty() && m_insertTarget.modps.front() == modp;
        const bool isOrigMod = m_insertTarget.hookLogicContainerp() == modp;
        AstVar* const hookPathVarp = newHookPathVarp(modp, idx, isInitMod, isOrigMod);
        modp->addStmtsp(hookPathVarp);
        return hookPathVarp;
    }
    AstVar* newHookPathVarp(AstNodeModule* modp, int idx, bool isInitMod = false,
                            bool isOrigMod = false) {
        AstTypeTable* const typeTablep = VN_CAST(m_netlistp->miscsp(), TypeTable);
        // Generate necessary dtype for Path Varps and Pinsp
        if (!m_dtypeCache.stringDTypep) {
            m_dtypeCache.stringDTypep
                = new AstBasicDType{modp->fileline(), VBasicDTypeKwd::STRING};
            m_dtypeCache.stringDTypep->generic(true);
            typeTablep->addTypesp(m_dtypeCache.stringDTypep);
        }
        const bool isIface = VN_IS(modp, Iface);
        AstVar* const hookPathVarp
            = new AstVar{modp->fileline(), isIface ? VVarType::VAR : VVarType::PORT,
                         "DPIHOOK_PATH", m_dtypeCache.stringDTypep};
        if (!isIface) hookPathVarp->direction(VDirection::INPUT);
        hookPathVarp->lifetime(VLifetime::STATIC_IMPLICIT);
        hookPathVarp->trace(false);
        if (isOrigMod) {
            AstUnpackArrayDType* const partsDTypep = new AstUnpackArrayDType{
                modp->fileline(), m_dtypeCache.stringDTypep, new AstRange{modp->fileline(), 0, 0}};
            partsDTypep->isCompound(true);
            AstUnpackArrayDType* const pathsDTypep
                = new AstUnpackArrayDType{modp->fileline(), m_dtypeCache.stringDTypep,
                                          new AstRange{modp->fileline(), dpiHookSlots() - 1, 0}};
            pathsDTypep->isCompound(true);
            pathsDTypep->refDTypep(partsDTypep);
            typeTablep->addTypesp(partsDTypep);
            typeTablep->addTypesp(pathsDTypep);
            hookPathVarp->dtypep(pathsDTypep);
            return hookPathVarp;
        }
        const int targetParts
            = m_insertTarget.modps.size();  // Target part amount for left range value
        AstRange* const rangep = isInitMod ? new AstRange{modp->fileline(), targetParts, 0}
                                           : new AstRange{modp->fileline(), targetParts - idx, 0};
        AstUnpackArrayDType* const partsDTypep
            = new AstUnpackArrayDType{modp->fileline(), m_dtypeCache.stringDTypep, rangep};
        partsDTypep->isCompound(true);
        AstUnpackArrayDType* const pathsDTypep
            = new AstUnpackArrayDType{modp->fileline(), m_dtypeCache.stringDTypep,
                                      new AstRange{modp->fileline(), dpiHookSlots() - 1, 0}};
        pathsDTypep->isCompound(true);
        pathsDTypep->refDTypep(partsDTypep);
        typeTablep->addTypesp(partsDTypep);
        typeTablep->addTypesp(pathsDTypep);
        hookPathVarp->dtypep(pathsDTypep);
        return hookPathVarp;
    }
    AstVar* findExistingInputVarp(AstNodeModule* modp, const string& name) {
        const bool isIface = VN_IS(modp, Iface);
        for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            AstVar* const varp = VN_CAST(stmtp, Var);
            if (!varp) continue;
            if (varp->name() == name && (varp->isInput() || isIface)) return varp;
        }
        return nullptr;
    }
    bool hasDpiTrigger() {
        AstNodeModule* const origModp = m_insertTarget.hookLogicContainerp();
        for (AstNode* stmtp = origModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            AstVar* const varp = VN_CAST(stmtp, Var);
            if (!varp) continue;
            if (varp->name() == "DPI_TRIGGER") {
                m_insertTarget.dpiTriggerVarp = varp;
                return true;
            }
        }
        return false;
    }
    bool hasPathFilter(AstNodeModule* modp) { return m_caseCache.count(modp) != 0; }
    bool hasInputPin(AstCell* cellp, const string& pinName) {
        for (const AstNode* pinp = cellp->pinsp(); pinp; pinp = pinp->nextp()) {
            if (pinp->name() == pinName) return true;
        }
        return false;
    }
    void insertCaseItems(AstNodeModule* modp, AstCase* casep, AstVar* hookPathVarp,
                         AstVar* loopVarp, int idx, InstPathMap& instPathVarps) {
        AstTypeTable* const typeTablep = VN_CAST(m_netlistp->miscsp(), TypeTable);
        const int nextIdx = idx + 1;  // Increase index by one to account for this variable
                                      // referencing the next module/instance
        for (AstCell* cellp : m_insertTarget.cellps) {
            if (cellOwnerModp(cellp) != modp) continue;
            const string cellFlatNm = cellFlatName(cellp);
            // One item per instance, also when several targets route through it
            if (!m_caseChildCells[modp].insert(cellFlatNm).second) continue;
            const string cellPath = AstNode::prettyName(cellFlatNm);
            // Add Instance Variable
            const int targetParts
                = m_insertTarget.modps.size();  // Target part amount for left range value
            AstRange* const rangep = new AstRange{modp->fileline(), targetParts - nextIdx, 0};
            AstUnpackArrayDType* const partsDTypep
                = new AstUnpackArrayDType{modp->fileline(), m_dtypeCache.stringDTypep, rangep};
            partsDTypep->isCompound(true);
            AstUnpackArrayDType* const pathsDTypep
                = new AstUnpackArrayDType{modp->fileline(), partsDTypep,
                                          new AstRange{modp->fileline(), dpiHookSlots() - 1, 0}};
            pathsDTypep->isCompound(true);
            pathsDTypep->refDTypep(partsDTypep);
            AstVar* const instPathVarp = new AstVar{modp->fileline(), VVarType::VAR,
                                                    "DPIPATH_" + cellFlatNm, pathsDTypep};
            instPathVarp->lifetime(VLifetime::STATIC_IMPLICIT);
            typeTablep->addTypesp(partsDTypep);
            typeTablep->addTypesp(pathsDTypep);
            modp->addStmtsp(instPathVarp);
            instPathVarps[InstPathKey{modp, cellFlatNm}] = instPathVarp;
            for (uint32_t part = 0; part <= static_cast<uint32_t>(targetParts - nextIdx); ++part) {
                AstArraySel* const slotSelp = new AstArraySel{
                    modp->fileline(),
                    new AstVarRef{modp->fileline(), instPathVarp, VAccess::WRITE},
                    new AstVarRef{modp->fileline(), loopVarp, VAccess::READ}};
                slotSelp->dtypep(partsDTypep);
                AstArraySel* const slotPartSelp = new AstArraySel{
                    modp->fileline(), slotSelp, new AstConst{modp->fileline(), part}};
                slotPartSelp->dtypep(m_dtypeCache.stringDTypep);
                AstConst* const emptyConstp
                    = new AstConst{modp->fileline(), AstConst::VerilogStringLiteral{}, ""};
                AstCvtPackString* const emptyStrp
                    = new AstCvtPackString{modp->fileline(), emptyConstp};
                emptyStrp->dtypep(m_dtypeCache.stringDTypep);
                casep->addHereThisAsNext(new AstAssign{modp->fileline(), slotPartSelp, emptyStrp});
            }
            // Add Case Item
            AstConst* const cellPathConstp
                = new AstConst{modp->fileline(), AstConst::VerilogStringLiteral{}, cellPath};
            AstCvtPackString* const cvtPackStringp
                = new AstCvtPackString{modp->fileline(), cellPathConstp};
            cvtPackStringp->dtypep(m_dtypeCache.stringDTypep);
            AstVarRef* const hookPathRefp
                = new AstVarRef{modp->fileline(), hookPathVarp, VAccess::READ};
            AstArraySel* const partSelp
                = new AstArraySel{modp->fileline(), hookPathRefp,
                                  new AstVarRef{modp->fileline(), loopVarp, VAccess::READ}};
            if (!m_dtypeCache.partSelDTypep) {
                AstUnpackArrayDType* const partSelDTypep = new AstUnpackArrayDType{
                    modp->fileline(), m_dtypeCache.stringDTypep,
                    new AstRange{modp->fileline(), targetParts - idx, 0}};
                partSelDTypep->isCompound(true);
                typeTablep->addTypesp(partSelDTypep);
                m_dtypeCache.partSelDTypep = partSelDTypep;
            }
            partSelp->dtypep(m_dtypeCache.partSelDTypep);
            // Element [0] is the path part used by the case match, so forward remains [hi:1]
            AstSliceSel* const sliceSelp
                = new AstSliceSel{modp->fileline(), partSelp, VNumRange{targetParts - idx, 1}};
            AstRange* const sliceSelRangep = new AstRange{modp->fileline(), targetParts - idx, 1};
            AstUnpackArrayDType* const sliceSelDTypep = new AstUnpackArrayDType{
                modp->fileline(), m_dtypeCache.stringDTypep, sliceSelRangep};
            sliceSelDTypep->isCompound(true);
            sliceSelp->dtypep(sliceSelDTypep);
            typeTablep->addTypesp(sliceSelDTypep);
            AstVarRef* const instPathWriteRefp
                = new AstVarRef{modp->fileline(), instPathVarp, VAccess::WRITE};
            AstArraySel* const instPathSelp
                = new AstArraySel{modp->fileline(), instPathWriteRefp,
                                  new AstVarRef{modp->fileline(), loopVarp, VAccess::READ}};
            instPathSelp->dtypep(partsDTypep);
            AstAssign* const assignp = new AstAssign{modp->fileline(), instPathSelp, sliceSelp};
            // Single remaining part -> instance is last jump
            if (targetParts - idx == 1) {
                AstCaseItem* const caseItemp
                    = new AstCaseItem{modp->fileline(), cvtPackStringp, assignp};
                casep->addItemsp(caseItemp);
                continue;
            }
            AstBegin* const beginp = new AstBegin{modp->fileline(), "", assignp, false};
            AstCaseItem* const caseItemp
                = new AstCaseItem{modp->fileline(), cvtPackStringp, beginp};
            casep->addItemsp(caseItemp);
        }
    }
    void insertCaseIdPin(AstCell* cellp, int idx, const std::vector<AstVar*>& caseIdInputVarps) {
        int pinNum = 0;
        for (AstNode* existingPinp = cellp->pinsp(); existingPinp;
             existingPinp = existingPinp->nextp())
            pinNum++;
        AstVarRef* const caseIdRefp
            = new AstVarRef{cellp->fileline(), caseIdInputVarps[idx], VAccess::READ};
        AstPin* const pinp = new AstPin{cellp->fileline(), pinNum, "DPIHOOK_CASE_ID", caseIdRefp};
        pinp->modVarp(caseIdInputVarps[idx + 1]);
        pinp->svDotName(true);
        cellp->addPinsp(pinp);
    }
    void insertPathFilter(AstNodeModule* modp, AstVar* hookPathVarp, int idx,
                          InstPathMap& instPathVarps) {
        AstTypeTable* const typeTablep = VN_CAST(m_netlistp->miscsp(), TypeTable);
        // Add filter logic providing path information to the modules/instances
        // Ensure the shared signed-int dtype for the loop index exists
        if (!m_dtypeCache.intDTypep) {
            m_dtypeCache.intDTypep
                = new AstBasicDType{modp->fileline(), VBasicDTypeKwd::INT, VSigning::SIGNED};
            m_dtypeCache.intDTypep->generic(true);
            typeTablep->addTypesp(m_dtypeCache.intDTypep);
        }
        PathFilterConfig cfg;
        cfg.modp = modp;
        cfg.intDTypep = m_dtypeCache.intDTypep;
        cfg.stringDTypep = m_dtypeCache.stringDTypep;
        cfg.hookPathVarp = hookPathVarp;
        cfg.targetVarName = "DPITARGETPATH";
        cfg.targetVarLifetime = VLifetime::STATIC_IMPLICIT;
        cfg.targetVarHasUserInit = false;
        cfg.declTargetInLoopBody = false;  // declared in the always body
        cfg.alwaysName = "DPIHOOK_PATH_FILTER";
        cfg.caseCachep = &m_caseCache;
        cfg.loopVarCachep = &m_loopVarCache;
        const PathFilterResult res = buildPathFilter(cfg);
        insertCaseItems(modp, res.casep, hookPathVarp, res.loopVarp, idx, instPathVarps);
        res.partSelp->dtypep(m_dtypeCache.partSelDTypep);
    }
    void insertCaseItemsIntoExisting(AstNodeModule* modp, AstVar* hookPathVarp, int idx,
                                     InstPathMap& instPathVarps) {
        AstCase* const casep = m_caseCache.at(modp);
        insertCaseItems(modp, casep, hookPathVarp, m_loopVarCache.at(modp), idx, instPathVarps);
    }
    void insertHookPathPin(AstCell* cellp, int idx, const std::vector<AstVar*>& hookPathVarps,
                           const InstPathMap& instPathVarps) {
        int pinNum = 0;
        for (AstNode* existingPinp = cellp->pinsp(); existingPinp;
             existingPinp = existingPinp->nextp())
            pinNum++;
        const auto it = instPathVarps.find(InstPathKey{cellOwnerModp(cellp), cellFlatName(cellp)});
        if (it != instPathVarps.end()) {
            AstVar* const instPathVarp = it->second;
            AstVarRef* const instPathRefp
                = new AstVarRef{cellp->fileline(), instPathVarp, VAccess::READ};
            AstPin* const pinp
                = new AstPin{cellp->fileline(), pinNum, "DPIHOOK_PATH", instPathRefp};
            pinp->modVarp(hookPathVarps[idx + 1]);
            pinp->svDotName(true);
            cellp->addPinsp(pinp);
        }
    }
    // Whether the parent already drives `ifaceVarp` through this instance
    bool hasIfaceCtrlAssign(AstNode* scopep, const AstVar* ifaceVarp, const string& cellName) {
        bool found = false;
        scopep->foreach([&](AstNode* nodep) {
            const AstVarXRef* const xrefp = VN_CAST(nodep, VarXRef);
            if (xrefp && xrefp->varp() == ifaceVarp && xrefp->dotted() == cellName
                && xrefp->access().isWriteOrRW())
                found = true;
        });
        return found;
    }
    void insertIfaceCtrlAssign(AstNodeModule* parentModp, AstCell* cellp, const string& instName,
                               AstVar* ifaceVarp, AstVar* srcVarp) {
        if (!ifaceVarp || !srcVarp) return;
        AstGenBlock* const genBlockp = cellGenBlockp(cellp);
        const string dotted = genBlockp ? flatNameTail(instName) : instName;
        AstNode* const scopep = genBlockp ? static_cast<AstNode*>(genBlockp) : parentModp;
        if (hasIfaceCtrlAssign(scopep, ifaceVarp, dotted)) return;
        FileLine* const fl = cellp->fileline();
        AstVarXRef* const lhsp = new AstVarXRef{fl, ifaceVarp, dotted, VAccess::WRITE};
        AstVarRef* const rhsp = new AstVarRef{fl, srcVarp, VAccess::READ};
        AstAssignW* const assignp = new AstAssignW{fl, lhsp, rhsp};
        AstAlways* const alwaysp = new AstAlways{fl, VAlwaysKwd::CONT_ASSIGN, nullptr, assignp};
        if (genBlockp) {
            genBlockp->addItemsp(alwaysp);
        } else {
            parentModp->addStmtsp(alwaysp);
        }
    }
    void insertCtrlLogicToIfaceCell(AstCell* cellp, int idx,
                                    const std::vector<AstVar*>& caseIdInputVarps,
                                    const InstPathMap& instPathVarps) {
        // The parent is a module, or an interface holding a nested interface
        AstNodeModule* const parentModp = cellOwnerModp(cellp);
        AstIface* const ifacep = VN_AS(cellp->modp(), Iface);
        // An interface array is already expanded into one cell per element here
        const string instName = cellFlatName(cellp);
        insertIfaceCtrlAssign(parentModp, cellp, instName,
                              findExistingInputVarp(ifacep, "DPIHOOK_CASE_ID"),
                              caseIdInputVarps[idx]);
        const auto pathIt = instPathVarps.find(InstPathKey{parentModp, instName});
        insertIfaceCtrlAssign(parentModp, cellp, instName,
                              findExistingInputVarp(ifacep, "DPIHOOK_PATH"),
                              pathIt == instPathVarps.end() ? nullptr : pathIt->second);
    }
    void insertCtrlLogicToCells(const std::vector<AstVar*>& caseIdInputVarps,
                                const std::vector<AstVar*>& hookPathVarps,
                                const InstPathMap& instPathVarps) {
        AstCell* prevCellp = nullptr;
        int idx = 0;
        for (AstCell* cellp : m_insertTarget.cellps) {
            if (prevCellp && cellp->modp() != prevCellp->modp()) idx++;
            if (VN_IS(cellp->modp(), Iface)) {
                insertCtrlLogicToIfaceCell(cellp, idx, caseIdInputVarps, instPathVarps);
            } else {
                if (!hasInputPin(cellp, "DPIHOOK_CASE_ID"))
                    insertCaseIdPin(cellp, idx, caseIdInputVarps);
                if (!hasInputPin(cellp, "DPIHOOK_PATH"))
                    insertHookPathPin(cellp, idx, hookPathVarps, instPathVarps);
            }
            prevCellp = cellp;
        }
    }
    void insertCtrlLogicToModules(std::vector<AstVar*>& caseIdInputVarps,
                                  std::vector<AstVar*>& hookPathVarps,
                                  InstPathMap& instPathVarps) {
        AstNodeModule* const origModp = m_insertTarget.hookLogicContainerp();
        size_t idx = 0;
        for (AstNodeModule* modp : m_insertTarget.modps) {
            AstVar* caseIdInputVarp = findExistingInputVarp(modp, "DPIHOOK_CASE_ID");
            if (!caseIdInputVarp) caseIdInputVarp = insertCaseIdInputVarp(modp);
            caseIdInputVarps.push_back(caseIdInputVarp);
            AstVar* hookPathVarp = findExistingInputVarp(modp, "DPIHOOK_PATH");
            if (!hookPathVarp) hookPathVarp = insertHookPathVarp(modp, idx);
            hookPathVarps.push_back(hookPathVarp);
            if (!hasPathFilter(modp)) {
                // First hook insert cfg -> build the filter and add its items
                insertPathFilter(modp, hookPathVarp, idx, instPathVarps);
            } else {
                // A sibling target already built the filter -> add the items of the
                // instances it does not route through yet
                insertCaseItemsIntoExisting(modp, hookPathVarp, idx, instPathVarps);
            }
            m_dtypeCache.partSelDTypep = nullptr;
            idx++;
        }
        AstVar* origCaseIdInputVarp = findExistingInputVarp(origModp, "DPIHOOK_CASE_ID");
        if (!origCaseIdInputVarp) origCaseIdInputVarp = insertCaseIdInputVarp(origModp);
        caseIdInputVarps.push_back(origCaseIdInputVarp);
        AstVar* origHookPathVarp = findExistingInputVarp(origModp, "DPIHOOK_PATH");
        if (!origHookPathVarp) origHookPathVarp = insertHookPathVarp(origModp, idx);
        hookPathVarps.push_back(origHookPathVarp);
    }
    void insertDpiTrigger() {
        AstNodeModule* const origModp = m_insertTarget.hookLogicContainerp();
        AstTypeTable* const typeTablep = VN_CAST(m_netlistp->miscsp(), TypeTable);
        AstBasicDType* const dpiTriggerDTypep
            = new AstBasicDType{origModp->fileline(), VBasicDTypeKwd::BIT, VSigning::NOSIGN};
        dpiTriggerDTypep->generic(true);
        typeTablep->addTypesp(dpiTriggerDTypep);
        AstVar* const dpiTriggerVarp
            = new AstVar{origModp->fileline(), VVarType::VAR, "DPI_TRIGGER", dpiTriggerDTypep};
        dpiTriggerVarp->lifetime(VLifetime::STATIC_IMPLICIT);
        dpiTriggerVarp->trace(false);
        m_insertTarget.dpiTriggerVarp = dpiTriggerVarp;
        origModp->addStmtsp(dpiTriggerVarp);
        AstLoop* const loopp = finalizeLoopp(new AstLoop{origModp->fileline()}, dpiTriggerVarp);
        AstBegin* const beginp = new AstBegin{origModp->fileline(), "", loopp, false};
        AstInitial* const initialp = new AstInitial{origModp->fileline(), beginp};
        origModp->addStmtsp(initialp);
    }

public:
    HookPathRouter(AstNetlist* netlistp, HookInsertTarget& insertTarget, DTypeCache& dtypeCache,
                   std::unordered_map<AstNodeModule*, AstCase*>& caseCache,
                   std::unordered_map<AstNodeModule*, AstVar*>& loopVarCache,
                   std::unordered_map<AstNodeModule*, std::set<string>>& caseChildCells)
        : m_netlistp{netlistp}
        , m_dtypeCache{dtypeCache}
        , m_insertTarget{insertTarget}
        , m_caseCache{caseCache}
        , m_loopVarCache{loopVarCache}
        , m_caseChildCells{caseChildCells} {}

    void insert() {
        std::vector<AstVar*> caseIdInputVarps;
        std::vector<AstVar*> hookPathVarps;
        InstPathMap instPathVarps;

        insertCtrlLogicToModules(caseIdInputVarps, hookPathVarps, instPathVarps);
        insertCtrlLogicToCells(caseIdInputVarps, hookPathVarps, instPathVarps);
        if (!hasDpiTrigger()) insertDpiTrigger();
    }
};

class DpiHookInserter final {
    // MEMBERS
    AstNetlist* m_netlistp;  // Netlist under transformation
    std::map<string, HookInsertTarget>& m_insertCfg;  // Resolved target configs

    // METHODS
    const HookInsertEntry* existingEntryp(AstNodeModule* modp, const HookInsertEntry& candidate) {
        for (const auto& [key, target] : m_insertCfg) {
            if (target.hookLogicContainerp() != modp) continue;
            for (const auto& entry : target.entries) {
                if (entry.done && entry.origVarp == candidate.origVarp
                    && entry.accessPath == candidate.accessPath)
                    return &entry;
            }
        }
        return nullptr;
    }

public:
    DpiHookInserter(AstNetlist* netlistp, std::map<string, HookInsertTarget>& insertCfg)
        : m_netlistp{netlistp}
        , m_insertCfg{insertCfg} {}

    void insertDpiHooks() {
        DTypeCache dtypeCache;
        std::unordered_map<AstNodeModule*, AstCase*> caseCache;
        std::unordered_map<AstNodeModule*, AstVar*> targetLoopVarCache;
        std::unordered_map<AstNodeModule*, std::set<string>> caseChildCells;
        std::vector<std::pair<string, HookInsertTarget*>> sortedCfg;
        for (auto& [key, target] : m_insertCfg) sortedCfg.emplace_back(key, &target);

        // descending Depth (Amount of elements in modps)
        std::sort(sortedCfg.begin(), sortedCfg.end(), [](const auto& a, const auto& b) {
            const size_t depthA = a.second->modps.size();
            const size_t depthB = b.second->modps.size();
            return depthA > depthB;  // bigger = deeper = earlier
        });
        for (auto& [key, target] : sortedCfg) {
            if (target->error) {
                m_netlistp->fileline()->v3error(
                    "Incomplete hook-insertion configuration for target '"
                    << key << "'; see the error above");
                return;
            }
            HookPathRouter pathRouter{m_netlistp,         *target,       dtypeCache, caseCache,
                                      targetLoopVarCache, caseChildCells};
            pathRouter.insert();
            // Validate all entries before sorting
            for (auto& entry : target->entries) {
                if (!entry.found) {
                    m_netlistp->fileline()->v3error(
                        "Incomplete hook-insertion configuration for target '"
                        << entry.origTarget << "'; see the error above");
                    return;
                }
            }
            // Insert hook logic for each entry
            for (auto& entry : target->entries) {
                AstVar* const origVarp = entry.origVarp;
                const HookInsertEntry* const priorp
                    = existingEntryp(target->hookLogicContainerp(), entry);
                if (!priorp) {
                    // Insert the hook logic for this entry
                } else if (priorp->callback != entry.callback) {
                    origVarp->v3error("DPI-hook target '" << entry.origTarget
                                                          << "' is already hooked with callback '"
                                                          << priorp->callback << "'");
                }
            }
        }
    }
};

//######################################################################
// Hook-insertion class functions

static std::map<string, HookInsertTarget> buildWorkingCfg() {
    std::map<string, HookInsertTarget> insertCfg;
    for (const auto& [targetName, cfgEntries] : V3Control::getHookInsertCfg()) {
        HookInsertTarget& target = insertCfg[targetName];
        for (const HookInsertCfgEntry& cfgEntry : cfgEntries) {
            HookInsertEntry entry;
            entry.callback = cfgEntry.callback;
            entry.varTarget = cfgEntry.varTarget;
            entry.accessPath = cfgEntry.accessPath;
            entry.origTarget = targetName + "." + cfgEntry.varTarget;
            for (const StepIntoTarget& step : cfgEntry.accessPath) {
                entry.origTarget
                    += step.isIndex ? "[" + std::to_string(step.index) + "]" : "." + step.member;
            }
            target.entries.push_back(std::move(entry));
        }
    }
    return insertCfg;
}

void V3InsertDPIHook::hookInsert(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    std::map<string, HookInsertTarget> insertCfg = buildWorkingCfg();
    // Finder phase: resolve the AST pointers for each configured target.
    { HookInsertTargetFinder{nodep, insertCfg}; }
    V3Global::dumpCheckGlobalTree("findDpiHookTarget", 0, dumpTreeEitherLevel() >= 3);
    V3Global::dumpCheckGlobalTree("insertDpiHook", 0, dumpTreeEitherLevel() >= 3);
}
