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

VL_DEFINE_DEBUG_FUNCTIONS;

// Widest value a DPI function may return (IEEE 1800 35.5.5) (wider targets use
// a task with an output argument instead)
static constexpr int DPIHOOK_MAX_FUNC_WIDTH = 64;

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
    DpiHookAccessPath
        accessPath;  // Member/index steps into the target var ("a.b[i]"); empty for scalars
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
    FileLine* cfgFl = nullptr;  // Location of the insert_dpihook directive
    bool hasElemIndex() const { return accessPath.size() == 1 && accessPath.front().isIndex; }
    uint32_t elemIndex() const { return accessPath.front().index; }
    bool hasMemberStep() const {
        for (const DpiHookStep& step : accessPath)
            if (!step.isIndex) return true;
        return false;
    }
    // Access path in source notation (".a", "[2].x"), used for messages
    string accessPathText() const {
        string s;
        for (const DpiHookStep& step : accessPath)
            s += step.isIndex ? ("[" + std::to_string(step.index) + "]") : ("." + step.member);
        return s;
    }
    // Name-safe suffix encoding for access path ("[2].x" -> "__05b2__05d__02ex")
    // Keeps per-leaf hook var names unique when several members of one struct var are hooked
    string accessPathSuffix() const {
        return accessPath.empty() ? "" : AstNode::encodeName(accessPathText());
    }
    // Generate name-safe suffix for generate-block scope ("lane[0]" -> "__040lane__05b0__05d")
    // Keeps hook var names unique across unrolled generate copies
    string genScopeSuffix() const {
        return genScope.empty() ? "" : AstNode::encodeName("@" + genScope);
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
struct HookLookups final {
    std::unordered_map<const AstNodeModule*, AstVar*> caseIdVarps;
    std::unordered_map<const AstNodeModule*, AstVar*> hookPathVarps;
    std::unordered_map<const AstNodeModule*, AstVar*> triggerVarps;
    std::set<std::pair<const AstCell*, string>> cellPins;
    std::unordered_map<const AstNodeModule*, std::unordered_map<string, AstNodeFTask*>> ftasks;
    static AstVar* varp(const std::unordered_map<const AstNodeModule*, AstVar*>& varps,
                        const AstNodeModule* modp) {
        const auto it = varps.find(modp);
        return it == varps.end() ? nullptr : it->second;
    }
    AstNodeFTask* ftaskp(const AstNodeModule* modp, const string& name) {
        auto it = ftasks.find(modp);
        if (it == ftasks.end()) {
            it = ftasks.emplace(modp, std::unordered_map<string, AstNodeFTask*>{}).first;
            for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp())
                if (AstNodeFTask* const ftaskp = VN_CAST(stmtp, NodeFTask))
                    it->second.emplace(ftaskp->name(), ftaskp);
        }
        const auto nameIt = it->second.find(name);
        return nameIt == it->second.end() ? nullptr : nameIt->second;
    }
};

//######################################################################
// Shared builder for the "path filter" always-block emitted by path router
// (HookPathRouter::insertPathFilter) and override builder
// (DpiOverrideBuilder::insertTargetFilterp).

struct PathFilterConfig final {
    AstNodeModule* modp = nullptr;  // Module/iface receiving the always block (also fileline src)
    AstBasicDType* intDTypep = nullptr;  // Signed-int dtype for the loop index (pre-registered)
    AstBasicDType* stringDTypep = nullptr;  // String dtype for the decoded part (pre-registered)
    AstVar* hookPathVarp = nullptr;  // __Vdpihook_path input being decoded
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
// A target path provided by the testbench that is not matched by any of the case item provides
// a warning
static void insertDefaultCases(const std::unordered_map<AstNodeModule*, AstCase*>& caseCache) {
    for (const auto& itr : caseCache) {
        AstNodeModule* const modp = itr.first;
        AstCase* const casep = itr.second;
        FileLine* const fl = casep->fileline();
        AstVar* const targetVarp = VN_AS(casep->exprp(), VarRef)->varp();
        AstConst* const emptyConstp = new AstConst{fl, AstConst::VerilogStringLiteral{}, ""};
        AstNeqN* const namedp = new AstNeqN{fl, new AstVarRef{fl, targetVarp, VAccess::READ},
                                            new AstCvtPackString{fl, emptyConstp}};
        AstDisplay* const warnp
            = new AstDisplay{fl, VDisplayType::DT_WARNING,
                             "DPI-hook: bound path part '%0s' matches nothing in '"
                                 + modp->prettyName() + "'; this target stays inactive",
                             nullptr, new AstVarRef{fl, targetVarp, VAccess::READ}};
        // A warning provides the simulation time
        warnp->fmtp()->timeunit(modp->timeunit());
        casep->addItemsp(new AstCaseItem{fl, nullptr, new AstIf{fl, namedp, warnp}});
    }
}
static AstNodeExpr* newAnyTargetBoundp(FileLine* fl, AstVar* hookPathVarp) {
    AstNodeExpr* boundp = nullptr;
    const int slots = dpiHookSlots();
    for (int idx = 0; idx < slots; ++idx) {
        AstArraySel* const partsSelp
            = new AstArraySel{fl, new AstVarRef{fl, hookPathVarp, VAccess::READ}, idx};
        AstConst* const emptyConstp = new AstConst{fl, AstConst::VerilogStringLiteral{}, ""};
        AstNeqN* const slotp = new AstNeqN{fl, new AstArraySel{fl, partsSelp, 0},
                                           new AstCvtPackString{fl, emptyConstp}};
        boundp = boundp ? static_cast<AstNodeExpr*>(new AstLogOr{fl, boundp, slotp}) : slotp;
    }
    return boundp;
}
// The path filter samples __Vdpihook_path once, at time zero (see buildPathFilter), so a
// testbench that binds after the first eval() hooks nothing at all. Without a check that
// mistake is silent, so latch at time zero whether anything was bound and compare at the
// end of the simulation. Both ends run once, outside of any eval.
static void insertBindCheck(AstNetlist* netlistp, const HookLookups& lookups) {
    AstNodeModule* const topModp = netlistp->topModulep();
    AstVar* const hookPathVarp = HookLookups::varp(lookups.hookPathVarps, topModp);
    UASSERT_OBJ(hookPathVarp, topModp, "DPI-hook: path input missing in top module");
    AstTypeTable* const typeTablep = VN_CAST(netlistp->miscsp(), TypeTable);
    FileLine* const fl = topModp->fileline();
    AstBasicDType* const bitDTypep = new AstBasicDType{fl, VBasicDTypeKwd::BIT, VSigning::NOSIGN};
    bitDTypep->generic(true);
    typeTablep->addTypesp(bitDTypep);
    AstVar* const boundVarp = new AstVar{fl, VVarType::VAR, "__Vdpihook_bound", bitDTypep};
    boundVarp->lifetime(VLifetime::STATIC_IMPLICIT);
    boundVarp->trace(false);
    topModp->addStmtsp(boundVarp);
    topModp->addStmtsp(
        new AstInitial{fl, new AstAssign{fl, new AstVarRef{fl, boundVarp, VAccess::WRITE},
                                         newAnyTargetBoundp(fl, hookPathVarp)}});
    AstDisplay* const warnp = new AstDisplay{
        fl, VDisplayType::DT_WARNING,
        "DPI-hook: __Vdpihook_path was written after the first eval(); the binding is sampled"
        " once, at time zero, so no target was hooked",
        nullptr, nullptr};
    // A warning provides the simulation time
    warnp->fmtp()->timeunit(topModp->timeunit());
    AstLogAnd* const lateBoundp
        = new AstLogAnd{fl, newAnyTargetBoundp(fl, hookPathVarp),
                        new AstLogNot{fl, new AstVarRef{fl, boundVarp, VAccess::READ}}};
    topModp->addStmtsp(new AstFinal{fl, new AstIf{fl, lateBoundp, warnp}});
}
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
    cellp->v3fatalSrc("Cell outside of a module");
    return nullptr;  // LCOV_EXCL_LINE
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
static std::vector<ChainStep> accessChainSteps(const AstVar* rootVarp,
                                               const DpiHookAccessPath& path) {
    std::vector<ChainStep> steps;
    AstNodeDType* dtypep = rootVarp->dtypep()->skipRefp();
    for (const DpiHookStep& step : path) {
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
    string m_curHier;  // Instance path resolved so far
    string m_target;  // Current config key
    HookInsertTarget* m_targetp = nullptr;  // Config of the current key
    struct ScopeNames final {
        std::unordered_map<string, AstCell*> cells;
        std::unordered_map<string, AstVar*> vars;
        std::unordered_map<string, AstGenBlock*> genBlocks;
    };
    std::unordered_map<const AstNode*, ScopeNames>
        m_scopeNames;  // Name index of each scope, built on first lookup

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
    FileLine* targetFl() const { return m_targetp->entries.front().cfgFl; }
    static AstNode* scopeDeclsp(AstNode* scopep) {
        if (AstNodeModule* const modp = VN_CAST(scopep, NodeModule)) return modp->stmtsp();
        if (AstGenBlock* const genBlockp = VN_CAST(scopep, GenBlock)) return genBlockp->itemsp();
        scopep->v3fatalSrc("Scope is neither a module nor a generate block");
        return nullptr;  // LCOV_EXCL_LINE
    }
    static void addScopeItems(ScopeNames& names, AstNode* itemsp) {
        for (AstNode* itemp = itemsp; itemp; itemp = itemp->nextp()) {
            if (AstCell* const cellp = VN_CAST(itemp, Cell))
                names.cells.emplace(cellp->name(), cellp);
            if (AstGenBlock* const genBlockp = VN_CAST(itemp, GenBlock)) {
                names.genBlocks.emplace(genBlockp->name(), genBlockp);
                if (genBlockp->implied()) addScopeItems(names, genBlockp->itemsp());
            }
        }
    }
    const ScopeNames& scopeNames(AstNode* scopep) {
        const auto it = m_scopeNames.find(scopep);
        if (it != m_scopeNames.end()) return it->second;
        ScopeNames& names = m_scopeNames[scopep];
        for (AstNode* declp = scopeDeclsp(scopep); declp; declp = declp->nextp())
            if (AstVar* const varp = VN_CAST(declp, Var)) names.vars.emplace(varp->name(), varp);
        addScopeItems(names, scopeDeclsp(scopep));
        return names;
    }
    AstCell* scopeChildCellp(AstNode* scopep, const string& name) {
        const ScopeNames& names = scopeNames(scopep);
        const auto it = names.cells.find(name);
        return it == names.cells.end() ? nullptr : it->second;
    }
    // Element cell of an instance array, e.g. "arr[1]". Elaboration fully expands
    // instance arrays, so by the time this pass runs the element is an ordinary
    // cell carrying the encoded name and there is no AstRange left to walk. An
    // index outside the declared range simply finds no cell.
    AstCell* arrayedInstCellp(AstNode* scopep, const string& name, uint32_t index) {
        return scopeChildCellp(scopep, name + "__BRA__"
                                           + AstNode::encodeNumber(static_cast<int64_t>(index))
                                           + "__KET__");
    }
    // Only interface arrays are addressable; see the module-array rejection below.
    AstCell* arrayedIfaceCellp(AstNode* scopep, const string& name, uint32_t index) {
        AstCell* const cellp = arrayedInstCellp(scopep, name, index);
        return (cellp && VN_IS(cellp->modp(), Iface)) ? cellp : nullptr;
    }
    AstVar* scopeChildVarp(AstNode* scopep, const string& name) {
        const ScopeNames& names = scopeNames(scopep);
        const auto it = names.vars.find(name);
        return it == names.vars.end() ? nullptr : it->second;
    }
    AstGenBlock* childGenBlockp(AstNode* scopep, const string& name) {
        const ScopeNames& names = scopeNames(scopep);
        const auto it = names.genBlocks.find(name);
        return it == names.genBlocks.end() ? nullptr : it->second;
    }
    struct PathComponent final {
        string name;
        bool hasIndex;
        uint32_t index;
    };
    // Split path component into its name and optional array index
    // "arr[2]" -> {"arr", true, 2}, "u" -> {"u", false, 0}
    static PathComponent parseComponent(const string& part) {
        const auto open = part.find('[');
        if (open == string::npos || part.back() != ']') return {part, false, 0};
        const string index = part.substr(open + 1, part.size() - open - 2);
        if (!isDpiHookConfigNumber(index)) return {part, false, 0};
        return {part.substr(0, open), true, static_cast<uint32_t>(std::stoul(index))};
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
            targetFl()->v3error("DPI-hook insertion of target '"
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
            const PathComponent part = parseComponent(targetParts[i]);
            AstCell* const targetCellp = part.hasIndex
                                             ? arrayedIfaceCellp(curScopep, part.name, part.index)
                                             : scopeChildCellp(curScopep, part.name);
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
            if (scopeChildVarp(curScopep, part.name)) {
                if (!genScope.empty()) {
                    targetFl()->v3warn(
                        E_UNSUPPORTED,
                        "Unsupported: DPI-hook insertion of target '"
                            << m_target << "': a member path into a variable of a generate block");
                    m_error = true;
                    return;
                }
                resolveMemberPath(curModp, targetParts, i);
                return;
            }
            // An indexed component may be an unrolled generate-loop iteration (e.g. "lane[0]")
            // Therefore descend into generate block and pin the var there
            if (AstGenBlock* const genBlockp = childGenBlockp(
                    curScopep, part.hasIndex ? genBlockName(part.name, part.index) : part.name)) {
                curScopep = genBlockp;
                genScope += (genScope.empty() ? "" : ".") + targetParts[i];
                m_curHier += "." + targetParts[i];
                continue;
            }
            if (part.hasIndex) {
                AstCell* const arrayCellp = arrayedInstCellp(curScopep, part.name, part.index);
                if (arrayCellp) {
                    targetFl()->v3warn(E_UNSUPPORTED, "Unsupported: DPI-hook insertion of target '"
                                                          << m_target
                                                          << "': arrayed module instances");
                    m_error = true;
                    return;
                }
            }
            // Neither a cell nor a var -> missing instance
            if (i == 1) {
                targetFl()->v3error("DPI-hook insertion of target '"
                                    << m_target
                                    << "' could not find initial 'instance' in "
                                       "'topModule.instance.__'");
            } else {
                targetFl()->v3error("DPI-hook insertion of target '"
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
            targetFl()->v3warn(E_UNSUPPORTED, "Unsupported: DPI-hook insertion of target '"
                                                  << m_target
                                                  << "' resolving to a non-module container");
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
                targetFl()->v3warn(E_UNSUPPORTED,
                                   "Unsupported: DPI-hook insertion of target '"
                                       << m_target << "': a member path into an interface signal\n"
                                       << targetFl()->warnMore()
                                       << "... Suggest hook the whole signal");
            } else {
                targetFl()->v3warn(E_UNSUPPORTED, "Unsupported: DPI-hook insertion of target '"
                                                      << m_target
                                                      << "' resolving to a non-module container");
            }
            m_error = true;
            return;
        }
        const PathComponent varPart = parseComponent(parts[boundaryIdx]);
        DpiHookAccessPath prefixSteps;
        if (varPart.hasIndex) prefixSteps.push_back(DpiHookStep{true, varPart.index, ""});
        for (size_t j = boundaryIdx + 1; j < parts.size(); ++j) {
            const PathComponent memberPart = parseComponent(parts[j]);
            prefixSteps.push_back(DpiHookStep{false, 0, memberPart.name});
            if (memberPart.hasIndex)
                prefixSteps.push_back(DpiHookStep{true, memberPart.index, ""});
        }
        for (auto& entry : m_targetp->entries) {
            DpiHookAccessPath full = prefixSteps;
            full.push_back(DpiHookStep{false, 0, entry.varTarget});  // the original last part
            for (const DpiHookStep& step : entry.accessPath) full.push_back(step);
            entry.varTarget = varPart.name;
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
                entry.cfgFl->v3error("DPI-hook insertion of target '"
                                     << m_target << "': signal '" << entry.varTarget
                                     << "' not found in interface '" << ifacep->name() << "'");
                m_error = true;
                return;
            }
            AstNodeDType* const dtypep = sigVarp->dtypep()->skipRefp();
            const AstStructDType* const structp = VN_CAST(dtypep, StructDType);
            if (entry.hasMemberStep() || (structp && !structp->packed())
                || VN_IS(dtypep, UnpackArrayDType)) {
                sigVarp->v3warn(E_UNSUPPORTED,
                                "Unsupported: DPI-hook insertion of target '"
                                    << m_target << "." << entry.varTarget
                                    << "': aggregate or member-addressed interface signal\n"
                                    << sigVarp->warnMore() << "... Suggest hook a packed leaf");
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
                        refp->v3warn(E_UNSUPPORTED,
                                     "Unsupported: DPI-hook insertion of target '"
                                         << m_target << "." << entry.varTarget
                                         << "': a read-write reference to an interface signal");
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
        std::unordered_map<string, std::vector<size_t>> entryIdxsByName;
        for (size_t ei = 0; ei < m_targetp->entries.size(); ++ei)
            entryIdxsByName[m_targetp->entries[ei].varTarget].push_back(ei);
        std::vector<AstVar*> targetVarps;
        for (AstNode* declp = scopeDeclsp(m_targetScopep); declp; declp = declp->nextp()) {
            AstVar* const varp = VN_CAST(declp, Var);
            if (!varp || varp->isFuncLocal()) continue;
            if (entryIdxsByName.count(varp->name())) targetVarps.push_back(varp);
        }
        std::set<string> foundNames;
        for (const AstVar* const varp : targetVarps) foundNames.insert(varp->name());
        for (const HookInsertEntry& entry : m_targetp->entries) {
            if (foundNames.count(entry.varTarget)) continue;
            entry.cfgFl->v3error("DPI-hook insertion of target '"
                                 << entry.origTarget
                                 << "' could not find 'var' in '__.instance.var'");
            m_error = true;
        }
        for (AstVar* const varp : targetVarps)
            for (const size_t ei : entryIdxsByName[varp->name()])
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
            fl, VVarType::VAR, "__Vdpihook_mirror__" + aggregateVarp->name() + scopeSuffix,
            mirrorDTypep};
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
                entry.hookedName = "__Vdpihook_hooked__" + aggregateVarp->name() + scopeSuffix;
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
            aggregateVarp->v3warn(
                E_UNSUPPORTED,
                "Unsupported: Target variable '"
                    << aggregateVarp->name() << "' in '" << m_curHier << "' flattens to "
                    << nLeaves << " leaves, too large to hook as a whole (limit "
                    << DPIHOOK_MAX_AGGREGATE_LEAVES << ")\n"
                    << aggregateVarp->warnMore() << "... Suggest hook individual elements");
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
            targetVarp->v3warn(
                E_UNSUPPORTED,
                "Unsupported: Target variable '"
                    << what << "' in '" << m_curHier
                    << "' has an unpacked or aggregate type that cannot be hooked directly; only"
                       " packed (bit-vector) types are supported");
            return false;
        }
        if (!basicp->isLiteralType()) {
            targetVarp->v3warn(E_UNSUPPORTED, "Unsupported: Target variable '"
                                                  << what << "' in '" << m_curHier << "' of type "
                                                  << dtypep->prettyDTypeNameQ());
            return false;
        }
        if (basicp->isDouble()) {
            targetVarp->v3warn(
                E_UNSUPPORTED,
                "Unsupported: Target variable '"
                    << what << "' in '" << m_curHier
                    << "' is a floating-point type, which has no gate-level representation");
            return false;
        }
        return true;
    }
    bool isReadInSensitivity(AstVar* targetVarp, const HookInsertEntry& entry) {
        const string what = targetVarp->name() + entry.accessPathText();
        const ClockUseVisitor clockUse{m_netlistp, targetVarp,
                                       accessChainSteps(targetVarp, entry.accessPath)};
        if (clockUse.isClock()) {
            targetVarp->v3warn(
                E_UNSUPPORTED,
                "Unsupported: Target variable '"
                    << what << "' in '" << m_curHier
                    << "' is used as a clock or asynchronous reset (it appears in an"
                       " edge-sensitive sensitivity list)");
            return true;
        }
        if (clockUse.isEventControl()) {
            // The block would keep waiting on the unhooked value
            targetVarp->v3warn(
                E_UNSUPPORTED,
                "Unsupported: Target variable '"
                    << what << "' in '" << m_curHier
                    << "' is read in an event control without an edge (e.g. 'always @("
                    << targetVarp->prettyName() << entry.accessPathText() << " or ...)')");
            return true;
        }
        return false;
    }
    AstNodeDType* resolveLeafDTypep(AstVar* varp, const DpiHookAccessPath& path) {
        AstNodeDType* dtypep = varp->dtypep()->skipRefp();
        for (const DpiHookStep& step : path) {
            if (step.isIndex) {
                AstUnpackArrayDType* const adtypep = VN_CAST(dtypep, UnpackArrayDType);
                if (!adtypep) {
                    varp->v3error("DPI-hook target '"
                                  << varp->name() << "' in '" << m_curHier << "': index ["
                                  << step.index << "] applied to " << dtypep->prettyDTypeNameQ()
                                  << "; element access is supported on unpacked arrays only");
                    return nullptr;
                }
                if (!isElemIndexInRange(adtypep, step.index)) {
                    varp->v3error("DPI-hook target '"
                                  << varp->name() << "' in '" << m_curHier << "': element index "
                                  << step.index << " out of range (" << adtypep->elementsConst()
                                  << " elements)");
                    return nullptr;
                }
                dtypep = adtypep->subDTypep()->skipRefp();
            } else {
                AstStructDType* const structp = VN_CAST(dtypep, StructDType);
                if (!structp) {
                    varp->v3error("DPI-hook target '"
                                  << varp->name() << "' in '" << m_curHier << "': member '."
                                  << step.member << "' of " << dtypep->prettyDTypeNameQ()
                                  << "; member access is supported on structs only");
                    return nullptr;
                }
                AstNodeDType* memberDTypep = nullptr;
                for (AstMemberDType* memberp = structp->membersp(); memberp && !memberDTypep;
                     memberp = VN_CAST(memberp->nextp(), MemberDType))
                    if (memberp->name() == step.member) memberDTypep = memberp->subDTypep();
                if (!memberDTypep) {
                    varp->v3error("DPI-hook target '" << varp->name() << "' in '" << m_curHier
                                                      << "': no member named '" << step.member
                                                      << "'");
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
                targetVarp->v3warn(E_UNSUPPORTED,
                                   "Unsupported: DPI-hook target '"
                                       << targetVarp->name() << "' in '" << m_curHier
                                       << "': the addressed member is an unpacked aggregate\n"
                                       << targetVarp->warnMore()
                                       << "... Suggest hook a scalar or packed leaf");
                return;
            }
            if (!checkHookableType(targetVarp, what, leafDTypep)) return;
            if (isReadInSensitivity(targetVarp, entry)) return;
            const string leafName = "__Vdpihook_hooked__" + targetVarp->name()
                                    + entry.accessPathSuffix() + entry.genScopeSuffix();
            setVarAt(entryIdx, targetVarp, leafName, leafDTypep);
            m_foundVar = true;
            return;
        }
        AstNodeDType* const dtypep = targetVarp->dtypep()->skipRefp();
        AstStructDType* const structp = VN_CAST(dtypep, StructDType);
        const bool wholeAggregate
            = !entry.hasElemIndex()
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
        if (entry.hasElemIndex() && !adtypep) {
            targetVarp->v3error("DPI-hook target '"
                                << targetVarp->name() << "' in '" << m_curHier << "': index ["
                                << entry.elemIndex() << "] applied to "
                                << targetVarp->dtypep()->skipRefp()->prettyDTypeNameQ()
                                << "; element access is supported on unpacked arrays only\n"
                                << targetVarp->warnMore() << "... Suggest hook the whole signal");
            return;
        }
        if (entry.hasElemIndex() && adtypep && !isElemIndexInRange(adtypep, entry.elemIndex())) {
            targetVarp->v3error("Element index "
                                << entry.elemIndex() << " is out of range for target variable '"
                                << targetVarp->name() << "' in '" << m_curHier << "' ("
                                << adtypep->elementsConst() << " elements)");
            return;
        }
        AstNodeDType* const valueDTypep = entry.hasElemIndex() ? adtypep->subDTypep() : dtypep;
        if (!checkHookableType(targetVarp, what, valueDTypep)) return;
        if (isReadInSensitivity(targetVarp, entry)) return;
        const string hookedName = "__Vdpihook_hooked__" + targetVarp->name()
                                  + entry.accessPathSuffix() + entry.genScopeSuffix();
        setVarAt(entryIdx, targetVarp, hookedName,
                 entry.hasElemIndex() && adtypep ? adtypep->subDTypep() : nullptr);
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
    HookLookups& m_lookups;  // Ports, triggers and pins the pass added so far

    // METHODS
    AstVar* insertCaseIdInputVarp(AstNodeModule* modp) {
        AstTypeTable* const typeTablep = VN_CAST(m_netlistp->miscsp(), TypeTable);
        AstBasicDType* const elemDTypep
            = new AstBasicDType{modp->fileline(), VBasicDTypeKwd::INT, VSigning::SIGNED};
        elemDTypep->generic(true);
        typeTablep->addTypesp(elemDTypep);
        AstUnpackArrayDType* const arrDTypep = new AstUnpackArrayDType{
            modp->fileline(), elemDTypep, new AstRange{modp->fileline(), dpiHookSlots() - 1, 0}};
        typeTablep->addTypesp(arrDTypep);
        AstVar* const caseIdInputVarp
            = new AstVar{modp->fileline(), VVarType::PORT, "__Vdpihook_id", arrDTypep};
        caseIdInputVarp->lifetime(VLifetime::STATIC_IMPLICIT);
        caseIdInputVarp->direction(VDirection::INPUT);
        caseIdInputVarp->trace(false);
        modp->addStmtsp(caseIdInputVarp);
        m_lookups.caseIdVarps.emplace(modp, caseIdInputVarp);
        return caseIdInputVarp;
    }
    AstVar* insertHookPathVarp(AstNodeModule* modp, int idx) {
        const bool isInitMod
            = !m_insertTarget.modps.empty() && m_insertTarget.modps.front() == modp;
        const bool isOrigMod = m_insertTarget.hookLogicContainerp() == modp;
        AstVar* const hookPathVarp = newHookPathVarp(modp, idx, isInitMod, isOrigMod);
        modp->addStmtsp(hookPathVarp);
        m_lookups.hookPathVarps.emplace(modp, hookPathVarp);
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
        AstVar* const hookPathVarp = new AstVar{modp->fileline(), VVarType::PORT,
                                                "__Vdpihook_path", m_dtypeCache.stringDTypep};
        hookPathVarp->direction(VDirection::INPUT);
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
    bool hasPathFilter(AstNodeModule* modp) { return m_caseCache.count(modp) != 0; }
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
                                                    "__Vdpihook_path__" + cellFlatNm, pathsDTypep};
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
    void insertCtrlPin(AstCell* cellp, int idx, const std::vector<AstVar*>& ctrlVarps) {
        int pinNum = 0;
        for (AstNode* existingPinp = cellp->pinsp(); existingPinp;
             existingPinp = existingPinp->nextp())
            pinNum++;
        AstVar* const portVarp = ctrlVarps[idx + 1];
        AstVarRef* const refp = new AstVarRef{cellp->fileline(), ctrlVarps[idx], VAccess::READ};
        AstPin* const pinp = new AstPin{cellp->fileline(), pinNum, portVarp->name(), refp};
        pinp->modVarp(portVarp);
        pinp->svDotName(true);
        cellp->addPinsp(pinp);
        m_lookups.cellPins.emplace(cellp, portVarp->name());
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
        cfg.targetVarName = "__Vdpihook_path_part";
        cfg.targetVarLifetime = VLifetime::STATIC_IMPLICIT;
        cfg.targetVarHasUserInit = false;
        cfg.declTargetInLoopBody = false;  // declared in the always body
        cfg.alwaysName = "__Vdpihook_path_filter";
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
                = new AstPin{cellp->fileline(), pinNum, "__Vdpihook_path", instPathRefp};
            pinp->modVarp(hookPathVarps[idx + 1]);
            pinp->svDotName(true);
            cellp->addPinsp(pinp);
            m_lookups.cellPins.emplace(cellp, "__Vdpihook_path");
        }
    }
    void insertCtrlLogicToCells(const std::vector<AstVar*>& caseIdInputVarps,
                                const std::vector<AstVar*>& hookPathVarps,
                                const std::vector<AstVar*>& triggerVarps,
                                const InstPathMap& instPathVarps) {
        AstCell* prevCellp = nullptr;
        int idx = 0;
        for (AstCell* cellp : m_insertTarget.cellps) {
            if (prevCellp && cellp->modp() != prevCellp->modp()) idx++;
            if (!m_lookups.cellPins.count({cellp, "__Vdpihook_id"}))
                insertCtrlPin(cellp, idx, caseIdInputVarps);
            if (!m_lookups.cellPins.count({cellp, "__Vdpihook_trigger"}))
                insertCtrlPin(cellp, idx, triggerVarps);
            if (!m_lookups.cellPins.count({cellp, "__Vdpihook_path"}))
                insertHookPathPin(cellp, idx, hookPathVarps, instPathVarps);
            prevCellp = cellp;
        }
    }
    void insertCtrlLogicToModules(std::vector<AstVar*>& caseIdInputVarps,
                                  std::vector<AstVar*>& hookPathVarps,
                                  std::vector<AstVar*>& triggerVarps, InstPathMap& instPathVarps) {
        AstNodeModule* const origModp = m_insertTarget.hookLogicContainerp();
        size_t idx = 0;
        for (AstNodeModule* modp : m_insertTarget.modps) {
            AstVar* caseIdInputVarp = HookLookups::varp(m_lookups.caseIdVarps, modp);
            if (!caseIdInputVarp) caseIdInputVarp = insertCaseIdInputVarp(modp);
            caseIdInputVarps.push_back(caseIdInputVarp);
            triggerVarps.push_back(triggerVarp(modp));
            AstVar* hookPathVarp = HookLookups::varp(m_lookups.hookPathVarps, modp);
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
        AstVar* origCaseIdInputVarp = HookLookups::varp(m_lookups.caseIdVarps, origModp);
        if (!origCaseIdInputVarp) origCaseIdInputVarp = insertCaseIdInputVarp(origModp);
        caseIdInputVarps.push_back(origCaseIdInputVarp);
        triggerVarps.push_back(triggerVarp(origModp));
        AstVar* origHookPathVarp = HookLookups::varp(m_lookups.hookPathVarps, origModp);
        if (!origHookPathVarp) origHookPathVarp = insertHookPathVarp(origModp, idx);
        hookPathVarps.push_back(origHookPathVarp);
    }
    AstVar* triggerVarp(AstNodeModule* modp) {
        if (AstVar* const varp = HookLookups::varp(m_lookups.triggerVarps, modp)) return varp;
        AstTypeTable* const typeTablep = VN_CAST(m_netlistp->miscsp(), TypeTable);
        AstBasicDType* const dtypep
            = new AstBasicDType{modp->fileline(), VBasicDTypeKwd::BIT, VSigning::NOSIGN};
        dtypep->generic(true);
        typeTablep->addTypesp(dtypep);
        AstVar* const varp
            = new AstVar{modp->fileline(), VVarType::PORT, "__Vdpihook_trigger", dtypep};
        varp->direction(VDirection::INPUT);
        varp->lifetime(VLifetime::STATIC_IMPLICIT);
        varp->trace(false);
        modp->addStmtsp(varp);
        m_lookups.triggerVarps.emplace(modp, varp);
        return varp;
    }

public:
    HookPathRouter(AstNetlist* netlistp, HookInsertTarget& insertTarget, DTypeCache& dtypeCache,
                   std::unordered_map<AstNodeModule*, AstCase*>& caseCache,
                   std::unordered_map<AstNodeModule*, AstVar*>& loopVarCache,
                   std::unordered_map<AstNodeModule*, std::set<string>>& caseChildCells,
                   HookLookups& lookups)
        : m_netlistp{netlistp}
        , m_dtypeCache{dtypeCache}
        , m_insertTarget{insertTarget}
        , m_caseCache{caseCache}
        , m_loopVarCache{loopVarCache}
        , m_caseChildCells{caseChildCells}
        , m_lookups{lookups} {}

    void insert() {
        std::vector<AstVar*> caseIdInputVarps;
        std::vector<AstVar*> hookPathVarps;
        std::vector<AstVar*> triggerVarps;
        InstPathMap instPathVarps;

        insertCtrlLogicToModules(caseIdInputVarps, hookPathVarps, triggerVarps, instPathVarps);
        insertCtrlLogicToCells(caseIdInputVarps, hookPathVarps, triggerVarps, instPathVarps);
        m_insertTarget.dpiTriggerVarp = triggerVarps.back();
    }
};

class DpiOverrideBuilder final {
    // MEMBERS
    AstBasicDType* m_idDTypep = nullptr;  // Dtype of the id argument of the callback
    AstNodeModule* m_targetModp;  // Provided by constructor (module or interface)
    AstFunc* m_funcp = nullptr;  // DPI import function of the callback (targets up to 64 bits)
    AstTask* m_taskp = nullptr;  // DPI import task of the callback (targets wider than 64 bits)
    AstTypeTable* m_typeTablep;  // Provided by constructor
    AstVar* m_condVarp = nullptr;  // Set while the target is bound (`__Vdpihook_sel_cond__*`)
    AstVar* m_caseIdVarp
        = nullptr;  // Per-target case-id, read by the DPI callback (see insertCaseIdVar)
    AstVar* m_dpiTriggerVarp;  // Provided by constructor
    AstVar* m_selResVarp
        = nullptr;  // Hook result every reader of the target sees (`__Vdpihook_sel_res__*`)
    AstVar* m_preVarp = nullptr;  // Intermediate the drivers write to
    AstArraySel* m_viewSelp = nullptr;  // The element view's own read; never redirected
    AstNodeExpr* m_viewExprp = nullptr;  // The member/index leaf view's own read; never redirected
    std::set<const AstArraySel*> m_resolvedSelps;  // Non-constant-index reads already resolved
    HookInsertEntry& m_targetEntry;  // Provided by constructor
    std::unordered_map<AstNodeModule*, AstCase*>& m_caseCache;  // Provided by constructor
    std::unordered_map<AstNodeModule*, AstVar*>&
        m_targetLoopVarCache;  // Loop index var of each module's __Vdpihook_target_filter
    std::map<std::pair<const AstNodeModule*, string>, AstNodeFTask*>&
        m_callbackCache;  // Callback imports created so far, by container and name
    HookLookups& m_lookups;  // Ports, triggers and pins the pass added so far

    // METHODS
    AstAlways* buildHandlerp(AstVar* hookedVarp, AstVar* targetVarp) {
        FileLine* const fl = m_targetModp->fileline();

        // Not targetVarp: this hook drives it, so reading it back would form a loop
        AstVar* const sourceVarp = m_preVarp ? m_preVarp : targetVarp;

        // Only evaluate fault callback when hook is actually bound at runtime
        AstNodeStmt* thenp = nullptr;
        if (m_taskp) {
            AstTaskRef* const taskRefp = new AstTaskRef{fl, m_taskp, nullptr};
            taskRefp->addArgsp(new AstArg{fl, "", new AstVarRef{fl, hookedVarp, VAccess::WRITE}});
            finalizeFtaskRef(taskRefp, sourceVarp);
            thenp = new AstStmtExpr{fl, taskRefp};
        } else {
            AstFuncRef* const funcRefp = new AstFuncRef{fl, m_funcp, nullptr};
            finalizeFtaskRef(funcRefp, sourceVarp);
            thenp = new AstAssign{fl, new AstVarRef{fl, hookedVarp, VAccess::WRITE}, funcRefp};
        }
        // Otherwise the unmodified value of the signal (== Passthrough)
        AstNodeStmt* const elsep = new AstAssign{fl, new AstVarRef{fl, hookedVarp, VAccess::WRITE},
                                                 new AstVarRef{fl, sourceVarp, VAccess::READ}};
        AstIf* const ifp
            = new AstIf{fl, new AstVarRef{fl, m_condVarp, VAccess::READ}, thenp, elsep};
        AstAlways* const dpiAlwaysp = new AstAlways{fl, VAlwaysKwd::ALWAYS_COMB, nullptr, ifp};
        m_targetModp->addStmtsp(dpiAlwaysp);

        AstCond* const condp = new AstCond{fl, new AstVarRef{fl, m_condVarp, VAccess::READ},
                                           new AstVarRef{fl, hookedVarp, VAccess::READ},
                                           new AstVarRef{fl, sourceVarp, VAccess::READ}};
        AstAssignW* const selResAssignp
            = new AstAssignW{fl, new AstVarRef{fl, m_selResVarp, VAccess::WRITE}, condp};
        return new AstAlways{fl, VAlwaysKwd::CONT_ASSIGN, nullptr, selResAssignp};
    }
    static AstNodeDType* dpiValueDTypep(AstVar* targetVarp) {
        AstNodeDType* const dtypep = targetVarp->dtypep()->skipRefp();
        if (VN_IS(dtypep, BasicDType)) return dtypep;
        const int width = dtypep->width();
        const VNumRange range{width - 1, 0};
        return dtypep->isFourstate()
                   ? targetVarp->findLogicRangeDType(range, width, VSigning::NOSIGN)
                   : targetVarp->findBitRangeDType(range, width, VSigning::NOSIGN);
    }
    AstNodeFTask* finalizeFtaskp(AstNodeFTask* ftaskp, AstVar* drivingVarp) {
        if (!m_idDTypep) {
            m_idDTypep = new AstBasicDType{ftaskp->fileline(), VBasicDTypeKwd::INT};
            m_idDTypep->generic(true);
            m_typeTablep->addTypesp(m_idDTypep);
        }
        AstVar* const idArgVarp
            = new AstVar{ftaskp->fileline(), VVarType::PORT, "__Vdpihook_id", m_idDTypep};
        idArgVarp->direction(VDirection::INPUT);
        idArgVarp->lifetime(VLifetime::AUTOMATIC_IMPLICIT);
        idArgVarp->funcLocal(true);
        ftaskp->addDeclsp(idArgVarp);

        AstVar* const triggerArgVarp = m_dpiTriggerVarp->cloneTree(false);
        triggerArgVarp->varType(VVarType::PORT);
        triggerArgVarp->direction(VDirection::INPUT);
        triggerArgVarp->lifetime(VLifetime::AUTOMATIC_IMPLICIT);
        triggerArgVarp->funcLocal(true);
        ftaskp->addDeclsp(triggerArgVarp);

        AstVar* const valueArgVarp = drivingVarp->cloneTree(false);
        valueArgVarp->dtypep(dpiValueDTypep(drivingVarp));
        valueArgVarp->direction(VDirection::INPUT);
        valueArgVarp->lifetime(VLifetime::AUTOMATIC_IMPLICIT);
        valueArgVarp->funcLocal(true);
        ftaskp->addDeclsp(valueArgVarp);

        return ftaskp;
    }
    void finalizeFtaskRef(AstNodeFTaskRef* ftaskRefp, AstVar* targetVarp) {
        AstVarRef* const caseIdRefp
            = new AstVarRef{ftaskRefp->fileline(), m_caseIdVarp, VAccess::READ};
        AstVarRef* const triggerRefp
            = new AstVarRef{ftaskRefp->fileline(), m_dpiTriggerVarp, VAccess::READ};
        ftaskRefp->addArgsp(new AstArg{ftaskRefp->fileline(), "", caseIdRefp});
        ftaskRefp->addArgsp(new AstArg{ftaskRefp->fileline(), "", triggerRefp});
        AstVarRef* const targetRefp
            = new AstVarRef{ftaskRefp->fileline(), targetVarp, VAccess::READ};
        ftaskRefp->addArgsp(new AstArg{ftaskRefp->fileline(), "", targetRefp});
    }
    AstNodeFTask* newDpiImportp() {
        AstVar* const targetVarp = m_targetEntry.hookedVarp;
        const string callback = m_targetEntry.callback;
        if (targetVarp->basicp()->isLiteralType()) {
            if (targetVarp->width() > DPIHOOK_MAX_FUNC_WIDTH) {
                AstTask* const taskp = new AstTask{m_targetModp->fileline(), callback};
                AstVar* const resultVarp
                    = new AstVar{m_targetModp->fileline(), VVarType::PORT, "__Vdpihook_result",
                                 dpiValueDTypep(targetVarp)};
                resultVarp->direction(VDirection::OUTPUT);
                resultVarp->lifetime(VLifetime::AUTOMATIC_IMPLICIT);
                resultVarp->funcLocal(true);
                taskp->addDeclsp(resultVarp);
                return finalizeFtaskp(taskp, targetVarp);
            }
            AstBasicDType* const returnDTypep
                = new AstBasicDType{m_targetModp->fileline(), dpiReturnKwd(targetVarp->width())};
            returnDTypep->generic(true);
            m_typeTablep->addTypesp(returnDTypep);
            AstFunc* const funcp = new AstFunc{m_targetModp->fileline(), callback, returnDTypep};
            funcp->fvarp()->dtypeChgSigned();
            funcp->dtypep(targetVarp->dtypep());
            funcp->dtypeChgSigned();
            return finalizeFtaskp(funcp, targetVarp);
        }
        // Unreachable: the finder rejects a target whose basic type is not literal before an
        // entry reaches the builder
        targetVarp->v3fatalSrc("DPI-hook target survived the finder's type check");
        return nullptr;
    }
    AstVar* findHookPathVarp() {
        if (AstVar* const varp = HookLookups::varp(m_lookups.hookPathVarps, m_targetModp))
            return varp;
        // Path router always adds __Vdpihook_path to target container before override builder runs
        m_targetModp->v3fatalSrc("DPI-hook path input missing in target container");
        return nullptr;
    }
    AstVar* findCaseIdInputVarp(AstNodeModule* modp) {
        return HookLookups::varp(m_lookups.caseIdVarps, modp);
    }
    AstCase* findTargetFilterp() const {
        const auto it = m_caseCache.find(m_targetModp);
        return it != m_caseCache.end() ? it->second : nullptr;
    }
    VBasicDTypeKwd dpiReturnKwd(int width) {
        VBasicDTypeKwd kwd;
        if (width <= 1) {
            kwd = VBasicDTypeKwd::BIT;
        } else if (width <= 8) {
            kwd = VBasicDTypeKwd::BYTE;
        } else if (width <= 16) {
            kwd = VBasicDTypeKwd::SHORTINT;
        } else if (width <= 32) {
            kwd = VBasicDTypeKwd::INT;
        } else {
            kwd = VBasicDTypeKwd::LONGINT;
        }
        return kwd;
    }
    void insertTargetAssign(AstVar* targetVarp) {
        AstVarRef* const selResRefp
            = new AstVarRef{m_targetModp->fileline(), m_selResVarp, VAccess::READ};
        AstVarRef* const targetRefp
            = new AstVarRef{m_targetModp->fileline(), targetVarp, VAccess::WRITE};
        AstAssignW* const assignp
            = new AstAssignW{m_targetModp->fileline(), targetRefp, selResRefp};
        AstAlways* const alwaysp
            = new AstAlways{m_targetModp->fileline(), VAlwaysKwd::CONT_ASSIGN, nullptr, assignp};
        m_targetModp->addStmtsp(alwaysp);
    }
    void redirectAssignReads(AstNodeAssign* assignp, AstVar* targetVarp) {
        std::vector<AstNodeVarRef*> readRefps;
        const auto collect = [&](AstNodeVarRef* refp) {
            if (refp->varp() == targetVarp && refp->access().isReadOnly())
                readRefps.push_back(refp);
        };
        assignp->rhsp()->foreach(collect);
        assignp->lhsp()->foreach(collect);
        for (AstNodeVarRef* const refp : readRefps) redirectReadRef(refp, m_selResVarp);
    }
    void redirectReadRef(AstNodeVarRef* refp, AstVar* selResVarp) {
        if (VN_IS(refp, VarXRef) && !VN_IS(m_targetModp, Iface)) {
            refp->replaceWith(new AstVarRef{refp->fileline(), selResVarp, VAccess::READ});
            VL_DO_DANGLING(refp->deleteTree(), refp);
        } else {
            refp->varp(selResVarp);
            refp->name(selResVarp->name());
        }
    }
    void redirectTargetReads() {
        for (AstNodeVarRef* const refp : m_targetEntry.readRefps)
            redirectReadRef(refp, m_selResVarp);
        for (AstVarXRef* const xrefp : m_targetEntry.readXrefps) {
            xrefp->varp(m_selResVarp);
            xrefp->name(m_selResVarp->name());
        }
    }
    void routeOutputDrivers(AstVar* targetVarp) {
        if (!targetVarp->isOutputish() || !m_targetEntry.accessPath.empty()
            || m_targetEntry.isAggregateMirror)
            return;
        std::vector<AstNodeVarRef*> writeRefps;
        m_targetModp->foreach([&](AstNodeVarRef* refp) {
            if (refp->varp() == targetVarp && refp->access().isWriteOrRW())
                writeRefps.push_back(refp);
        });
        m_preVarp = new AstVar{m_targetModp->fileline(), VVarType::VAR,
                               "__Vdpihook_pre_hook__" + targetVarp->name(), targetVarp->dtypep()};
        m_preVarp->lifetime(VLifetime::STATIC_IMPLICIT);
        m_preVarp->trace(false);
        m_targetModp->addStmtsp(m_preVarp);
        for (AstNodeVarRef* const refp : writeRefps) {
            refp->varp(m_preVarp);
            refp->name(m_preVarp->name());
        }
    }
    void insertIfaceModportMember(AstVar* varp, VDirection::en direction) {
        AstIface* const ifacep = VN_CAST(m_targetModp, Iface);
        if (!ifacep) return;
        for (AstNode* stmtp = ifacep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstModport* const modportp = VN_CAST(stmtp, Modport)) {
                modportp->addVarsp(
                    new AstModportVarRef{varp->fileline(), varp->name(), direction});
            }
        }
    }
    void routeIfaceDrivers(AstVar* targetVarp) {
        if (!VN_IS(m_targetModp, Iface) || m_targetEntry.writeRefps.empty()) return;
        m_preVarp = new AstVar{m_targetModp->fileline(), VVarType::VAR,
                               "__Vdpihook_pre_hook__" + targetVarp->name(), targetVarp->dtypep()};
        m_preVarp->lifetime(VLifetime::STATIC_IMPLICIT);
        m_preVarp->trace(false);
        m_targetModp->addStmtsp(m_preVarp);
        insertIfaceModportMember(m_preVarp, VDirection::OUTPUT);
        for (AstNodeVarRef* const refp : m_targetEntry.writeRefps) {
            refp->varp(m_preVarp);
            refp->name(m_preVarp->name());
        }
    }
    void routeElementTarget(AstVar* targetVarp) {
        if (!m_targetEntry.hasElemIndex()) return;
        const AstUnpackArrayDType* const adtypep
            = VN_CAST(targetVarp->dtypep()->skipRefp(), UnpackArrayDType);
        if (!adtypep) return;
        const uint32_t idx = elemPos(adtypep, m_targetEntry.elemIndex());
        FileLine* const fl = m_targetModp->fileline();
        m_preVarp = new AstVar{fl, VVarType::VAR, "__Vdpihook_elem__" + hookBaseName(targetVarp),
                               m_targetEntry.hookedVarp->dtypep()};
        m_preVarp->lifetime(VLifetime::STATIC_IMPLICIT);
        m_preVarp->trace(false);
        m_targetModp->addStmtsp(m_preVarp);
        AstArraySel* const viewSelp = new AstArraySel{
            fl, new AstVarRef{fl, targetVarp, VAccess::READ}, new AstConst{fl, idx}};
        viewSelp->dtypep(m_preVarp->dtypep());
        m_viewSelp = viewSelp;
        m_targetModp->addStmtsp(new AstAlways{
            fl, VAlwaysKwd::CONT_ASSIGN, nullptr,
            new AstAssignW{fl, new AstVarRef{fl, m_preVarp, VAccess::WRITE}, viewSelp}});
    }
    // Visit every node of every module, so that reads reaching the target through a cross-module
    // reference are seen too
    template <typename Func>
    static void foreachModule(Func&& f) {
        for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp;
             modp = VN_AS(modp->nextp(), NodeModule)) {
            modp->foreach(f);
        }
    }
    static AstNodeVarRef* readRootRefp(AstNode* nodep) {
        while (nodep) {
            if (AstNodeVarRef* const refp = VN_CAST(nodep, NodeVarRef)) return refp;
            if (AstSel* const selp = VN_CAST(nodep, Sel)) {
                nodep = selp->fromp();
            } else {
                nodep = aggregateSelFromp(nodep);
            }
        }
        v3fatalSrc("Hooked read without a variable reference");
        return nullptr;  // LCOV_EXCL_LINE
    }
    static AstNodeExpr* newSelReadp(FileLine* fl, const AstNode* rootp, AstVar* selResVarp) {
        if (const AstVarXRef* const xrefp = VN_CAST(rootp, VarXRef))
            return new AstVarXRef{fl, selResVarp, xrefp->dotted(), VAccess::READ};
        return new AstVarRef{fl, selResVarp, VAccess::READ};
    }
    static void replaceReadWithSelRes(AstNodeExpr* readp, const AstNodeVarRef* rootRefp,
                                      AstVar* selResVarp) {
        readp->replaceWith(newSelReadp(readp->fileline(), rootRefp, selResVarp));
        VL_DO_DANGLING(readp->deleteTree(), readp);
    }
    void redirectElementReads(AstVar* targetVarp) {
        const uint32_t idx = elemPos(VN_AS(targetVarp->dtypep()->skipRefp(), UnpackArrayDType),
                                     m_targetEntry.elemIndex());
        std::vector<std::pair<AstArraySel*, AstNodeVarRef*>> reads;
        std::vector<std::pair<AstArraySel*, AstNodeVarRef*>> dynReads;
        foreachModule([&](AstNode* nodep) {
            AstArraySel* const selp = VN_CAST(nodep, ArraySel);
            if (!selp || selp == m_viewSelp) return;  // keep the view's own read
            AstNodeVarRef* const refp = VN_CAST(selp->fromp(), NodeVarRef);
            if (!refp || refp->varp() != targetVarp || !refp->access().isReadOnly()) return;
            if (const AstConst* const idxConstp = VN_CAST(selp->bitp(), Const)) {
                if (idxConstp->toUInt() == idx) reads.emplace_back(selp, refp);
            } else {
                dynReads.emplace_back(selp, refp);
            }
        });
        for (const auto& itr : reads) replaceReadWithSelRes(itr.first, itr.second, m_selResVarp);
        for (const auto& itr : dynReads) {
            AstArraySel* const selp = itr.first;
            AstNodeVarRef* const rootRefp = itr.second;
            AstNodeExpr* const bitp = selp->bitp();
            const int idxWidth = bitp->width();
            if (!bitp->isPure()) continue;
            m_resolvedSelps.insert(selp);
            FileLine* const fl = selp->fileline();
            VNRelinker relinker;
            selp->unlinkFrBack(&relinker);
            AstEq* const eqp
                = new AstEq{fl, bitp->cloneTree(false),
                            new AstConst{fl, AstConst::WidthedValue{}, idxWidth, idx}};
            AstCond* const condp
                = new AstCond{fl, eqp, newSelReadp(fl, rootRefp, m_selResVarp), selp};
            condp->dtypeFrom(selp);
            relinker.relink(condp);
        }
    }
    // Build select chain rootVarp<accessPath> (e.g. u.arr[2].x) with dtypes set and
    // returning the outermost expression
    AstNodeExpr* buildAccessChainp(AstVar* rootVarp, FileLine* fl,
                                   const VAccess& access = VAccess::READ) {
        AstNodeExpr* curp = new AstVarRef{fl, rootVarp, access};
        for (const ChainStep& step : accessChainSteps(rootVarp, m_targetEntry.accessPath)) {
            AstNodeExpr* selp = nullptr;
            switch (step.kind) {
            case ChainStep::ARRAYSEL:
                selp = new AstArraySel{fl, curp, new AstConst{fl, step.index}};
                break;
            case ChainStep::STRUCTSEL: selp = new AstStructSel{fl, curp, step.member}; break;
            case ChainStep::BITSEL: selp = new AstSel{fl, curp, step.lsb, step.width}; break;
            }
            selp->dtypep(step.dtypep);
            curp = selp;
        }
        return curp;
    }
    // Whether `exprp` is exactly the READ select chain rootVarp<accessPath>
    bool matchesAccessChain(const AstNode* exprp, const AstVar* rootVarp) const {
        const std::vector<ChainStep> steps = accessChainSteps(rootVarp, m_targetEntry.accessPath);
        const AstNode* curp = exprp;
        for (size_t n = steps.size(); n-- > 0;) {  // outermost select first
            const ChainStep& step = steps[n];
            switch (step.kind) {
            case ChainStep::ARRAYSEL: {
                const AstArraySel* const arraySelp = VN_CAST(curp, ArraySel);
                if (!arraySelp) return false;
                const AstConst* const idxConstp = VN_CAST(arraySelp->bitp(), Const);
                if (!idxConstp || idxConstp->toUInt() != step.index) return false;
                curp = arraySelp->fromp();
                break;
            }
            case ChainStep::STRUCTSEL: {
                const AstStructSel* const structSelp = VN_CAST(curp, StructSel);
                if (!structSelp || structSelp->name() != step.member) return false;
                curp = structSelp->fromp();
                break;
            }
            case ChainStep::BITSEL: {
                const AstSel* const bitSelp = VN_CAST(curp, Sel);
                if (!bitSelp || bitSelp->widthConst() != step.width) return false;
                const AstConst* const lsbp = VN_CAST(bitSelp->lsbp(), Const);
                if (!lsbp || static_cast<int>(lsbp->toUInt()) != step.lsb) return false;
                curp = bitSelp->fromp();
                break;
            }
            }
        }
        const AstNodeVarRef* const refp = VN_CAST(curp, NodeVarRef);
        return refp && refp->varp() == rootVarp && refp->access().isReadOnly();
    }
    // Give a member/index-path target a scalar view of the addressed leaf, driven
    // continuously from the leaf access chain (the counterpart of routeElementTarget)
    void routeMemberTarget(AstVar* targetVarp) {
        if (!m_targetEntry.hasMemberStep()) return;
        FileLine* const fl = m_targetModp->fileline();
        m_preVarp = new AstVar{fl, VVarType::VAR, "__Vdpihook_leaf__" + hookBaseName(targetVarp),
                               m_targetEntry.hookedVarp->dtypep()};
        m_preVarp->lifetime(VLifetime::STATIC_IMPLICIT);
        m_preVarp->trace(false);
        m_targetModp->addStmtsp(m_preVarp);
        AstNodeExpr* const viewExprp = buildAccessChainp(targetVarp, fl);
        m_viewExprp = viewExprp;
        m_targetModp->addStmtsp(new AstAlways{
            fl, VAlwaysKwd::CONT_ASSIGN, nullptr,
            new AstAssignW{fl, new AstVarRef{fl, m_preVarp, VAccess::WRITE}, viewExprp}});
    }
    void redirectMemberReads(AstVar* targetVarp) {
        std::vector<std::pair<AstNodeExpr*, AstNodeVarRef*>> reads;
        foreachModule([&](AstNode* nodep) {
            AstNodeExpr* const exprp = VN_CAST(nodep, NodeExpr);
            if (!exprp || exprp == m_viewExprp) return;
            if (!matchesAccessChain(exprp, targetVarp)) return;
            reads.emplace_back(exprp, readRootRefp(exprp));
        });
        for (const auto& itr : reads) replaceReadWithSelRes(itr.first, itr.second, m_selResVarp);
    }
    static bool isReadByAssignTo(const AstNode* nodep, const AstVar* lhsVarp) {
        for (const AstNode* backp = nodep->backp(); backp; backp = backp->backp()) {
            if (const AstNodeAssign* const assignp = VN_CAST(backp, NodeAssign)) {
                const AstVarRef* const lhsRefp = VN_CAST(assignp->lhsp(), VarRef);
                return lhsRefp && lhsRefp->varp() == lhsVarp;
            }
        }
        return false;
    }
    AstVar* buildAggregateViewp(AstVar* aggregateVarp, AstVar* targetVarp) {
        FileLine* const fl = aggregateVarp->fileline();
        AstVar* const viewVarp
            = new AstVar{fl, VVarType::VAR, "__Vdpihook_view__" + hookBaseName(targetVarp),
                         aggregateVarp->dtypep()};
        viewVarp->lifetime(VLifetime::STATIC_IMPLICIT);
        viewVarp->trace(false);
        m_targetModp->addStmtsp(viewVarp);
        AstNodeStmt* stmtsp = nullptr;
        if (m_targetEntry.isAggregateMirror) {
            std::vector<AstNodeExpr*> leafps;
            std::vector<int> widths;
            collectLeafAccesses(new AstVarRef{fl, viewVarp, VAccess::WRITE},
                                aggregateVarp->dtypep(), leafps, widths);
            int msb = m_selResVarp->width();  // First leaf is the most significant
            for (size_t k = 0; k < leafps.size(); ++k) {
                msb -= widths[k];
                AstSel* const sliceSelp = new AstSel{
                    fl, new AstVarRef{fl, m_selResVarp, VAccess::READ}, msb, widths[k]};
                sliceSelp->dtypep(leafps[k]->dtypep());
                AstNodeStmt* const assignp = new AstAssign{fl, leafps[k], sliceSelp};
                stmtsp = stmtsp ? AstNode::addNext(stmtsp, assignp) : assignp;
            }
        } else {
            stmtsp = new AstAssign{fl, new AstVarRef{fl, viewVarp, VAccess::WRITE},
                                   new AstVarRef{fl, aggregateVarp, VAccess::READ}};
            stmtsp->addNext(new AstAssign{fl, buildAccessChainp(viewVarp, fl, VAccess::WRITE),
                                          new AstVarRef{fl, m_selResVarp, VAccess::READ}});
        }
        m_targetModp->addStmtsp(new AstAlways{fl, VAlwaysKwd::ALWAYS_COMB, nullptr, stmtsp});
        return viewVarp;
    }
    void redirectViewReads(AstVar* aggregateVarp, AstVar* targetVarp) {
        const AstNodeVarRef* const leafRootRefp
            = m_viewExprp ? readRootRefp(m_viewExprp) : nullptr;
        std::vector<AstNodeVarRef*> readRefps;
        foreachModule([&](AstNodeVarRef* refp) {
            if (refp->varp() != aggregateVarp || !refp->access().isReadOnly()
                || refp == leafRootRefp)
                return;
            if (m_targetEntry.hasElemIndex()) {
                // In case of element read, the hooked one is redirected, the others are not hooked
                const AstArraySel* const selp = VN_CAST(refp->backp(), ArraySel);
                if (selp && selp->fromp() == refp
                    && (VN_IS(selp->bitp(), Const) || m_resolvedSelps.count(selp)))
                    return;
            }
            if (m_targetEntry.isAggregateMirror && isReadByAssignTo(refp, targetVarp)) return;
            readRefps.push_back(refp);
        });
        if (readRefps.empty()) return;
        AstVar* const viewVarp = buildAggregateViewp(aggregateVarp, targetVarp);
        for (AstNodeVarRef* const refp : readRefps) {
            refp->replaceWith(newSelReadp(refp->fileline(), refp, viewVarp));
            VL_DO_DANGLING(refp->deleteTree(), refp);
        }
    }
    string bindName(AstVar* targetVarp) const {
        string name;
        if (m_targetEntry.isAggregateMirror) {
            name = m_targetEntry.aggregateVarp->name();
        } else {
            name = targetVarp->name();
            for (const DpiHookStep& step : m_targetEntry.accessPath)
                name += step.isIndex ? ("[" + std::to_string(step.index) + "]")
                                     : ("." + step.member);
        }
        if (!m_targetEntry.genScope.empty()) name = m_targetEntry.genScope + "." + name;
        return name;
    }
    void insertCaseItem(AstVar* targetVarp, AstCase* casep) {
        const string bindName = this->bindName(targetVarp);
        AstConst* const bindNameConstp
            = new AstConst{m_targetModp->fileline(), AstConst::VerilogStringLiteral{}, bindName};
        AstCvtPackString* const cvtPackStringp
            = new AstCvtPackString{m_targetModp->fileline(), bindNameConstp};
        AstVarRef* const condWriteRefp
            = new AstVarRef{m_targetModp->fileline(), m_condVarp, VAccess::WRITE};
        AstAssign* const condAssignp = new AstAssign{m_targetModp->fileline(), condWriteRefp,
                                                     new AstConst{m_targetModp->fileline(), 1}};
        AstVar* const caseIdInputVarp = findCaseIdInputVarp(m_targetModp);
        const auto loopIt = m_targetLoopVarCache.find(m_targetModp);
        UASSERT_OBJ(loopIt != m_targetLoopVarCache.end(), m_targetModp,
                    "DPI-hook: target filter loop variable missing for module");
        AstVar* const loopVarp = loopIt->second;
        AstArraySel* const caseIdSelp = new AstArraySel{
            m_targetModp->fileline(),
            new AstVarRef{m_targetModp->fileline(), caseIdInputVarp, VAccess::READ},
            new AstVarRef{m_targetModp->fileline(), loopVarp, VAccess::READ}};
        AstVarRef* const caseIdWriteRefp
            = new AstVarRef{m_targetModp->fileline(), m_caseIdVarp, VAccess::WRITE};
        AstAssign* const caseIdAssignp
            = new AstAssign{m_targetModp->fileline(), caseIdWriteRefp, caseIdSelp};
        AstBegin* const caseBodyBeginp
            = new AstBegin{m_targetModp->fileline(), "", condAssignp, false};
        caseBodyBeginp->addStmtsp(caseIdAssignp);
        AstCaseItem* const caseItemp
            = new AstCaseItem{m_targetModp->fileline(), cvtPackStringp, caseBodyBeginp};
        casep->addItemsp(caseItemp);
        clearBindFlagBeforeLoop(casep);
    }
    void clearBindFlagBeforeLoop(AstCase* casep) {
        AstBegin* outerBeginp = nullptr;
        for (AstNode* nodep = getParentp(casep); nodep; nodep = getParentp(nodep)) {
            if (VN_IS(nodep, Always)) break;
            if (AstBegin* const beginp = VN_CAST(nodep, Begin)) outerBeginp = beginp;
        }
        UASSERT_OBJ(outerBeginp && outerBeginp->stmtsp(), casep,
                    "DPI-hook: target filter case outside its always block");
        AstVarRef* const condWriteRefp
            = new AstVarRef{m_targetModp->fileline(), m_condVarp, VAccess::WRITE};
        outerBeginp->stmtsp()->addHereThisAsNext(new AstAssign{
            m_targetModp->fileline(), condWriteRefp, new AstConst{m_targetModp->fileline(), 0}});
    }
    static AstNodeExpr* aggregateSelFromp(AstNode* nodep) {
        if (AstStructSel* const structSelp = VN_CAST(nodep, StructSel)) return structSelp->fromp();
        if (AstArraySel* const arraySelp = VN_CAST(nodep, ArraySel)) return arraySelp->fromp();
        return nullptr;
    }
    void redirectAggregateReads(AstVar* aggregateVarp) {
        AstVar* const mirrorVarp = m_targetEntry.origVarp;
        const int totalW = mirrorVarp->width();
        std::vector<AstNodeExpr*> targetps;
        foreachModule([&](AstNode* nodep) {
            AstNodeVarRef* const refp = VN_CAST(nodep, NodeVarRef);
            if (!refp || refp->varp() != aggregateVarp || !refp->access().isReadOnly()) return;
            AstNode* curp = refp;
            while (AstNode* const parentp = curp->backp()) {
                if (aggregateSelFromp(parentp) == curp) {
                    curp = parentp;
                } else {
                    break;
                }
            }
            for (AstNode* ancestorp = curp->backp(); ancestorp; ancestorp = ancestorp->backp()) {
                if (AstNodeAssign* const assignp = VN_CAST(ancestorp, NodeAssign)) {
                    AstVarRef* const lhsRefp = VN_CAST(assignp->lhsp(), VarRef);
                    if (lhsRefp && lhsRefp->varp() == mirrorVarp) return;
                    break;
                }
            }
            AstNodeExpr* const outerp = VN_CAST(curp, NodeExpr);
            if (!outerp || !isAggregateLeafDType(outerp->dtypep())) return;
            targetps.push_back(outerp);
        });
        for (AstNodeExpr* const outerp : targetps)
            redirectOneLeafAccess(aggregateVarp, outerp, totalW);
    }
    void redirectOneLeafAccess(AstVar* aggregateVarp, AstNodeExpr* outerp, int totalW) {
        FileLine* const fl = outerp->fileline();
        AstNode* rootp = outerp;  // The reference the select chainps starts from
        while (AstNode* const fromp = aggregateSelFromp(rootp)) rootp = fromp;
        AstNodeExpr* const selReadp = newSelReadp(fl, rootp, m_selResVarp);
        std::vector<AstNode*> chainps;
        for (AstNode* curp = outerp; aggregateSelFromp(curp); curp = aggregateSelFromp(curp))
            chainps.push_back(curp);
        std::reverse(chainps.begin(), chainps.end());
        AstNodeDType* dtypep = aggregateVarp->dtypep()->skipRefp();
        AstNodeDType* const idxDTypep
            = aggregateVarp->findLogicRangeDType(VNumRange{31, 0}, 32, VSigning::NOSIGN);
        int constMsbOff = 0;
        AstNodeExpr* dynp = nullptr;
        for (AstNode* const stepp : chainps) {
            if (AstStructSel* const structSelp = VN_CAST(stepp, StructSel)) {
                AstStructDType* const structp = VN_CAST(dtypep, StructDType);
                AstNodeDType* memberDTypep = nullptr;
                for (AstMemberDType* memberp = structp->membersp(); memberp;
                     memberp = VN_CAST(memberp->nextp(), MemberDType)) {
                    if (memberp->name() == structSelp->name()) {
                        memberDTypep = memberp->subDTypep();
                        break;
                    }
                    constMsbOff += aggregateBitWidth(memberp->subDTypep());
                }
                dtypep = memberDTypep->skipRefp();
            } else {
                AstArraySel* const arraySelp = VN_AS(stepp, ArraySel);
                AstUnpackArrayDType* const adtypep = VN_CAST(dtypep, UnpackArrayDType);
                const int stride = aggregateBitWidth(adtypep->subDTypep());
                if (AstConst* const idxConstp = VN_CAST(arraySelp->bitp(), Const)) {
                    constMsbOff += static_cast<int>(idxConstp->toUInt()) * stride;
                } else {
                    // The operands of the offset arithmetic take the width of the result
                    AstNodeExpr* idxp = arraySelp->bitp()->unlinkFrBack();
                    if (idxp->width() < idxDTypep->width()) {
                        idxp = new AstExtend{fl, idxp};
                        idxp->dtypep(idxDTypep);
                    }
                    AstMul* const mulp
                        = new AstMul{fl, idxp, new AstConst{fl, static_cast<uint32_t>(stride)}};
                    mulp->dtypep(idxDTypep);
                    if (!dynp) {
                        dynp = mulp;
                    } else {
                        AstAdd* const addp = new AstAdd{fl, dynp, mulp};
                        addp->dtypep(idxDTypep);
                        dynp = addp;
                    }
                }
                dtypep = adtypep->subDTypep()->skipRefp();
            }
        }
        const int leafW = outerp->dtypep()->skipRefp()->width();
        const int constLsb = totalW - leafW - constMsbOff;
        AstNodeExpr* lsbp;
        if (!dynp) {
            lsbp = new AstConst{fl, static_cast<uint32_t>(constLsb)};
        } else {
            AstSub* const subp
                = new AstSub{fl, new AstConst{fl, static_cast<uint32_t>(constLsb)}, dynp};
            subp->dtypep(idxDTypep);
            lsbp = subp;
        }
        AstSel* const sliceSelp = new AstSel{fl, selReadp, lsbp, leafW};
        sliceSelp->dtypep(outerp->dtypep());
        outerp->replaceWith(sliceSelp);
        VL_DO_DANGLING(outerp->deleteTree(), outerp);
    }
    void insertSelResVar(AstVar* hookedVarp, AstVar* targetVarp) {
        m_selResVarp
            = new AstVar{m_targetModp->fileline(), VVarType::VAR,
                         "__Vdpihook_sel_res__" + hookBaseName(targetVarp), hookedVarp->dtypep()};
        m_selResVarp->lifetime(VLifetime::STATIC_IMPLICIT);
        m_selResVarp->trace(false);
        if (m_targetEntry.isAggregateMirror) {
            m_targetModp->addStmtsp(m_selResVarp);
            redirectAggregateReads(m_targetEntry.aggregateVarp);
            redirectViewReads(m_targetEntry.aggregateVarp, targetVarp);
            return;
        }
        if (m_targetEntry.hasElemIndex()) {
            m_targetModp->addStmtsp(m_selResVarp);
            redirectElementReads(targetVarp);
            redirectViewReads(targetVarp, targetVarp);
            return;
        }
        if (m_targetEntry.hasMemberStep()) {
            m_targetModp->addStmtsp(m_selResVarp);
            redirectMemberReads(targetVarp);
            redirectViewReads(targetVarp, targetVarp);
            return;
        }
        m_targetModp->addStmtsp(m_selResVarp);
        if (targetVarp->isOutputish()) {
            // Drivers write the pre-hook var, and the port holds the hook result, so
            // every reader sees the result without a redirect
            insertTargetAssign(targetVarp);
            return;
        }
        insertIfaceModportMember(m_selResVarp, VDirection::INPUT);
        // Redirect the collected reads
        for (AstNodeAssign* const assignp : m_targetEntry.assignps)
            redirectAssignReads(assignp, targetVarp);
        redirectTargetReads();
    }
    string hookBaseName(const AstVar* targetVarp) const {
        return targetVarp->name() + m_targetEntry.accessPathSuffix()
               + m_targetEntry.genScopeSuffix();
    }
    void insertCondVar(AstVar* targetVarp) {
        m_condVarp = new AstVar{m_targetModp->fileline(), VVarType::VAR,
                                "__Vdpihook_sel_cond__" + hookBaseName(targetVarp),
                                VFlagLogicPacked{}, 1};
        m_condVarp->lifetime(VLifetime::STATIC_IMPLICIT);
        m_condVarp->trace(false);
        m_targetModp->addStmtsp(m_condVarp);
    }
    void insertCaseIdVar(AstVar* targetVarp) {
        AstBasicDType* const idDTypep
            = new AstBasicDType{m_targetModp->fileline(), VBasicDTypeKwd::INT, VSigning::SIGNED};
        idDTypep->generic(true);
        m_typeTablep->addTypesp(idDTypep);
        m_caseIdVarp = new AstVar{m_targetModp->fileline(), VVarType::VAR,
                                  "__Vdpihook_case_id__" + hookBaseName(targetVarp), idDTypep};
        m_caseIdVarp->lifetime(VLifetime::STATIC_IMPLICIT);
        m_caseIdVarp->trace(false);
        m_targetModp->addStmtsp(m_caseIdVarp);
    }
    static int callbackWidth(const AstNodeFTask* ftaskp) {
        if (VN_IS(ftaskp, Func)) return ftaskp->dtypep()->width();
        return VN_AS(ftaskp->declsp(), Var)->width();
    }
    // Insert import of callback, or reuse import from earlier target in this container
    bool insertDpiImport() {
        AstVar* const targetVarp = m_targetEntry.hookedVarp;
        AstNodeFTask*& ftaskp = m_callbackCache[{m_targetModp, m_targetEntry.callback}];
        if (ftaskp) {
            const int existingWidth = callbackWidth(ftaskp);
            if (existingWidth != targetVarp->width()) {
                targetVarp->v3error(
                    "DPI-hook callback '"
                    << m_targetEntry.callback << "' is reused for a target of width "
                    << targetVarp->width() << ", but was already used for width " << existingWidth
                    << '\n'
                    << targetVarp->warnMore()
                    << "... Suggest use a distinct callback name per signal width");
                return false;
            }
        } else {
            if (AstNodeFTask* const userFTaskp
                = m_lookups.ftaskp(m_targetModp, m_targetEntry.callback)) {
                userFTaskp->v3error(
                    "DPI-hook callback '"
                    << m_targetEntry.callback << "' of target '" << m_targetEntry.origTarget
                    << "' has the name of this function or task\n"
                    << userFTaskp->warnMore() << "... Suggest use another callback name");
                return false;
            }
            ftaskp = newDpiImportp();
            ftaskp->dpiImport(true);
            ftaskp->prototype(true);
            if (AstFunc* const funcp = VN_CAST(ftaskp, Func)) funcp->verilogFunction(true);
            m_targetModp->addStmtsp(ftaskp);
        }
        m_funcp = VN_CAST(ftaskp, Func);
        m_taskp = VN_CAST(ftaskp, Task);
        return true;
    }
    void insertHandler(AstVar* hookedVarp, AstVar* targetVarp) {
        m_targetModp->addStmtsp(buildHandlerp(hookedVarp, targetVarp));
    }
    AstVar* newHookedVarp() const {
        AstVar* const hookedVarp = m_targetEntry.origVarp->cloneTree(false);
        if (m_targetEntry.hookedDTypep) hookedVarp->dtypep(m_targetEntry.hookedDTypep);
        hookedVarp->name(m_targetEntry.hookedName);
        hookedVarp->origName(m_targetEntry.hookedName);
        hookedVarp->varType(VVarType::VAR);
        hookedVarp->trace(false);
        return hookedVarp;
    }
    void insertHookedVar(AstVar* hookedVarp, AstVar* targetVarp) {
        if (targetVarp->direction() != VDirection::NONE) hookedVarp->direction(VDirection::NONE);
        m_targetModp->addStmtsp(hookedVarp);
    }
    AstCase* insertTargetFilterp() {
        AstVar* const hookPathVarp = findHookPathVarp();
        // Add filter logic providing path information to the modules/instances
        // Create the loop-index and decoded-part dtypes (fresh per target filter)
        AstBasicDType* const loopVarDTypep
            = new AstBasicDType{m_targetModp->fileline(), VBasicDTypeKwd::INT, VSigning::SIGNED};
        loopVarDTypep->generic(true);
        m_typeTablep->addTypesp(loopVarDTypep);
        AstBasicDType* const stringDTypep
            = new AstBasicDType{m_targetModp->fileline(), VBasicDTypeKwd::STRING};
        stringDTypep->generic(true);
        m_typeTablep->addTypesp(stringDTypep);
        PathFilterConfig cfg;
        cfg.modp = m_targetModp;
        cfg.intDTypep = loopVarDTypep;
        cfg.stringDTypep = stringDTypep;
        cfg.hookPathVarp = hookPathVarp;
        cfg.targetVarName = "__Vdpihook_target_part";
        cfg.targetVarLifetime = VLifetime::AUTOMATIC_IMPLICIT;
        cfg.targetVarHasUserInit = true;
        cfg.declTargetInLoopBody = true;  // declared in the loop body
        cfg.alwaysName = "__Vdpihook_target_filter";
        cfg.caseCachep = &m_caseCache;
        cfg.loopVarCachep = &m_targetLoopVarCache;
        const PathFilterResult res = buildPathFilter(cfg);
        res.targetSelp->dtypep(hookPathVarp->dtypep());
        return res.casep;
    }

public:
    DpiOverrideBuilder(
        AstNodeModule* targetModp, AstTypeTable* typeTablep, AstVar* dpiTriggerVarp,
        HookInsertEntry& targetEntry, std::unordered_map<AstNodeModule*, AstCase*>& caseCache,
        std::unordered_map<AstNodeModule*, AstVar*>& targetLoopVarCache,
        std::map<std::pair<const AstNodeModule*, string>, AstNodeFTask*>& callbackCache,
        HookLookups& lookups)
        : m_targetModp{targetModp}
        , m_typeTablep{typeTablep}
        , m_dpiTriggerVarp{dpiTriggerVarp}
        , m_targetEntry{targetEntry}
        , m_caseCache{caseCache}
        , m_targetLoopVarCache{targetLoopVarCache}
        , m_callbackCache{callbackCache}
        , m_lookups{lookups} {}
    void insert() {
        VL_RESTORER(m_selResVarp);
        m_targetEntry.hookedVarp = newHookedVarp();
        AstVar* const hookedVarp = m_targetEntry.hookedVarp;
        AstVar* const targetVarp = m_targetEntry.origVarp;
        // Insert Task/Function
        if (!insertDpiImport()) {
            VL_DO_DANGLING(m_targetEntry.hookedVarp->deleteTree(), m_targetEntry.hookedVarp);
            return;
        }
        // Drive an output port from the hook result
        routeOutputDrivers(targetVarp);
        // Give a "var[i]" target a scalar view of the selected element
        routeElementTarget(targetVarp);
        // Give a "u.a" member/index target a scalar view of the addressed leaf
        routeMemberTarget(targetVarp);
        // Route an interface signal's cross-module drivers through a pre-hook var
        routeIfaceDrivers(targetVarp);
        // Insert hooked vars and selection logic
        insertCondVar(targetVarp);
        insertCaseIdVar(targetVarp);
        insertHookedVar(hookedVarp, targetVarp);
        insertSelResVar(hookedVarp, targetVarp);
        // Insert the override handler (buildHandlerp branches func vs. task internally)
        insertHandler(hookedVarp, targetVarp);
        AstCase* casep = findTargetFilterp();
        if (!casep) casep = insertTargetFilterp();
        insertCaseItem(targetVarp, casep);
        m_targetEntry.done = true;
    }
};

class DpiHookInserter final {
    // MEMBERS
    AstNetlist* m_netlistp;  // Netlist under transformation
    std::map<string, HookInsertTarget>& m_insertCfg;  // Resolved target configs
    std::map<std::tuple<const AstNodeModule*, const AstVar*, string>, const HookInsertEntry*>
        m_doneEntries;  // Built entries, by container, variable and access path

    // METHODS
    static std::tuple<const AstNodeModule*, const AstVar*, string>
    doneKey(const AstNodeModule* modp, const HookInsertEntry& entry) {
        return std::make_tuple(modp, entry.origVarp, entry.accessPathText());
    }
    const HookInsertEntry* existingEntryp(AstNodeModule* modp, const HookInsertEntry& candidate) {
        const auto it = m_doneEntries.find(doneKey(modp, candidate));
        return it == m_doneEntries.end() ? nullptr : it->second;
    }

public:
    DpiHookInserter(AstNetlist* netlistp, std::map<string, HookInsertTarget>& insertCfg)
        : m_netlistp{netlistp}
        , m_insertCfg{insertCfg} {}

    void insertDpiHooks() {
        AstTypeTable* const typeTablep = VN_CAST(m_netlistp->miscsp(), TypeTable);
        DTypeCache dtypeCache;
        std::unordered_map<AstNodeModule*, AstCase*> caseCache;
        std::unordered_map<AstNodeModule*, AstVar*> targetLoopVarCache;
        std::map<std::pair<const AstNodeModule*, string>, AstNodeFTask*> callbackCache;
        std::unordered_map<AstNodeModule*, std::set<string>> caseChildCells;
        HookLookups lookups;
        std::vector<std::pair<string, HookInsertTarget*>> sortedCfg;
        for (auto& itr : m_insertCfg) sortedCfg.emplace_back(itr.first, &itr.second);

        // descending Depth (Amount of elements in modps)
        std::stable_sort(sortedCfg.begin(), sortedCfg.end(), [](const auto& a, const auto& b) {
            const size_t depthA = a.second->modps.size();
            const size_t depthB = b.second->modps.size();
            return depthA > depthB;  // bigger = deeper = earlier
        });
        for (const auto& itr : sortedCfg) {
            HookInsertTarget* const target = itr.second;
            if (target->error) continue;
            HookPathRouter pathRouter{m_netlistp,         *target,        dtypeCache, caseCache,
                                      targetLoopVarCache, caseChildCells, lookups};
            pathRouter.insert();
            // Insert hook logic for each entry
            for (auto& entry : target->entries) {
                if (!entry.found) continue;
                AstVar* const origVarp = entry.origVarp;
                const HookInsertEntry* const priorp
                    = existingEntryp(target->hookLogicContainerp(), entry);
                if (!priorp) {
                    DpiOverrideBuilder overrideBuilder{target->hookLogicContainerp(),
                                                       typeTablep,
                                                       target->dpiTriggerVarp,
                                                       entry,
                                                       caseCache,
                                                       targetLoopVarCache,
                                                       callbackCache,
                                                       lookups};
                    overrideBuilder.insert();
                    if (entry.done)
                        m_doneEntries.emplace(doneKey(target->hookLogicContainerp(), entry),
                                              &entry);
                } else if (priorp->callback != entry.callback) {
                    origVarp->v3error("DPI-hook target '" << entry.origTarget
                                                          << "' is already hooked with callback '"
                                                          << priorp->callback << "'");
                }
            }
        }
        if (V3Error::errorCount()) return;
        insertDefaultCases(caseCache);
        insertBindCheck(m_netlistp, lookups);
    }
};

//######################################################################
// Hook-insertion class functions

static std::map<string, HookInsertTarget> buildWorkingCfg() {
    std::map<string, HookInsertTarget> insertCfg;
    for (const auto& itr : V3Control::getHookInsertCfg()) {
        const string& targetName = itr.first;
        HookInsertTarget& target = insertCfg[targetName];
        for (const HookInsertCfgEntry& cfgEntry : itr.second) {
            HookInsertEntry entry;
            entry.callback = cfgEntry.callback;
            entry.varTarget = cfgEntry.varTarget;
            entry.accessPath = cfgEntry.accessPath;
            entry.cfgFl = cfgEntry.fl;
            entry.origTarget = targetName + "." + cfgEntry.varTarget;
            for (const DpiHookStep& step : cfgEntry.accessPath) {
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
    // Insertion phase: mutate the AST using the resolved pointers.
    DpiHookInserter inserter{nodep, insertCfg};
    inserter.insertDpiHooks();
    V3Global::dumpCheckGlobalTree("insertDpiHook", 0, dumpTreeEitherLevel() >= 3);
}
