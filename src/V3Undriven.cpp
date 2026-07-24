// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Check for unused/undriven signals
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2004-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Undriven's Transformations:
//
// Netlist:
//      Make vector for all variables
//      SEL(VARREF(...))) mark only some bits as used/driven
//      else VARREF(...) mark all bits as used/driven
//      Report unused/undriven nets
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Undriven.h"

#include "V3Stats.h"
#include "V3UndrivenCapture.h"
#include "V3Width.h"

#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Class for every variable we may process

class UndrivenVarEntry final {
    // MEMBERS
    AstVar* const m_varp;  // Variable this tracks
    std::vector<bool> m_wholeFlags;  // Used/Driven on whole vector
    std::vector<bool> m_bitFlags;  // Used/Driven on each subbit
    const AstNode* m_usedNotDrivenp = nullptr;  // First read before any write
    const AstAlways* m_alwCombp
        = nullptr;  // always_comb of var if driven within always_comb, else nullptr
    const AstAlways* m_alwFFp = nullptr;  // always_ff of var if driven within always_ff
    const AstAlways* m_alwPlainp = nullptr;  // plain always of var if driven within plain always
    const AstNodeVarRef* m_nodep = nullptr;  // varref if driven, else nullptr
    const AstNode* m_initStaticp = nullptr;  // varref if in InitialStatic driven
    const AstNode* m_initialp = nullptr;  // varref if driven in an explicit initial block
    const AstNode* m_contAssignp = nullptr;  // varref if in continuous assignment driven
    const AstNode* m_procWritep = nullptr;  // varref if written in process
    bool m_underGen = false;  // Under a generate
    bool m_ftaskDriven = false;  // Last driven by function or task

    const AstNodeFTaskRef* m_callNodep = nullptr;  // Call node if driven via writeSummary

    enum : uint8_t {
        FLAG_USED = 0,  // Signal or bit has been read/observed
        FLAG_DRIVEN = 1,  // Signal or bit has been written/driven
        FLAG_DRIVEN_ALWCOMB = 2,  // Whole signal has been driven from always_comb
        FLAG_DRIVEN_ALWFF = 3,  // Whole signal has been driven from always_ff
        FLAG_DRIVEN_ALWPLAIN = 4,  // Whole signal has been driven from a plain always
        FLAGS_PER_BIT = 5  // Number of flags stored for each tracked bit
    };

public:
    // CONSTRUCTORS
    explicit UndrivenVarEntry(AstVar* varp)
        : m_varp{varp} {  // Construction for when a var is used
        UINFO(9, "create " << varp);
        m_wholeFlags.resize(FLAGS_PER_BIT);
        for (int i = 0; i < FLAGS_PER_BIT; i++) m_wholeFlags[i] = false;
        m_bitFlags.resize(varp->width() * FLAGS_PER_BIT);
        for (int i = 0; i < varp->width() * FLAGS_PER_BIT; i++) m_bitFlags[i] = false;
    }
    ~UndrivenVarEntry() = default;

private:
    // METHODS
    bool bitNumOk(int bit) const {
        return bit >= 0 && (bit * FLAGS_PER_BIT < static_cast<int>(m_bitFlags.size()));
    }
    bool usedFlag(int bit) const {
        return m_wholeFlags[FLAG_USED] || m_bitFlags[bit * FLAGS_PER_BIT + FLAG_USED];
    }
    bool drivenFlag(int bit) const {
        return m_wholeFlags[FLAG_DRIVEN] || m_bitFlags[bit * FLAGS_PER_BIT + FLAG_DRIVEN];
    }
    int bitCount() const { return m_bitFlags.size() / FLAGS_PER_BIT; }
    void recordUsedNotDriven(const AstNode* nodep) {
        if (!m_usedNotDrivenp) m_usedNotDrivenp = nodep;
    }
    enum BitNamesWhich : uint8_t { BN_UNUSED, BN_UNDRIVEN, BN_BOTH };
    string bitNames(BitNamesWhich which) {
        string bits;
        bool prev = false;
        int msb = 0;
        // bit==-1 loops below; we do one extra iteration so end with prev=false
        for (int bit = (m_bitFlags.size() / FLAGS_PER_BIT) - 1; bit >= -1; --bit) {
            if (bit >= 0
                && ((which == BN_UNUSED && !usedFlag(bit) && drivenFlag(bit))
                    || (which == BN_UNDRIVEN && usedFlag(bit) && !drivenFlag(bit))
                    || (which == BN_BOTH && !usedFlag(bit) && !drivenFlag(bit)))) {
                if (!prev) {
                    prev = true;
                    msb = bit;
                }
            } else if (prev) {
                const AstBasicDType* const bdtypep = m_varp->basicp();
                const int lsb = bit + 1;
                if (bits != "") bits += ",";
                if (lsb == msb) {
                    bits += cvtToStr(lsb + bdtypep->lo());
                } else {
                    if (bdtypep->ascending()) {
                        bits
                            += cvtToStr(lsb + bdtypep->lo()) + ":" + cvtToStr(msb + bdtypep->lo());
                    } else {
                        bits
                            += cvtToStr(msb + bdtypep->lo()) + ":" + cvtToStr(lsb + bdtypep->lo());
                    }
                }
                prev = false;
            }
        }
        return "[" + bits + "]";
    }

public:
    void usedWhole(const AstNode* nodep) {
        UINFO(9, "set u[*] " << m_varp->name() << " " << nodep);
        if (!m_wholeFlags[FLAG_DRIVEN]) {
            for (int bit = 0; bit < bitCount(); ++bit) {
                if (!drivenFlag(bit)) {
                    recordUsedNotDriven(nodep);
                    break;
                }
            }
        }
        m_wholeFlags[FLAG_USED] = true;
    }
    void drivenWhole(const AstNode* nodep) {
        UINFO(9, "set d[*] " << m_varp->name() << " " << nodep);
        m_wholeFlags[FLAG_DRIVEN] = true;
    }
    void drivenWhole(const AstNodeVarRef* nodep, bool ftaskDef) {
        m_ftaskDriven = ftaskDef && !isDrivenWhole();
        drivenWhole(nodep);
        m_nodep = nodep;
    }
    void drivenAlwaysCombWhole(const AstAlways* alwCombp) {
        m_wholeFlags[FLAG_DRIVEN_ALWCOMB] = true;
        m_alwCombp = alwCombp;
    }
    void drivenAlwaysFFWhole(const AstAlways* alwFFp, const AstVar* varp) {
        m_wholeFlags[FLAG_DRIVEN_ALWFF] = true;
        m_alwFFp = alwFFp;
    }
    void drivenAlwaysPlainWhole(const AstAlways* alwPlainp) {
        m_wholeFlags[FLAG_DRIVEN_ALWPLAIN] = true;
        m_alwPlainp = alwPlainp;
    }

    const AstNode* initStaticp() const { return m_initStaticp; }
    void initStaticp(const AstNode* nodep) { m_initStaticp = nodep; }
    const AstNode* initialp() const { return m_initialp; }
    void initialp(const AstNode* nodep) { m_initialp = nodep; }
    const AstNode* contAssignp() const { return m_contAssignp; }
    void contAssignp(const AstNode* nodep) { m_contAssignp = nodep; }
    const AstNode* procWritep() const { return m_procWritep; }
    void procWritep(const AstNode* nodep) { m_procWritep = nodep; }
    void underGenerate() { m_underGen = true; }
    bool isUnderGen() const { return m_underGen; }
    bool isDrivenWhole() const { return m_wholeFlags[FLAG_DRIVEN]; }
    bool isDrivenAlwaysCombWhole() const { return m_wholeFlags[FLAG_DRIVEN_ALWCOMB]; }
    bool isDrivenAlwaysFFWhole() const { return m_wholeFlags[FLAG_DRIVEN_ALWFF]; }
    bool isDrivenAlwaysPlainWhole() const { return m_wholeFlags[FLAG_DRIVEN_ALWPLAIN]; }
    bool isFtaskDriven() const { return m_ftaskDriven; }
    const AstNodeVarRef* getNodep() const { return m_nodep; }
    const AstAlways* getAlwCombp() const { return m_alwCombp; }
    const AstAlways* getAlwFFp() const { return m_alwFFp; }
    const AstAlways* getAlwPlainp() const { return m_alwPlainp; }
    void usedBit(int bit, int width, const AstNode* nodep) {
        UINFO(9, "set u[" << (bit + width - 1) << ":" << bit << "] " << m_varp->name());
        for (int i = 0; i < width; i++) {
            if (bitNumOk(bit + i)) {
                if (!drivenFlag(bit + i)) recordUsedNotDriven(nodep);
                m_bitFlags[(bit + i) * FLAGS_PER_BIT + FLAG_USED] = true;
            }
        }
    }
    void drivenBit(int bit, int width) {
        UINFO(9, "set d[" << (bit + width - 1) << ":" << bit << "] " << m_varp->name());
        for (int i = 0; i < width; i++) {
            if (bitNumOk(bit + i)) m_bitFlags[(bit + i) * FLAGS_PER_BIT + FLAG_DRIVEN] = true;
        }
    }
    bool isUsedNotDrivenBit(int bit, int width) const {
        for (int i = 0; i < width; i++) {
            if (bitNumOk(bit + i)
                && (m_wholeFlags[FLAG_USED] || m_bitFlags[(bit + i) * FLAGS_PER_BIT + FLAG_USED])
                && !(m_wholeFlags[FLAG_DRIVEN]
                     || m_bitFlags[(bit + i) * FLAGS_PER_BIT + FLAG_DRIVEN]))
                return true;
        }
        return false;
    }
    bool isUsedNotDrivenAny() const {
        return isUsedNotDrivenBit(0, m_bitFlags.size() / FLAGS_PER_BIT);
    }
    const AstNode* firstUsedNotDrivenp() const { return m_usedNotDrivenp; }
    static bool unusedMatch(AstVar* nodep) {
        const string regexp = v3Global.opt.unusedRegexp();
        if (regexp == "") return false;
        const string prettyName = nodep->prettyName();
        return VString::wildmatch(prettyName.c_str(), regexp.c_str());
    }
    void reportViolations() {
        // Combine bits into overall state
        AstVar* const nodep = m_varp;

        if (initStaticp() && procWritep() && nodep->hasUserInit() && !nodep->isClassMember()
            && !nodep->isFuncLocal()) {
            initStaticp()->v3warn(
                PROCASSINIT,
                "Procedural assignment to declaration with initial value: "
                    << nodep->prettyNameQ() << '\n'
                    << initStaticp()->warnMore() << "... Location of variable initialization\n"
                    << initStaticp()->warnContextPrimary() << '\n'
                    << procWritep()->warnOther() << "... Location of variable process write\n"
                    << procWritep()->warnMore()
                    << "... Perhaps should initialize instead using a reset in this process\n"
                    << procWritep()->warnContextSecondary());
        }
        const AstNode* const initp = nodep->hasUserInit() ? initStaticp() : initialp();
        if (initp && contAssignp() && !nodep->isClassMember() && !nodep->isFuncLocal()) {
            initp->v3warn(E_CONTASSINIT, "Continuous assignment to variable with initial value: "
                                             << nodep->prettyNameQ() << '\n'
                                             << initp->warnMore()
                                             << "... Location of variable initialization\n"
                                             << initp->warnContextPrimary() << '\n'
                                             << contAssignp()->warnOther()
                                             << "... Location of continuous assignment\n"
                                             << contAssignp()->warnContextSecondary());
        }
        if (nodep->isGenVar()) {  // Genvar
            if (!nodep->isIfaceRef() && !nodep->isUsedParam() && !unusedMatch(nodep)) {
                nodep->v3warn(UNUSEDGENVAR, "Genvar is not used: " << nodep->prettyNameQ());
                nodep->fileline()->modifyWarnOff(V3ErrorCode::UNUSEDGENVAR,
                                                 true);  // Warn only once
            }
        } else if (nodep->isParam()) {  // Parameter
            if (!nodep->isIfaceRef() && !nodep->isUsedParam() && !unusedMatch(nodep)) {
                nodep->v3warn(UNUSEDPARAM, "Parameter is not used: " << nodep->prettyNameQ());
                nodep->fileline()->modifyWarnOff(V3ErrorCode::UNUSEDPARAM,
                                                 true);  // Warn only once
            }
        } else {  // Signal
            const string varType{nodep->isFuncLocal() ? "Function variable" : "Signal"};
            const bool funcInout = nodep->isFuncLocal() && nodep->isInout();
            bool allU = true;
            bool allD = true;
            bool anyU = m_wholeFlags[FLAG_USED];
            bool anyD = m_wholeFlags[FLAG_DRIVEN];
            bool anyUnotD = false;
            bool anyDnotU = false;
            bool anynotDU = false;
            for (unsigned bit = 0; bit < m_bitFlags.size() / FLAGS_PER_BIT; bit++) {
                const bool used = usedFlag(bit);
                const bool driv = drivenFlag(bit);
                allU &= used;
                anyU |= used;
                allD &= driv;
                anyD |= driv;
                anyUnotD |= used && !driv;
                anyDnotU |= !used && driv;
                anynotDU |= !used && !driv;
            }
            if (funcInout) {
                if (anyD) allU = true;
                allD = true;
            }
            if (allU) m_wholeFlags[FLAG_USED] = true;
            if (allD) m_wholeFlags[FLAG_DRIVEN] = true;
            // Test results
            if (nodep->isIfaceRef()) {
                // For interface top level we don't do any tracking
                // Ideally we'd report unused instance cells, but presumably a signal inside one
                // would get reported as unused
            } else if (allU && allD) {
                // It's fine
            } else if (!anyD && !anyU) {
                // UNDRIVEN is considered more serious - as is more likely a bug,
                // thus undriven+unused bits get UNUSED warnings, as they're not as buggy.
                if (!unusedMatch(nodep)) {
                    nodep->v3warn(UNUSEDSIGNAL,
                                  varType << " is not driven, nor used: " << nodep->prettyNameQ());
                    nodep->fileline()->modifyWarnOff(V3ErrorCode::UNUSEDSIGNAL,
                                                     true);  // Warn only once
                }
            } else if (allD && !anyU) {
                if (!unusedMatch(nodep)) {
                    nodep->v3warn(UNUSEDSIGNAL,
                                  varType << " is not used: " << nodep->prettyNameQ());
                    nodep->fileline()->modifyWarnOff(V3ErrorCode::UNUSEDSIGNAL,
                                                     true);  // Warn only once
                }
            } else if (!anyD && allU) {
                nodep->v3warn(UNDRIVEN, varType << " is not driven: " << nodep->prettyNameQ());
                nodep->fileline()->modifyWarnOff(V3ErrorCode::UNDRIVEN, true);  // Warn only once
            } else if (!funcInout) {
                // Bits have different dispositions
                const std::string varTypeLower = [&varType]() {
                    std::string str = varType;
                    str[0] = std::tolower(static_cast<unsigned char>(str[0]));
                    return str;
                }();
                bool setU = false;
                bool setD = false;
                if (anynotDU && !unusedMatch(nodep)) {
                    nodep->v3warn(UNUSEDSIGNAL,
                                  "Bits of " << varTypeLower << " are not driven, nor used: "
                                             << nodep->prettyNameQ() << bitNames(BN_BOTH));
                    setU = true;
                }
                if (anyDnotU && !unusedMatch(nodep)) {
                    nodep->v3warn(UNUSEDSIGNAL, "Bits of " << varTypeLower << " are not used: "
                                                           << nodep->prettyNameQ()
                                                           << bitNames(BN_UNUSED));
                    setU = true;
                }
                if (anyUnotD) {
                    nodep->v3warn(UNDRIVEN, "Bits of " << varTypeLower << " are not driven: "
                                                       << nodep->prettyNameQ()
                                                       << bitNames(BN_UNDRIVEN));
                    setD = true;
                }
                if (setU) {  // Warn only once
                    nodep->fileline()->modifyWarnOff(V3ErrorCode::UNUSEDSIGNAL, true);
                }
                if (setD) {  // Warn only once
                    nodep->fileline()->modifyWarnOff(V3ErrorCode::UNDRIVEN, true);
                }
            }
        }
    }

    void drivenViaCall(const AstNodeFTaskRef* nodep) {
        drivenWhole(nodep);
        if (!m_callNodep) m_callNodep = nodep;
    }
    const AstNodeFTaskRef* callNodep() const { return m_callNodep; }
};

//######################################################################
// Undriven state, as a visitor of each AstNode

class UndrivenVisitor final : public VNVisitorConst {
    // NODE STATE
    // Netlist:
    //  AstVar::user1p          -> UndrivenVar* for usage var, 0=not set yet
    const VNUser1InUse m_inuser1;
    // Each always:
    //  AstNode::user2p         -> UndrivenVar* for usage var, 0=not set yet
    const VNUser2InUse m_inuser2;

    // STATE
    std::array<std::vector<UndrivenVarEntry*>, 3> m_entryps = {};  // Nodes to delete when finished
    bool m_inBBox = false;  // In black box; mark as driven+used
    bool m_inContAssign = false;  // In continuous assignment
    bool m_inInitial = false;  // In explicit initial block
    bool m_inInitialSetup = false;  // In InitialAutomatic*/InitialStatic* assignment LHS
    bool m_inInitialStatic = false;  // In InitialStatic
    bool m_inProcAssign = false;  // In procedural assignment
    bool m_inFTaskRef = false;  // In function or task call
    bool m_inInoutOrRefPin = false;  // Connected to pin that is inout
    bool m_inSelLhs = false;  // Iterating the fromp of an AstSel (a partial-bit write target)
    const AstNodeFTask* m_taskp = nullptr;  // Current task
    const AstAlways* m_alwaysp = nullptr;  // Current always of either type
    const AstAlways* m_alwaysCombp = nullptr;  // Current always if combo, otherwise nullptr
    const AstAlways* m_alwaysFFp = nullptr;  // Current always if ff, otherwise nullptr
    const AstAlways* m_alwaysPlainp = nullptr;  // Current always if plain (not comb/ff/latch)

    V3UndrivenCapture* const m_capturep = nullptr;  // Capture object.  'nullptr' if disabled.

    // METHODS

    UndrivenVarEntry* getEntryp(AstVar* nodep, int which_user) {
        if (!(which_user == 1 ? nodep->user1p() : nodep->user2p())) {
            UndrivenVarEntry* const entryp = new UndrivenVarEntry{nodep};
            // UINFO(9," Associate u="<<which_user<<" "<<cvtToHex(this)<<" "<<nodep->name()<<endl);
            m_entryps[which_user].push_back(entryp);
            if (which_user == 1) {
                nodep->user1p(entryp);
            } else if (which_user == 2) {
                nodep->user2p(entryp);
            } else {
                nodep->v3fatalSrc("Bad case");
            }
            return entryp;
        } else {
            UndrivenVarEntry* const entryp = reinterpret_cast<UndrivenVarEntry*>(
                which_user == 1 ? nodep->user1p() : nodep->user2p());
            return entryp;
        }
    }

    void warnAlwCombOrder(AstNodeVarRef* nodep, const AstNode* readp) {
        AstVar* const varp = nodep->varp();
        if (!varp->isParam() && !varp->isGenVar() && !varp->isUsedLoopIdx()
            && !varp->ignoreSchedWrite()
            && !m_inBBox  // We may have falsely considered a SysIgnore as a driver
            && !VN_IS(nodep, VarXRef)  // Xrefs might point at two different instances
            && !varp->fileline()->warnIsOff(
                V3ErrorCode::ALWCOMBORDER)) {  // Warn only once per variable
            nodep->v3warn(ALWCOMBORDER,
                          "always_comb reads "
                              << nodep->prettyNameQ()
                              << " before assigning it later in the same block; behavior "
                                 "may imply latch/state-like behavior and is not purely "
                                 "combinational"
                              << (readp ? "\n" + readp->warnOther()
                                              + "... Location of earlier read\n"
                                              + readp->warnContextSecondary()
                                        : ""));
            varp->fileline()->modifyWarnOff(V3ErrorCode::ALWCOMBORDER,
                                            true);  // Complain just once for any usage
        }
    }

    // VISITORS
    void visit(AstVar* nodep) override {
        const bool funcInout = nodep->isFuncLocal() && nodep->isInout();
        for (int usr = 1; usr < (m_alwaysCombp ? 3 : 2); ++usr) {
            // For assigns and non-combo always, do just usr==1, to look
            // for module-wide undriven etc.
            // For combo always, run both usr==1 for above, and also
            // usr==2 for always-only checks.
            UndrivenVarEntry* const entryp = getEntryp(nodep, usr);
            if ((nodep->isNonOutput() && !funcInout) || nodep->isSigPublic()
                || nodep->hasUserInit() || nodep->isSigUserRWPublic()
                || (m_taskp && (m_taskp->dpiImport() || m_taskp->dpiExport()))) {
                entryp->drivenWhole(nodep);
            }
            if ((nodep->isWritable() && !funcInout) || nodep->isSigPublic()
                || nodep->isSigUserRWPublic() || nodep->isSigUserRdPublic()
                || (m_taskp && (m_taskp->dpiImport() || m_taskp->dpiExport()))) {
                entryp->usedWhole(nodep);
            }
            if (nodep->valuep()) entryp->drivenWhole(nodep->valuep());
        }
        // Discover variables used in bit definitions, etc
        iterateChildrenConst(nodep);
    }
    void visit(AstArraySel* nodep) override {
        // Arrays are rarely constant assigned, so for now we punt and do all entries
        iterateChildrenConst(nodep);
    }
    void visit(AstSliceSel* nodep) override {
        // Arrays are rarely constant assigned, so for now we punt and do all entries
        iterateChildrenConst(nodep);
    }
    void visit(AstSel* nodep) override {
        AstNodeVarRef* const varrefp = VN_CAST(nodep->fromp(), NodeVarRef);
        AstConst* const constp = VN_CAST(nodep->lsbp(), Const);
        if (varrefp && constp && !constp->num().isFourState()) {
            for (int usr = 1; usr < (m_alwaysCombp ? 3 : 2); ++usr) {
                UndrivenVarEntry* const entryp = getEntryp(varrefp->varp(), usr);
                const int lsb = constp->toUInt();
                if (m_inBBox || varrefp->access().isWriteOrRW()) {
                    // Don't warn if already driven earlier as "a=0; if(a) a=1;" is fine.
                    if (usr == 2 && m_alwaysCombp
                        && entryp->isUsedNotDrivenBit(lsb, nodep->width())) {
                        UINFO(9, " Select.  Entryp=" << cvtToHex(entryp));
                        warnAlwCombOrder(varrefp, entryp->firstUsedNotDrivenp());
                    }
                    entryp->drivenBit(lsb, nodep->width());
                }
                if (m_inBBox || !varrefp->access().isWriteOrRW())
                    entryp->usedBit(lsb, nodep->width(), varrefp);
            }
        } else {
            // skip over static longest static prefix
            iterateConst(nodep->lsbp());
            VL_RESTORER(m_inSelLhs);
            m_inSelLhs = !V3Width::selectNonConstantRecurse(nodep->lsbp(), /*inSel=*/true);
            iterateConst(nodep->fromp());
        }
    }
    void visit(AstNodeVarRef* nodep) override {
        // Any variable
        if (nodep->access().isWriteOrRW()
            && !VN_IS(nodep, VarXRef)) {  // Ignore interface variables and similar ugly items
            if (m_inProcAssign && !nodep->varp()->varType().isProcAssignable()
                && !nodep->varp()->isDeclTyped()  //
                && !nodep->varp()->isClassMember() && !nodep->varp()->isFuncLocal()) {
                nodep->v3warn(PROCASSWIRE, "Procedural assignment to wire, perhaps intended var"
                                               << " (IEEE 1800-2023 6.5): "
                                               << nodep->prettyNameQ());
            } else if (m_inContAssign && !nodep->varp()->varType().isContAssignable()
                       && !nodep->fileline()->language().systemVerilog()) {
                nodep->v3warn(CONTASSREG,
                              "Continuous assignment to reg, perhaps intended wire"
                                  << " (IEEE 1364-2005 6.1; Verilog only, legal in SV): "
                                  << nodep->prettyNameQ());
            }
            if (m_inFTaskRef && nodep->varp()->varType().isNet()) {
                nodep->v3warn(
                    PROCASSWIRE,
                    "Passed wire on output or inout subroutine argument, expected expression that "
                    "is valid on the left hand side of a procedural assignment"
                        << " (IEEE 1800-2023 13.5): " << nodep->prettyNameQ());
            }
        }

        // If writeSummary is enabled, task/function definitions are treated as non-executed.
        // Remember that anything driven here doesn't count toward MULTIDRIVEN.
        bool ftaskDef = false;
        if (m_taskp && !m_alwaysp && !m_inContAssign && !m_inInitialStatic && !m_inBBox
            && !m_taskp->dpiExport()) {
            AstVar* const retVarp = VN_CAST(m_taskp->fvarp(), Var);
            if (!retVarp || nodep->varp() != retVarp) ftaskDef = true;
        }

        for (int usr = 1; usr < (m_alwaysCombp ? 3 : 2); ++usr) {
            UndrivenVarEntry* const entryp = getEntryp(nodep->varp(), usr);
            const bool fdrv = nodep->access().isWriteOrRW()
                              && nodep->varp()->attrFileDescr();  // FD's are also being read from
            if (m_inBBox || nodep->access().isWriteOrRW()) {
                if (usr == 2 && m_alwaysCombp && entryp->isUsedNotDrivenAny()) {
                    UINFO(9, " Full bus.  Entryp=" << cvtToHex(entryp));
                    warnAlwCombOrder(nodep, entryp->firstUsedNotDrivenp());
                }
                const AstNodeVarRef* const otherVarRefp = entryp->getNodep();
                const AstNode* const otherWritep = otherVarRefp
                                                       ? static_cast<const AstNode*>(otherVarRefp)
                                                       : entryp->callNodep();
                const bool sameFileLine
                    = otherVarRefp && nodep->fileline() == otherVarRefp->fileline();
                if (entryp->isDrivenWhole() && !m_inBBox && !VN_IS(nodep, VarXRef)
                    && !VN_IS(nodep->dtypep()->skipRefp(), UnpackArrayDType) && !sameFileLine
                    && !entryp->isUnderGen() && otherWritep && !entryp->isFtaskDriven()
                    && !ftaskDef && !m_inSelLhs
                    && (!nodep->varp()->fileline()->warnIsOff(V3ErrorCode::MULTIDRIVEN)
                        || !nodep->varp()->fileline()->warnIsOff(V3ErrorCode::MULTIDRIVENPROC))) {
                    const bool otherWriteIsStaticInit
                        = nodep->varp()->hasUserInit() && otherWritep == entryp->initStaticp();

                    if (m_alwaysCombp
                        && (!entryp->isDrivenAlwaysCombWhole()
                            || (m_alwaysCombp != entryp->getAlwCombp()
                                && m_alwaysCombp->fileline()
                                       != entryp->getAlwCombp()->fileline()))) {
                        nodep->v3warn(
                            MULTIDRIVEN,
                            "Variable written to in always_comb also written by other process"
                                << " (IEEE 1800-2023 9.2.2.2): " << nodep->prettyNameQ() << '\n'
                                << nodep->warnOther() << '\n'
                                << nodep->warnContextPrimary() << '\n'
                                << otherWritep->warnOther() << "... Location of other write\n"
                                << otherWritep->warnContextSecondary());
                    }
                    if (!m_alwaysCombp && entryp->isDrivenAlwaysCombWhole()) {
                        nodep->v3warn(MULTIDRIVEN, "Variable also written to in always_comb"
                                                       << " (IEEE 1800-2023 9.2.2.2): "
                                                       << nodep->prettyNameQ() << '\n'
                                                       << nodep->warnOther() << '\n'
                                                       << nodep->warnContextPrimary() << '\n'
                                                       << otherWritep->warnOther()
                                                       << "... Location of always_comb write\n"
                                                       << otherWritep->warnContextSecondary());
                    }
                    if (m_alwaysFFp && !otherWriteIsStaticInit
                        && (!entryp->isDrivenAlwaysFFWhole()
                            || (m_alwaysFFp != entryp->getAlwFFp()
                                && m_alwaysFFp->fileline() != entryp->getAlwFFp()->fileline()))) {
                        nodep->v3warn(
                            MULTIDRIVEN,
                            "Variable written to in always_ff also written by other process"
                                << " (IEEE 1800-2023 9.2.2.4): " << nodep->prettyNameQ() << '\n'
                                << nodep->warnOther() << '\n'
                                << nodep->warnContextPrimary() << '\n'
                                << otherWritep->warnOther() << "... Location of other write\n"
                                << otherWritep->warnContextSecondary());
                    }
                    if (!m_alwaysFFp && !m_inInitialStatic && entryp->isDrivenAlwaysFFWhole()) {
                        nodep->v3warn(MULTIDRIVEN, "Variable also written to in always_ff"
                                                       << " (IEEE 1800-2023 9.2.2.4): "
                                                       << nodep->prettyNameQ() << '\n'
                                                       << nodep->warnOther() << '\n'
                                                       << nodep->warnContextPrimary() << '\n'
                                                       << otherWritep->warnOther()
                                                       << "... Location of always_ff write\n"
                                                       << otherWritep->warnContextSecondary());
                    }
                    // Two plain always blocks driving the whole signal: legal
                    // SystemVerilog, but a driver conflict for synthesis. The
                    // always_ff/always_comb cases above already cover mixes with
                    // an explicit process, so only warn for plain+plain here.
                    // When the two blocks are clocked differently, the
                    // (on-by-default) MULTIDRIVEN check in V3Delayed already reports
                    // the conflict, so don't also emit MULTIDRIVENPROC for that case.
                    const AstAlways* const otherAlwaysp = entryp->getAlwPlainp();
                    const AstSenTree* const senp
                        = m_alwaysPlainp ? m_alwaysPlainp->sentreep() : nullptr;
                    const AstSenTree* const otherSenp
                        = otherAlwaysp ? otherAlwaysp->sentreep() : nullptr;
                    const bool differentClocking = senp && otherSenp && senp->hasClocked()
                                                   && otherSenp->hasClocked()
                                                   && !senp->sameTree(otherSenp);
                    if (m_alwaysPlainp && entryp->isDrivenAlwaysPlainWhole()
                        && m_alwaysPlainp != otherAlwaysp
                        && m_alwaysPlainp->fileline() != otherAlwaysp->fileline()
                        && !differentClocking) {
                        nodep->v3warn(
                            MULTIDRIVENPROC,
                            "Variable written to in always block also written by another always "
                            "block: "
                                << nodep->prettyNameQ() << '\n'
                                << nodep->warnOther() << '\n'
                                << nodep->warnContextPrimary() << '\n'
                                << otherWritep->warnOther() << "... Location of other write\n"
                                << otherWritep->warnContextSecondary());
                    }
                }
                if (!m_inInitialSetup || nodep->varp()->hasUserInit()) {
                    // Else don't count default initialization as a driver to a net/variable
                    entryp->drivenWhole(nodep, ftaskDef);
                }
                if (m_alwaysCombp && entryp->isDrivenAlwaysCombWhole()
                    && m_alwaysCombp != entryp->getAlwCombp()
                    && m_alwaysCombp->fileline() == entryp->getAlwCombp()->fileline())
                    entryp->underGenerate();
                if (m_alwaysCombp) entryp->drivenAlwaysCombWhole(m_alwaysCombp);
                if (m_alwaysFFp) entryp->drivenAlwaysFFWhole(m_alwaysFFp, nodep->varp());
                if (m_alwaysPlainp) entryp->drivenAlwaysPlainWhole(m_alwaysPlainp);
            }
            if (nodep->access().isWriteOrRW() && !VN_IS(nodep, VarXRef)) {
                // Ignoring xrefs as the initial and assignment to track might refer to two
                // different instances.  Ideally all of V3Undriven would move after V3Scope,
                // then could use VarScope tracking instead.
                if (m_inInitialStatic && !entryp->initStaticp()) entryp->initStaticp(nodep);
                if (m_inInitial && !entryp->initialp()) entryp->initialp(nodep);
                if (m_inContAssign && !entryp->contAssignp()) entryp->contAssignp(nodep);
                if (m_alwaysp && m_inProcAssign && !entryp->procWritep())
                    entryp->procWritep(nodep);
            }
            if ((!m_inInitialSetup || nodep->varp()->hasUserInit())
                && (m_inBBox || nodep->access().isReadOrRW()
                    || fdrv
                    // Inouts have only isWrite set, as we don't have more
                    // information and operating on module boundary, treat as
                    // both read and writing
                    || m_inInoutOrRefPin))
                entryp->usedWhole(nodep);
        }
    }

    // Don't know what black boxed calls do, assume in+out
    void visit(AstSysIgnore* nodep) override {
        VL_RESTORER(m_inBBox);
        m_inBBox = true;
        iterateChildrenConst(nodep);
    }

    void visit(AstAssign* nodep) override {
        VL_RESTORER(m_inProcAssign);
        m_inProcAssign = true;
        {
            VL_RESTORER(m_inInitialSetup);
            m_inInitialSetup = false;
            iterateConst(nodep->rhsp());
        }
        iterateConst(nodep->lhsp());
    }
    void visit(AstAssignDly* nodep) override {
        VL_RESTORER(m_inProcAssign);
        m_inProcAssign = true;
        iterateChildrenConst(nodep);
    }
    void visit(AstAssignForce* nodep) override {
        iterateConst(nodep->rhsp());
        VL_RESTORER(m_inInitial);
        m_inInitial = false;
        iterateConst(nodep->lhsp());
    }
    void visit(AstAssignW* nodep) override {
        VL_RESTORER(m_inContAssign);
        m_inContAssign = true;
        iterateChildrenConst(nodep);
    }
    void visit(AstRelease* nodep) override {
        VL_RESTORER(m_inInitial);
        m_inInitial = false;
        iterateConst(nodep->lhsp());
    }
    void visit(AstInitial* nodep) override {
        VL_RESTORER(m_inInitial);
        m_inInitial = true;
        iterateChildrenConst(nodep);
    }
    void visit(AstInitialAutomatic* nodep) override {
        VL_RESTORER(m_inInitialSetup);
        m_inInitialSetup = true;
        iterateChildrenConst(nodep);
    }
    void visit(AstInitialAutomaticStmt* nodep) override {
        VL_RESTORER(m_inInitialSetup);
        m_inInitialSetup = true;
        iterateChildrenConst(nodep);
    }
    void visit(AstInitialStatic* nodep) override {
        VL_RESTORER(m_inInitialStatic);
        m_inInitialStatic = true;
        VL_RESTORER(m_inInitialSetup);
        m_inInitialSetup = true;
        iterateChildrenConst(nodep);
    }
    void visit(AstInitialStaticStmt* nodep) override {
        VL_RESTORER(m_inInitialSetup);
        m_inInitialSetup = true;
        iterateChildrenConst(nodep);
    }
    void visit(AstAlways* nodep) override {
        VL_RESTORER(m_alwaysp);
        VL_RESTORER(m_alwaysCombp);
        VL_RESTORER(m_alwaysFFp);
        VL_RESTORER(m_alwaysPlainp);
        AstNode::user2ClearTree();
        m_alwaysp = nodep;
        if (nodep->keyword() == VAlwaysKwd::ALWAYS_COMB) {
            UINFO(9, "   " << nodep);
            m_alwaysCombp = nodep;
        } else {
            m_alwaysCombp = nullptr;
        }
        m_alwaysFFp = nodep->keyword() == VAlwaysKwd::ALWAYS_FF ? nodep : nullptr;
        m_alwaysPlainp = nodep->keyword() == VAlwaysKwd::ALWAYS ? nodep : nullptr;
        iterateChildrenConst(nodep);
        if (nodep->keyword() == VAlwaysKwd::ALWAYS_COMB) UINFO(9, "   Done " << nodep);
    }

    void visit(AstNodeFTaskRef* nodep) override {
        VL_RESTORER(m_inFTaskRef);
        m_inFTaskRef = true;

        iterateChildrenConst(nodep);

        if (!m_capturep) return;

        // If writeSummary is enabled, task/function definitions are treated as non-executed.
        // Do not apply writeSummary at calls inside a task definition, or they will look like
        // independent drivers (phantom MULTIDRIVEN).
        const bool inExecutedContext
            = !(m_taskp && !m_alwaysp && !m_inContAssign && !m_inInitialStatic && !m_inBBox
                && !m_taskp->dpiExport());

        if (!inExecutedContext) return;

        AstNodeFTask* const calleep = nodep->taskp();
        if (!calleep) return;

        const auto& vars = m_capturep->writeSummary(calleep);
        for (AstVar* const varp : vars) {
            for (int usr = 1; usr < (m_alwaysCombp ? 3 : 2); ++usr) {
                UndrivenVarEntry* const entryp = getEntryp(varp, usr);
                entryp->drivenViaCall(nodep);
                if (m_alwaysCombp) entryp->drivenAlwaysCombWhole(m_alwaysCombp);
                if (m_alwaysFFp) entryp->drivenAlwaysFFWhole(m_alwaysFFp, varp);
            }
        }
    }

    void visit(AstNodeFTask* nodep) override {
        VL_RESTORER(m_taskp);
        m_taskp = nodep;
        iterateChildrenConst(nodep);
    }
    void visit(AstPin* nodep) override {
        VL_RESTORER(m_inInoutOrRefPin);
        m_inInoutOrRefPin = nodep->modVarp()->isInoutOrRef();
        iterateChildrenConst(nodep);
    }

    // Until we support tables, primitives will have undriven and unused I/Os
    void visit(AstPrimitive*) override {}

    // Coverage artifacts etc shouldn't count as a sink
    void visit(AstNodeCoverDecl*) override {}
    void visit(AstCoverInc*) override {}
    void visit(AstCoverToggle*) override {}
    void visit(AstTraceDecl* nodep) override { nodep->v3fatalSrc("Should not exist yet"); }
    void visit(AstTraceInc* nodep) override { nodep->v3fatalSrc("Should not exist yet"); }

    // iterate
    void visit(AstConst* nodep) override {}
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    // CONSTRUCTORS
    explicit UndrivenVisitor(AstNetlist* nodep, V3UndrivenCapture* capturep)
        : m_capturep{capturep} {
        iterateConst(nodep);
    }

    ~UndrivenVisitor() override {
        for (UndrivenVarEntry* ip : m_entryps[1]) ip->reportViolations();
        for (int usr = 1; usr < 3; ++usr) {
            for (UndrivenVarEntry* ip : m_entryps[usr]) delete ip;
        }
    }
};

//######################################################################
// Undriven class functions

void V3Undriven::undrivenAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");

    V3UndrivenCapture capture{nodep};
    { UndrivenVisitor{nodep, &capture}; }

    if (v3Global.opt.stats()) V3Stats::statsStage("undriven");
}
