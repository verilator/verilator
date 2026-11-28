// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit CUDA code for the GPU model
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstMT.h"

#include "V3EmitC.h"
#include "V3EmitCFunc.h"
#include "V3Gpu.h"
#include "V3Stats.h"

#include <map>
#include <set>
#include <unordered_set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

std::string gpuStateName() { return v3Global.opt.prefix() + "__GpuState"; }

std::string gpuMemberRef(const AstVar* varp) {
    return "vlGpuSoa<" + varp->dtypep()->cType("", false, false) + ">(vlSelf, offsetof("
           + gpuStateName() + ", " + V3GpuCapture::memberName(varp) + "))";
}

std::string gpuDeviceArgs(EmitCBaseVisitorConst& emitter, const AstCFunc* funcp) {
    std::string args = emitter.cFuncArgs(funcp);
    if (!funcp->isLoose() || funcp->isStatic()) return args;
    const size_t comma = args.find(", ");
    args = comma == std::string::npos ? "" : args.substr(comma + 2);
    return "VlGpuView vlSelf" + (args.empty() ? "" : ", " + args);
}

std::string gpuDeviceSignature(EmitCBaseVisitorConst& emitter, const AstCFunc* funcp) {
    return "__device__ " + funcp->rtnTypeVoid() + " " + emitter.funcNameProtect(funcp) + "("
           + gpuDeviceArgs(emitter, funcp) + ")";
}

struct GpuTaskGuard final {
    bool m_all = true;  // Task may run whatever the triggers are
    const AstVar* m_varp = nullptr;  // Trigger vector the guard reads
    std::vector<uint64_t> m_words;  // Trigger bits that enable the task, per word
};

bool gpuGuardBits(const AstNode* nodep, GpuTaskGuard& g) {
    if (const AstOr* const orp = VN_CAST(nodep, Or)) {
        return gpuGuardBits(orp->lhsp(), g) && gpuGuardBits(orp->rhsp(), g);
    }
    const AstAnd* const andp = VN_CAST(nodep, And);
    if (!andp) return false;
    const AstConst* constp = VN_CAST(andp->lhsp(), Const);
    const AstArraySel* selp = VN_CAST(andp->rhsp(), ArraySel);
    if (!constp) {
        constp = VN_CAST(andp->rhsp(), Const);
        selp = VN_CAST(andp->lhsp(), ArraySel);
    }
    if (!constp || !selp || constp->width() > 64 || selp->width() > 64) return false;
    const AstVarRef* const refp = VN_CAST(selp->fromp(), VarRef);
    const AstConst* const idxp = VN_CAST(selp->bitp(), Const);
    if (!refp || !idxp) return false;
    if (g.m_varp && g.m_varp != refp->varp()) return false;
    g.m_varp = refp->varp();
    const uint32_t word = idxp->toUInt();
    if (word >= 8) return false;
    if (g.m_words.size() <= word) g.m_words.resize(word + 1, 0);
    g.m_words[word] |= constp->toUQuad();
    return true;
}

bool gpuGuardCond(const AstNode* nodep, GpuTaskGuard& g) {
    if (const AstLogOr* const orp = VN_CAST(nodep, LogOr)) {
        return gpuGuardCond(orp->lhsp(), g) && gpuGuardCond(orp->rhsp(), g);
    }
    if (const AstTriggered* const trigp = VN_CAST(nodep, Triggered)) {
        const AstVar* const varp = trigp->trigRefp()->varp();
        if (g.m_varp && g.m_varp != varp) return false;
        g.m_varp = varp;
        for (const uint32_t index : trigp->indices()) {
            const uint32_t word = VL_BITWORD_Q(index);
            if (word >= 8) return false;
            if (g.m_words.size() <= word) g.m_words.resize(word + 1, 0);
            g.m_words[word] |= VL_BIT_Q(index);
        }
        return true;
    }
    const AstNeq* const neqp = VN_CAST(nodep, Neq);
    if (!neqp) return false;
    const AstConst* zerop = VN_CAST(neqp->rhsp(), Const);
    const AstNode* exprp = neqp->lhsp();
    if (!zerop) {
        zerop = VN_CAST(neqp->lhsp(), Const);
        exprp = neqp->rhsp();
    }
    return zerop && zerop->isZero() && gpuGuardBits(exprp, g);
}

GpuTaskGuard gpuTaskGuard(const AstCFunc* funcp) {
    GpuTaskGuard g;
    for (const AstNode* stmtp = funcp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
        if (VN_IS(stmtp, Comment)) continue;
        if (VN_IS(stmtp, CStmt)) {
            bool known = false;
            if (V3Gpu::deviceCStmtText(stmtp, known).empty() && known) continue;
            return GpuTaskGuard{};
        }
        const AstIf* const ifp = VN_CAST(stmtp, If);
        if (!ifp || ifp->elsesp() || !gpuGuardCond(ifp->condp(), g)) return GpuTaskGuard{};
    }
    g.m_all = false;
    return g;
}

std::string gpuDeferRef() {
    return "vlGpuSoa<VlGpuDeferBuf>(vlSelf, offsetof(" + gpuStateName() + ", __Vgpu_defer))";
}

struct GpuMembers final {
    std::vector<const AstVar*> m_shared;
    std::vector<const AstVar*> m_primary;
    std::vector<const AstVar*> m_nontriv;
    std::vector<const AstVar*> m_device;
    std::vector<const AstVar*> sharedAll() const {
        std::vector<const AstVar*> result{m_shared};
        result.insert(result.end(), m_primary.begin(), m_primary.end());
        result.insert(result.end(), m_nontriv.begin(), m_nontriv.end());
        return result;
    }
};

GpuMembers collectMembers() {
    GpuMembers members;
    std::unordered_set<const AstVar*> seen;
    std::vector<const AstVar*> ordered;
    for (AstCFunc* const funcp : V3Gpu::deviceFuncs()) {
        funcp->foreach([&](const AstVarRef* refp) {
            const AstVar* const varp = refp->varp();
            if (!V3Gpu::isMember(varp)) return;
            if (seen.insert(varp).second) ordered.push_back(varp);
        });
    }
    if (V3Gpu::residentMode()) {
        for (const AstVar* const varp : {static_cast<const AstVar*>(V3Gpu::timingFinishVarp()),
                                         static_cast<const AstVar*>(V3Gpu::timingFatalVarp()),
                                         static_cast<const AstVar*>(V3Gpu::timingOverflowVarp()),
                                         static_cast<const AstVar*>(V3Gpu::resident().m_suspp),
                                         static_cast<const AstVar*>(V3Gpu::timingTbaseVarp())}) {
            if (varp && seen.insert(varp).second) ordered.push_back(varp);
        }
    }
    for (const AstVar* const varp : ordered) {
        const std::string name = EmitCBaseVisitorConst::varName(varp);
        if (name.rfind("__VprimaryPorts.", 0) == 0) {
            members.m_primary.push_back(varp);
        } else if (name.rfind("__Vnontrivs.", 0) == 0) {
            members.m_nontriv.push_back(varp);
        } else if (V3Gpu::isHostMember(varp)) {
            members.m_shared.push_back(varp);
        } else {
            members.m_device.push_back(varp);
        }
    }
    V3Stats::addStat("GPU, shared members", members.sharedAll().size());
    V3Stats::addStat("GPU, device-only members", members.m_device.size());
    return members;
}

class EmitCGpuState final : public EmitCBaseVisitorConst {
    void emitList(const std::vector<const AstVar*>& vars) {
        const size_t lim = std::max<size_t>(v3Global.opt.compLimitMembers(), 1);
        const size_t n = vars.size();
        size_t per = 1;
        int levels = 0;
        while (per * lim < n) {
            per *= lim;
            ++levels;
        }
        emitNested(vars, 0, n, levels, per);
    }
    void emitNested(const std::vector<const AstVar*>& vars, size_t begin, size_t end, int levels,
                    size_t per) {
        if (levels == 0) {
            for (size_t i = begin; i < end; ++i) emitVarDecl(vars[i]);
            return;
        }
        const size_t lim = std::max<size_t>(v3Global.opt.compLimitMembers(), 1);
        for (size_t start = begin; start < end; start += per) {
            puts("struct {\n");
            emitNested(vars, start, std::min(end, start + per), levels - 1, per / lim);
            puts("};\n");
        }
    }

public:
    explicit EmitCGpuState(const GpuMembers& members) {
        openNewOutputHeaderFile(gpuStateName(), "GPU model state");
        const std::string guard = "VERILATED_" + VString::upcase(gpuStateName()) + "_H_";
        puts("#ifndef " + guard + "\n");
        puts("#define " + guard + "\n\n");
        puts("#include \"verilated.h\"\n");
        puts("#include \"verilated_gpu.h\"\n\n");
        puts("struct " + gpuStateName() + " final {\n");
        emitList(members.m_shared);
        if (!members.m_primary.empty()) {
            puts("struct {\n");
            emitList(members.m_primary);
            puts("} __VprimaryPorts;\n");
        }
        if (!members.m_nontriv.empty()) {
            puts("struct {\n");
            emitList(members.m_nontriv);
            puts("} __Vnontrivs;\n");
        }
        puts("VlGpuDeferBuf __Vgpu_defer;\n");
        emitList(members.m_device);
        puts("};\n\n");
        puts("#endif\n");
        closeOutputFile();
    }
    void visit(AstNode*) override {}
};

class EmitCGpuFunc final : public EmitCFunc {
    std::string m_fileBase;  // Base name of the output files
    int m_fileNum = 0;  // Number of the current output file
    std::unordered_set<const AstVar*> m_poolEmitted;

    static std::string gpuPoolName(const AstVar* varp) {
        return "__Vgpu_" + EmitCUtil::constPoolName(varp);
    }

    void emitPoolVars(AstCFunc* funcp) {
        std::vector<const AstVar*> vars;
        funcp->foreach([&](const AstVarRef* refp) {
            const AstVar* const varp = refp->varp();
            if (varp->constPoolEntry() && m_poolEmitted.insert(varp).second) {
                vars.push_back(varp);
            }
        });
        for (const AstVar* const varp : vars) {
            puts("\nstatic __device__ const ");
            puts(varp->dtypep()->cType(gpuPoolName(varp), false, false));
            emitInitializer(VN_AS(varp->valuep(), NodeExpr));
            puts(";\n");
        }
    }

    void emitDpiDeclarations() {
        std::map<std::string, const AstCFunc*> wrappers;
        for (const AstCFunc* const funcp : V3Gpu::deviceFuncs()) {
            funcp->foreach([&](const AstNodeCCall* callp) {
                if (V3Gpu::isGpuDpi(callp->funcp())) {
                    wrappers.emplace(callp->funcp()->name(), callp->funcp());
                }
            });
        }
        for (const auto& it : wrappers) {
            const std::string args = cFuncArgs(it.second);
            puts("__device__ void " + V3Gpu::dpiName(it.second) + "(VlGpuDpiCtx ctx"
                 + (args.empty() ? "" : ", " + args) + ");\n");
        }
        if (!wrappers.empty()) puts("\n");
    }

    static bool isGraphBody(const AstCFunc* funcp) {
        for (const V3GpuGroup& group : V3Gpu::groups()) {
            if (group.m_bodyp == funcp) return !group.m_levels.empty();
        }
        return false;
    }

    void emitDeclarations() {
        emitDpiDeclarations();
        puts("namespace vlgpu_dev {\n");
        for (const AstCFunc* const funcp : V3Gpu::deviceFuncs()) {
            if (isGraphBody(funcp)) continue;
            puts(gpuDeviceSignature(*this, funcp) + ";\n");
        }
        puts("\n");
    }

    void openNextFile() {
        openNewOutputGpuFile(m_fileBase + "__" + std::to_string(m_fileNum++),
                             "GPU device functions");
        puts("\n#include \"" + gpuStateName() + ".h\"\n");
        puts("#include \"verilated_gpu_device.h\"\n\n");
        for (AstCFunc* const funcp : V3Gpu::deviceFuncs()) m_lazyDecls.declared(funcp);
        m_poolEmitted.clear();
        emitDeclarations();
    }

    void emitCapture(AstNode* nodep, int id) {
        const std::vector<AstVar*> vars = V3GpuCapture::vars(nodep);
        std::vector<std::string> refs;
        for (const AstVar* const varp : vars) {
            refs.push_back(!V3Gpu::isMember(varp) ? varp->nameProtect() : gpuMemberRef(varp));
        }
        std::string size = "0";
        for (const std::string& ref : refs) size += " + sizeof(" + ref + ")";
        puts("{\n");
        puts("uint8_t* __Vgpu_p = vlGpuDeferBegin(" + gpuDeferRef() + ", " + std::to_string(id)
             + "U, static_cast<uint32_t>(" + size + "));\n");
        if (!refs.empty()) {
            puts("if (__Vgpu_p) {\n");
            for (const std::string& ref : refs) {
                puts("memcpy(__Vgpu_p, &" + ref + ", sizeof(" + ref + ")); __Vgpu_p += sizeof("
                     + ref + ");\n");
            }
            puts("}\n");
        }
        puts("}\n");
    }
    void deferred(AstNode* nodep) {
        const int id = V3Gpu::replayId(nodep);
        UASSERT_OBJ(id >= 0, nodep, "Deferred GPU statement without replay");
        emitCapture(nodep, id);
    }

public:
    using EmitCFunc::visit;
    void visit(AstVarRef* nodep) override {
        if (nodep->varp()->constPoolEntry()) {
            putns(nodep, gpuPoolName(nodep->varp()));
            return;
        }
        if (V3Gpu::isMember(nodep->varp())) {
            putns(nodep, gpuMemberRef(nodep->varp()));
            return;
        }
        EmitCFunc::visit(nodep);
    }
    std::string memberResetText(const AstVar* varp, const std::string& vlSelf) const override {
        if (V3Gpu::isMember(varp)) return gpuMemberRef(varp);
        return EmitCFunc::memberResetText(varp, vlSelf);
    }
    std::string varRefText(const AstVarRef* refp) const override {
        if (refp->varp()->constPoolEntry()) return gpuPoolName(refp->varp());
        if (V3Gpu::isMember(refp->varp())) return gpuMemberRef(refp->varp());
        return EmitCFunc::varRefText(refp);
    }
    void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_useSelfForThis);
        VL_RESTORER(m_cfuncp);
        emitPoolVars(nodep);
        m_cfuncp = nodep;
        splitSizeInc(nodep);
        puts("\n" + gpuDeviceSignature(*this, nodep) + " {\n");
        m_useSelfForThis = true;
        m_usevlSelfRef = true;
        if (nodep->varsp()) iterateAndNextConstNull(nodep->varsp());
        if (nodep->stmtsp()) iterateAndNextConstNull(nodep->stmtsp());
        m_usevlSelfRef = false;
        puts("}\n");
    }
    void visit(AstCCall* nodep) override {
        if (!V3Gpu::isGpuDpi(nodep->funcp())) {
            EmitCFunc::visit(nodep);
            return;
        }
        putns(nodep, V3Gpu::dpiName(nodep->funcp()) + "(VlGpuDpiCtx{vlSelf.m_i, vlSelf.m_n, &"
                         + gpuDeferRef() + "}");
        putCommaIterateNext(nodep->argsp(), true);
        puts(")");
    }
    std::string localNow() const {
        return "(vlGpuNow - " + gpuMemberRef(V3Gpu::timingTbaseVarp()) + ")";
    }
    std::string finishRef() const {
        return "(" + gpuMemberRef(V3Gpu::timingFinishVarp()) + " != 0U)";
    }
    std::string mapPlaceholders(std::string text) const {
        const std::string finish = "@@VLGPU_FINISH@@";
        for (size_t pos = text.find(finish); pos != std::string::npos; pos = text.find(finish)) {
            text.replace(pos, finish.size(), finishRef());
        }
        const std::string now = "@@VLGPU_NOW@@";
        for (size_t pos = text.find(now); pos != std::string::npos; pos = text.find(now)) {
            text.replace(pos, now.size(), localNow());
        }
        const std::string fatal = "@@VLGPU_FATAL@@";
        for (size_t pos = text.find(fatal); pos != std::string::npos; pos = text.find(fatal)) {
            const size_t numPos = pos + fatal.size();
            const size_t end = text.find("@@", numPos);
            const std::string code = text.substr(numPos, end - numPos);
            text.replace(pos, end + 2 - pos,
                         gpuMemberRef(V3Gpu::timingFatalVarp()) + " = " + code + "U; "
                             + gpuMemberRef(V3Gpu::timingFinishVarp()) + " = 1U;");
        }
        return text;
    }
    void emitSeqGraphs(const V3GpuResident& r) {
        constexpr size_t HEAVY = 32;
        constexpr size_t MAX_LIGHT = 160;
        std::string okText;
        std::string runText;
        for (size_t g = 0; g < r.m_graphs.size() && g < 15; ++g) {
            const std::vector<AstCFunc*>& order = r.m_graphs[g].m_order;
            std::vector<GpuTaskGuard> guards;
            const AstVar* varp = nullptr;
            for (const AstCFunc* const funcp : order) {
                GpuTaskGuard guard = gpuTaskGuard(funcp);
                if (!guard.m_all && guard.m_varp) {
                    if (!varp) varp = guard.m_varp;
                    if (varp != guard.m_varp) guard = GpuTaskGuard{};
                }
                guards.push_back(guard);
            }
            if (!varp || !V3Gpu::isMember(varp)) continue;
            size_t words = 0;
            for (const GpuTaskGuard& guard : guards) words = std::max(words, guard.m_words.size());
            std::vector<size_t> counts(words * 64, 0);
            for (const GpuTaskGuard& guard : guards) {
                if (guard.m_all) continue;
                for (size_t w = 0; w < guard.m_words.size(); ++w) {
                    for (int b = 0; b < 64; ++b) {
                        if ((guard.m_words[w] >> b) & 1ULL) ++counts[w * 64 + b];
                    }
                }
            }
            std::vector<uint64_t> heavy(words, 0);
            for (size_t w = 0; w < words; ++w) {
                for (int b = 0; b < 64; ++b) {
                    if (counts[w * 64 + b] > HEAVY) heavy[w] |= 1ULL << b;
                }
            }
            std::vector<size_t> light;
            bool overlaps = false;
            for (size_t t = 0; t < guards.size(); ++t) {
                const GpuTaskGuard& guard = guards[t];
                if (guard.m_all) {
                    light.push_back(t);
                    continue;
                }
                bool rare = false;
                bool hits = false;
                for (size_t w = 0; w < guard.m_words.size(); ++w) {
                    rare = rare || (guard.m_words[w] & ~heavy[w]);
                    hits = hits || (guard.m_words[w] & heavy[w]);
                }
                if (rare) light.push_back(t);
                overlaps = overlaps || hits;
            }
            if (!overlaps || light.size() > MAX_LIGHT) continue;
            const std::string trig = "vlGpuSoa<" + varp->dtypep()->cType("", false, false)
                                     + ">(v, offsetof(" + gpuStateName() + ", "
                                     + V3GpuCapture::memberName(varp) + "))";
            std::string test;
            for (size_t w = 0; w < words; ++w) {
                if (!heavy[w]) continue;
                if (!test.empty()) test += " | ";
                test += "(" + trig + "[" + std::to_string(w) + "U] & 0x" + cvtToHex(heavy[w])
                        + "ULL)";
            }
            okText += "case " + std::to_string(g) + ": return (" + test + ") == 0ULL;\n";
            runText += "case " + std::to_string(g) + ": {\n";
            for (size_t w = 0; w < words; ++w) {
                runText += "const uint64_t t" + std::to_string(w) + " = " + trig + "["
                           + std::to_string(w) + "U];\n";
            }
            for (const size_t t : light) {
                const GpuTaskGuard& guard = guards[t];
                std::string cond;
                for (size_t w = 0; w < guard.m_words.size() && !guard.m_all; ++w) {
                    if (!guard.m_words[w]) continue;
                    if (!cond.empty()) cond += " | ";
                    cond += "(t" + std::to_string(w) + " & 0x" + cvtToHex(guard.m_words[w])
                            + "ULL)";
                }
                const std::string call = funcNameProtect(order[t]) + "(v);\n";
                runText += cond.empty() ? call : "if ((" + cond + ") != 0ULL) " + call;
            }
            runText += "return;\n}\n";
        }
        puts("static __device__ bool seqOk(int graph, const VlGpuView& v) {\nswitch (graph) {\n"
             + okText + "default: return false;\n}\n}\n");
        puts("static __device__ void runSeq(int graph, const VlGpuView& v) {\nswitch (graph) {\n"
             + runText + "default: return;\n}\n}\n");
    }
    void emitNodes(AstNode* nodesp) {
        for (AstNode* itemp = nodesp; itemp; itemp = itemp->nextp()) {
            if (const AstText* const textp = VN_CAST(itemp, Text)) {
                puts(textp->text());
            } else {
                iterateConst(itemp);
            }
        }
    }
    void visit(AstCExpr* nodep) override {
        if (V3Gpu::residentMode() && V3Gpu::isTimingDeviceStmt(nodep)) {
            putnbs(nodep, "");
            emitNodes(nodep->nodesp());
            return;
        }
        const std::string text = V3Gpu::residentMode() ? V3Gpu::deviceCExprText(nodep)
                                                       : V3Gpu::gpuAssertCtlText(nodep);
        if (text.empty()) {
            EmitCFunc::visit(nodep);
            return;
        }
        putnbs(nodep, "");
        puts(mapPlaceholders(text));
    }
    void visit(AstTime* nodep) override {
        if (!V3Gpu::residentMode()) {
            EmitCFunc::visit(nodep);
            return;
        }
        const double scale
            = nodep->timeunit().multiplier() / v3Global.rootp()->timeprecision().multiplier();
        putns(nodep, "(" + localNow() + " / static_cast<uint64_t>(" + cvtToStr(scale) + "))");
    }
    void visit(AstTimeD* nodep) override {
        if (!V3Gpu::residentMode()) {
            EmitCFunc::visit(nodep);
            return;
        }
        const double scale
            = nodep->timeunit().multiplier() / v3Global.rootp()->timeprecision().multiplier();
        putns(nodep, "(static_cast<double>(" + localNow() + ") / " + cvtToStr(scale) + ")");
    }
    void visit(AstExecGraph*) override {}
    void visit(AstCStmt* nodep) override {
        if (V3Gpu::isGpuNoopStmt(nodep)) return;
        if (V3Gpu::residentMode()) {
            int graph = 0;
            int label = 0;
            if (V3Gpu::isResidentGraphPoint(nodep, graph, label)) {
                const std::string ret = m_cfuncp->rtnTypeVoid() == "void" ? "" : " 0";
                puts("{\n" + gpuMemberRef(V3Gpu::resident().m_suspp) + " = "
                     + std::to_string(graph + 1) + "U;\n"
                     + gpuMemberRef(V3Gpu::residentGraphPc(nodep)) + " = " + std::to_string(label)
                     + "U;\nreturn" + ret + ";\n}\ncase " + std::to_string(label) + ":;\n");
                return;
            }
            if (V3Gpu::isTimingDeviceStmt(nodep) || V3Gpu::isResidentStmt(nodep)) {
                emitNodes(nodep->nodesp());
                puts("\n");
                return;
            }
            bool known = false;
            const std::string text = V3Gpu::deviceCStmtText(nodep, known);
            if (known) {
                puts(mapPlaceholders(text) + "\n");
                return;
            }
        }
        EmitCFunc::visit(nodep);
    }
    void finishNow() {
        if (V3Gpu::residentMode()) puts(gpuMemberRef(V3Gpu::timingFinishVarp()) + " = 1U;\n");
    }
    void visit(AstDisplay* nodep) override { deferred(nodep); }
    void visit(AstStop* nodep) override {
        deferred(nodep);
        finishNow();
    }
    void visit(AstFinish* nodep) override {
        deferred(nodep);
        finishNow();
    }

    explicit EmitCGpuFunc(AstNodeModule* modp) {
        m_modp = modp;
        m_fileBase = v3Global.opt.prefix() + "__Gpu";
        openNextFile();
        for (AstCFunc* const funcp : V3Gpu::deviceFuncs()) {
            if (isGraphBody(funcp)) continue;
            if (splitNeeded()) {
                puts("}\n");
                closeOutputFile();
                openNextFile();
            }
            iterateConst(funcp);
        }
        puts("}\n");
        closeOutputFile();
        emitKernels();
        if (V3Gpu::residentMode()) emitResident();
    }

    std::string regionCall(const AstCFunc* funcp, const std::string& extra = "") {
        if (!funcp) return "return false;";
        return "return " + funcNameProtect(funcp) + "(v" + extra + ");";
    }

    void emitResident() {
        const std::string prefix = v3Global.opt.prefix();
        const V3GpuResident& r = V3Gpu::resident();
        openNewOutputGpuFile(m_fileBase + "__resident", "GPU resident driver");
        puts("\n#include \"" + gpuStateName() + ".h\"\n");
        puts("#include \"verilated_gpu_resident.h\"\n\n");
        puts("#include <cstdlib>\n\n");
        emitDeclarations();
        puts("struct GpuModel final {\n");
        puts("static constexpr int GRAPHS = " + std::to_string(r.m_graphs.size()) + ";\n");
        puts("static constexpr size_t STRIDE = sizeof(" + gpuStateName() + ");\n");
        const auto trivial = [](const AstCFunc* funcp) {
            if (!funcp) return true;
            const AstCReturn* const returnp = VN_CAST(funcp->stmtsp(), CReturn);
            if (!returnp || returnp->nextp()) return false;
            const AstConst* const constp = VN_CAST(returnp->lhsp(), Const);
            return constp && constp->isZero();
        };
        puts("static constexpr __host__ __device__ bool trivialLoop(int loop) {\nreturn ");
        const AstCFunc* const loops[]
            = {r.m_icop, r.m_actp, r.m_inactp, r.m_nbap, r.m_obsp, r.m_reactp};
        std::string expr = "false";
        for (int l = 1; l < 6; ++l) {
            if (trivial(loops[l])) expr += " || loop == " + std::to_string(l);
        }
        puts(expr + ";\n}\n");
        puts("static __device__ bool evalIco(const VlGpuView& v, bool first) { "
             + regionCall(r.m_icop, ", first") + " }\n");
        puts("static __device__ bool evalAct(const VlGpuView& v) { " + regionCall(r.m_actp)
             + " }\n");
        puts("static __device__ bool evalInact(const VlGpuView& v) { " + regionCall(r.m_inactp)
             + " }\n");
        puts("static __device__ bool evalNba(const VlGpuView& v) { " + regionCall(r.m_nbap)
             + " }\n");
        puts("static __device__ bool evalObs(const VlGpuView& v) { " + regionCall(r.m_obsp)
             + " }\n");
        puts("static __device__ bool evalReact(const VlGpuView& v) { " + regionCall(r.m_reactp)
             + " }\n");
        puts("static __device__ void evalSample(const VlGpuView& v) { "
             + (r.m_samplep ? funcNameProtect(r.m_samplep) + "(v);" : std::string{}) + " }\n");
        puts("static __device__ void evalPostponed(const VlGpuView& v) { "
             + (r.m_postponedp ? funcNameProtect(r.m_postponedp) + "(v);" : std::string{})
             + " }\n");
        puts("static __device__ uint64_t nextTime(const VlGpuView& v) { return "
             + funcNameProtect(V3Gpu::timingNextTimeFuncp()) + "(v); }\n");
        const auto member = [](const AstVar* varp) {
            return "vlGpuSoa<uint32_t>(v, offsetof(" + gpuStateName() + ", "
                   + V3GpuCapture::memberName(varp) + "))";
        };
        puts("static __device__ bool finished(const VlGpuView& v) { return "
             + member(V3Gpu::timingFinishVarp()) + " != 0U; }\n");
        puts("static __device__ bool forkOverflow(const VlGpuView& v) { return "
             + member(V3Gpu::timingOverflowVarp()) + " != 0U; }\n");
        puts("static __device__ uint64_t timeBase(const VlGpuView& v) { return "
             "vlGpuSoa<uint64_t>(v, offsetof("
             + gpuStateName() + ", " + V3GpuCapture::memberName(V3Gpu::timingTbaseVarp())
             + ")); }\n");
        puts("static __device__ uint32_t takeSuspend(const VlGpuView& v) {\n");
        puts("uint32_t& s = " + member(r.m_suspp) + ";\n");
        puts("const uint32_t result = s;\ns = 0U;\nreturn result;\n}\n");
        puts("static __device__ int graphLevels(int graph) {\nswitch (graph) {\n");
        size_t maxLevel = 1;
        for (size_t g = 0; g < r.m_graphs.size(); ++g) {
            puts("case " + std::to_string(g) + ": return "
                 + std::to_string(r.m_graphs[g].m_levels.size()) + ";\n");
        }
        puts("default: return 0;\n}\n}\n");
        puts("static __device__ int levelSize(int graph, int level) {\nswitch (graph) {\n");
        for (size_t g = 0; g < r.m_graphs.size(); ++g) {
            puts("case " + std::to_string(g) + ": {\nswitch (level) {\n");
            for (size_t l = 0; l < r.m_graphs[g].m_levels.size(); ++l) {
                const size_t size = r.m_graphs[g].m_levels[l].size();
                maxLevel = std::max(maxLevel, size);
                puts("case " + std::to_string(l) + ": return " + std::to_string(size) + ";\n");
            }
            puts("default: return 0;\n}\n}\n");
        }
        puts("default: return 0;\n}\n}\n");
        puts("static __device__ void runTask(int graph, int level, int task, const VlGpuView& v) "
             "{\nswitch (graph) {\n");
        for (size_t g = 0; g < r.m_graphs.size(); ++g) {
            puts("case " + std::to_string(g) + ": {\nswitch (level) {\n");
            for (size_t l = 0; l < r.m_graphs[g].m_levels.size(); ++l) {
                puts("case " + std::to_string(l) + ": {\nswitch (task) {\n");
                const std::vector<AstCFunc*>& tasks = r.m_graphs[g].m_levels[l];
                for (size_t t = 0; t < tasks.size(); ++t) {
                    puts("case " + std::to_string(t) + ": " + funcNameProtect(tasks[t])
                         + "(v); return;\n");
                }
                puts("default: return;\n}\n}\n");
            }
            puts("default: return;\n}\n}\n");
        }
        puts("default: return;\n}\n}\n");
        size_t totalTasks = 0;
        std::vector<size_t> bases;
        for (size_t g = 0; g < r.m_graphs.size(); ++g) {
            bases.push_back(totalTasks);
            totalTasks += r.m_graphs[g].m_order.size();
        }
        puts("static constexpr int TOTAL_TASKS = " + std::to_string(totalTasks) + ";\n");
        puts("static __device__ int graphTasks(int graph) {\nswitch (graph) {\n");
        for (size_t g = 0; g < r.m_graphs.size(); ++g) {
            puts("case " + std::to_string(g) + ": return "
                 + std::to_string(r.m_graphs[g].m_order.size()) + ";\n");
        }
        puts("default: return 0;\n}\n}\n");
        puts("static __device__ int taskBase(int graph) {\nswitch (graph) {\n");
        for (size_t g = 0; g < r.m_graphs.size(); ++g) {
            puts("case " + std::to_string(g) + ": return " + std::to_string(bases[g]) + ";\n");
        }
        puts("default: return 0;\n}\n}\n");
        puts("static __device__ void preds(int graph, int task, const uint32_t*& beginp, "
             "const uint32_t*& endp);\n");
        puts("static __device__ void runFlat(int graph, int task, const VlGpuView& v) "
             "{\nswitch (graph) {\n");
        for (size_t g = 0; g < r.m_graphs.size(); ++g) {
            puts("case " + std::to_string(g) + ": {\nswitch (task) {\n");
            const std::vector<AstCFunc*>& order = r.m_graphs[g].m_order;
            for (size_t t = 0; t < order.size(); ++t) {
                puts("case " + std::to_string(t) + ": " + funcNameProtect(order[t])
                     + "(v); return;\n");
            }
            puts("default: return;\n}\n}\n");
        }
        puts("default: return;\n}\n}\n");
        emitSeqGraphs(r);
        puts("};\n");
        for (size_t g = 0; g < r.m_graphs.size(); ++g) {
            const V3GpuResidentGraph& graph = r.m_graphs[g];
            std::string starts;
            std::string list;
            size_t count = 0;
            for (size_t t = 0; t < graph.m_order.size(); ++t) {
                starts += std::to_string(count) + ",";
                for (const int pred : graph.m_preds[t]) {
                    list += std::to_string(pred) + ",";
                    ++count;
                }
            }
            starts += std::to_string(count);
            if (list.empty()) list = "0";
            puts("static __device__ const uint32_t s_predStart" + std::to_string(g) + "[] = {"
                 + starts + "};\n");
            puts("static __device__ const uint32_t s_preds" + std::to_string(g) + "[] = {" + list
                 + "};\n");
        }
        puts("__device__ void GpuModel::preds(int graph, int task, const uint32_t*& beginp, "
             "const uint32_t*& endp) {\nswitch (graph) {\n");
        for (size_t g = 0; g < r.m_graphs.size(); ++g) {
            const std::string gs = std::to_string(g);
            puts("case " + gs + ": beginp = s_preds" + gs + " + s_predStart" + gs
                 + "[task]; endp = s_preds" + gs + " + s_predStart" + gs
                 + "[task + 1]; return;\n");
        }
        puts("default: beginp = endp = nullptr; return;\n}\n}\n");
        puts("}\n");
        puts("using namespace vlgpu_dev;\n\n");
        puts("extern \"C\" size_t " + prefix + "__gpuResidentStack() {\n");
        puts("cudaFuncAttributes attr{};\n");
        puts("if (cudaFuncGetAttributes(&attr, vlGpuResidentKernel<GpuModel>) != cudaSuccess) "
             "return ~static_cast<size_t>(0);\n");
        puts("return attr.localSizeBytes;\n}\n");
        puts("extern \"C\" int " + prefix
             + "__gpuResidentLaunch(void* basep, int n, const void* activep, void* ctlp) {\n");
        puts("static int s_blocks = 0;\n");
        puts("constexpr int threads = 128;\n");
        puts("if (!s_blocks) {\n");
        puts("int perSm = 0;\nint sms = 0;\n");
        puts("if (cudaOccupancyMaxActiveBlocksPerMultiprocessor(&perSm, "
             "vlGpuResidentKernel<GpuModel>, threads, 0) != cudaSuccess) return -1;\n");
        puts("if (cudaDeviceGetAttribute(&sms, cudaDevAttrMultiProcessorCount, 0) != "
             "cudaSuccess) return -1;\n");
        puts("const long items = static_cast<long>(" + std::to_string(maxLevel)
             + ") * ((n + 31) / 32) * 32;\n");
        puts("const long want = (items + threads - 1) / threads;\n");
        puts("const long limit = static_cast<long>(perSm) * sms;\n");
        puts("s_blocks = static_cast<int>(want < limit ? want : limit);\n");
        puts("if (const char* const envp = std::getenv(\"VERILATOR_GPU_BLOCKS\")) {\n");
        puts("const long forced = std::atol(envp);\n");
        puts("if (forced > 0) s_blocks = static_cast<int>(forced < limit ? forced : limit);\n");
        puts("}\n");
        puts("if (s_blocks < 1) s_blocks = 1;\n");
        puts("}\n");
        puts("static uint32_t* s_flowp = nullptr;\n");
        puts("if (!s_flowp) {\n");
        puts("const size_t bytes = sizeof(uint32_t) * (static_cast<size_t>(GpuModel::TOTAL_TASKS) "
             "+ 1) * ((n + 31) / 32);\n");
        puts("if (cudaMalloc(reinterpret_cast<void**>(&s_flowp), bytes) != cudaSuccess) return "
             "-1;\n");
        puts("if (cudaMemset(s_flowp, 0, bytes) != cudaSuccess) return -1;\n");
        puts("if (cudaMemcpyToSymbol(vlGpuFlowFlags, &s_flowp, sizeof(s_flowp)) != cudaSuccess) "
             "return -1;\n");
        puts("}\n");
        puts("uint8_t* basePtr = static_cast<uint8_t*>(basep);\n");
        puts("const uint8_t* activePtr = static_cast<const uint8_t*>(activep);\n");
        puts("VlGpuResidentCtl* ctlPtr = static_cast<VlGpuResidentCtl*>(ctlp);\n");
        puts("void* args[] = {&basePtr, &n, &activePtr, &ctlPtr};\n");
        puts("return cudaLaunchCooperativeKernel(reinterpret_cast<void*>("
             "vlGpuResidentKernel<GpuModel>), s_blocks, threads, args, 0, nullptr) "
             "== cudaSuccess ? 0 : -1;\n");
        puts("}\n");
        closeOutputFile();
    }

    void emitKernels() {
        openNewOutputGpuFile(m_fileBase + "__kernels", "GPU kernels");
        puts("\n#include \"" + gpuStateName() + ".h\"\n");
        puts("#include \"verilated_gpu_device.h\"\n\n");
        emitDeclarations();
        for (const V3GpuGroup& group : V3Gpu::groups()) {
            if (!group.m_levels.empty()) {
                for (size_t level = 0; level < group.m_levels.size(); ++level) {
                    if (group.m_levels[level].empty()) continue;
                    puts("__global__ void " + v3Global.opt.prefix() + "__gpuKernel_"
                         + std::to_string(group.m_id) + "_" + std::to_string(level)
                         + "(uint8_t* basep, int n, const uint8_t* activep) {\n");
                    puts("const int i = blockIdx.x * blockDim.x + threadIdx.x;\n");
                    puts("if (i >= n || !activep[i]) return;\n");
                    puts("const VlGpuView view{basep, static_cast<uint32_t>(n), "
                         "static_cast<uint32_t>(i)};\n");
                    puts("switch (blockIdx.y) {\n");
                    const std::vector<AstCFunc*>& tasks = group.m_levels[level];
                    for (size_t t = 0; t < tasks.size(); ++t) {
                        puts("case " + std::to_string(t) + ": " + funcNameProtect(tasks[t])
                             + "(view); break;\n");
                    }
                    puts("default: break;\n");
                    puts("}\n");
                    puts("}\n");
                }
                continue;
            }
            puts("__global__ void " + v3Global.opt.prefix() + "__gpuKernel_"
                 + std::to_string(group.m_id)
                 + "(uint8_t* basep, int n, const uint8_t* activep) {\n");
            puts("const int i = blockIdx.x * blockDim.x + threadIdx.x;\n");
            puts("if (i < n && activep[i]) " + funcNameProtect(group.m_bodyp)
                 + "(VlGpuView{basep, static_cast<uint32_t>(n), static_cast<uint32_t>(i)});\n");
            puts("}\n");
        }
        puts("}\n");
        puts("using namespace vlgpu_dev;\n");
        puts("\nvoid " + v3Global.opt.prefix()
             + "__gpuLaunch(int groupId, void* statesp, int n, int levelBegin, int levelEnd, "
               "const uint8_t* activep) {\n");
        if (V3Gpu::groups().empty()) {
            puts("(void)groupId;\n(void)statesp;\n(void)n;\n(void)levelBegin;\n(void)levelEnd;\n"
                 "(void)activep;\n}\n");
            closeOutputFile();
            return;
        }
        puts("uint8_t* const sp = static_cast<uint8_t*>(statesp);\n");
        puts("const int threads = 64;\n");
        puts("const int blocks = (n + threads - 1) / threads;\n");
        puts("switch (groupId) {\n");
        for (const V3GpuGroup& group : V3Gpu::groups()) {
            if (!group.m_levels.empty()) {
                puts("case " + std::to_string(group.m_id) + ":\n");
                for (size_t level = 0; level < group.m_levels.size(); ++level) {
                    if (group.m_levels[level].empty()) continue;
                    puts("if (levelBegin <= " + std::to_string(level) + " && "
                         + std::to_string(level) + " < levelEnd) " + v3Global.opt.prefix()
                         + "__gpuKernel_" + std::to_string(group.m_id) + "_"
                         + std::to_string(level) + "<<<dim3(blocks, "
                         + std::to_string(group.m_levels[level].size())
                         + "), threads>>>(sp, n, activep);\n");
                }
                puts("break;\n");
                continue;
            }
            puts("case " + std::to_string(group.m_id) + ": " + v3Global.opt.prefix()
                 + "__gpuKernel_" + std::to_string(group.m_id)
                 + "<<<blocks, threads>>>(sp, n, activep); break;\n");
        }
        puts("default: break;\n");
        puts("}\n");
        puts("}\n");
        closeOutputFile();
    }
};

class EmitCGpuHost final : public EmitCBaseVisitorConst {
    void emitTable(const std::string& name, const std::vector<const AstVar*>& vars,
                   const std::string& rootName) {
        puts("\nstatic const VlGpuCopy " + name + "[] = {\n");
        for (const AstVar* const varp : vars) {
            const std::string member = V3GpuCapture::memberName(varp);
            puts("{offsetof(" + rootName + ", " + member + "), offsetof(" + gpuStateName() + ", "
                 + member + "), sizeof(static_cast<" + gpuStateName() + "*>(nullptr)->" + member
                 + ")},\n");
        }
        puts("{0, 0, 0}};\n");
        puts("\nstatic const char* const " + name + "Names[] = {\n");
        for (const AstVar* const varp : vars) puts("\"" + varp->prettyName() + "\",\n");
        puts("nullptr};\n");
    }

public:
    explicit EmitCGpuHost(const GpuMembers& members) {
        const std::string prefix = v3Global.opt.prefix();
        const std::string rootName = EmitCUtil::prefixNameProtect(V3Gpu::modulep());
        const std::string state = gpuStateName();
        openNewOutputSourceFile(prefix + "__GpuHost", false, false, "GPU host control");
        puts("\n#include \"" + EmitCUtil::pchClassName() + ".h\"\n");
        puts("#include \"" + state + ".h\"\n");
        puts("#include \"verilated_gpu.h\"\n\n");
        puts("#include <cstddef>\n");
        puts("#include <cstring>\n\n");
        puts("#pragma GCC diagnostic ignored \"-Winvalid-offsetof\"\n");
        for (const V3GpuReplay& replay : V3Gpu::replays()) {
            puts("void " + funcNameProtect(replay.m_funcp) + "(" + rootName + "* vlSelf);\n");
        }
        puts("void " + prefix
             + "__gpuLaunch(int groupId, void* statesp, int n, int levelBegin, int levelEnd, "
               "const uint8_t* activep);\n");
        emitTable("s_gpuShared", members.sharedAll(), rootName);
        emitTable("s_gpuDevice", members.m_device, rootName);
        puts("\nstatic void gpuReplay(int id, void* userp) {\n");
        puts(rootName + "* const vlSelf = static_cast<" + rootName + "*>(userp);\n");
        puts("switch (id) {\n");
        for (const V3GpuReplay& replay : V3Gpu::replays()) {
            puts("case " + std::to_string(replay.m_id) + ": " + funcNameProtect(replay.m_funcp)
                 + "(vlSelf); break;\n");
        }
        puts("default: break;\n");
        puts("}\n");
        puts("}\n");
        puts("\nvoid " + prefix
             + "__gpuRun(void* selfp, int groupId, int levelBegin, int levelEnd) {\n");
        puts(rootName + "* const vlSelf = static_cast<" + rootName + "*>(selfp);\n");
        puts("constexpr size_t stride = sizeof(" + state + ");\n");
        puts("constexpr size_t deferOffset = offsetof(" + state + ", __Vgpu_defer);\n");
        puts("static const int n = VerilatedGpu::batch();\n");
        puts("static " + state + "* const hostStatep = new " + state + "{};\n");
        puts("static uint8_t* const devStatep = static_cast<uint8_t*>("
             "VerilatedGpu::deviceAlloc(VerilatedGpu::stateBytes(stride, n)));\n");
        puts("static bool s_uploaded = false;\n");
        puts("VerilatedGpu::copyIn(s_gpuShared, vlSelf, hostStatep);\n");
        puts("if (!s_uploaded) {\n");
        puts("VerilatedGpu::copyIn(s_gpuDevice, vlSelf, hostStatep);\n");
        puts("VerilatedGpu::dpiCopyInit(n);\n");
        puts("VerilatedGpu::soaUploadAll(devStatep, n, -1, hostStatep, stride, s_gpuShared, "
             "s_gpuDevice);\n");
        puts("s_uploaded = true;\n");
        puts("} else {\n");
        puts("VerilatedGpu::soaPreLaunch(devStatep, n, deferOffset, hostStatep, s_gpuShared);\n");
        puts("}\n");
        puts("VerilatedGpu::assertCtlSync();\n");
        puts(prefix
             + "__gpuLaunch(groupId, devStatep, n, levelBegin, levelEnd, "
               "VerilatedGpu::activeDevice(n));\n");
        puts("VerilatedGpu::synchronize(\"kernel\");\n");
        puts("const bool pending = VerilatedGpu::soaPostLaunch(devStatep, n, deferOffset, "
             "hostStatep, s_gpuShared);\n");
        puts("VerilatedGpu::copyOut(s_gpuShared, hostStatep, vlSelf);\n");
        puts("if (pending) VerilatedGpu::soaReplayPending(devStatep, deferOffset, n, "
             "&gpuReplay, vlSelf);\n");
        puts("}\n");
        if (V3Gpu::residentMode()) {
            puts("\nextern \"C\" int " + prefix
                 + "__gpuResidentLaunch(void* basep, int n, const void* activep, void* ctlp);\n");
            puts("extern \"C\" size_t " + prefix + "__gpuResidentStack();\n");
            puts("\nvoid " + prefix + "__gpuDumpHost(void* selfp, const char* pathp) {\n");
            puts(rootName + "* const vlSelf = static_cast<" + rootName + "*>(selfp);\n");
            puts(state + "* const statep = new " + state + "{};\n");
            puts("VerilatedGpu::copyIn(s_gpuShared, vlSelf, statep);\n");
            puts("VerilatedGpu::copyIn(s_gpuDevice, vlSelf, statep);\n");
            puts("VerilatedGpu::dumpState(pathp, statep, sizeof(" + state
                 + "), s_gpuShared, "
                   "s_gpuSharedNames, s_gpuDevice, s_gpuDeviceNames);\n");
            puts("delete statep;\n");
            puts("}\n");
            puts("\nstatic const char* const s_gpuFatalMsgs[] = {\n");
            for (const std::string& msg : V3Gpu::fatalMessages()) {
                puts("\"" + V3OutFormatter::quoteNameControls(msg) + "\",\n");
            }
            puts("nullptr};\n");
            puts("\nvoid " + prefix + "__gpuResidentRun(void* selfp) {\n");
            puts(rootName + "* const vlSelf = static_cast<" + rootName + "*>(selfp);\n");
            puts("constexpr size_t stride = sizeof(" + state + ");\n");
            puts("constexpr size_t deferOffset = offsetof(" + state + ", __Vgpu_defer);\n");
            puts("const int n = VerilatedGpu::residentSlots(stride, " + prefix
                 + "__gpuResidentStack());\n");
            puts(state + "* const hostStatep = new " + state + "{};\n");
            puts("uint8_t* const devStatep = static_cast<uint8_t*>("
                 "VerilatedGpu::deviceAlloc(VerilatedGpu::stateBytes(stride, n)));\n");
            puts("VerilatedGpu::copyIn(s_gpuShared, vlSelf, hostStatep);\n");
            puts("VerilatedGpu::copyIn(s_gpuDevice, vlSelf, hostStatep);\n");
            puts("VerilatedGpu::soaUploadAll(devStatep, n, -1, hostStatep, stride, s_gpuShared, "
                 "s_gpuDevice);\n");
            puts("VerilatedGpu::soaDeferReset(devStatep, deferOffset, n);\n");
            puts("VerilatedGpu::assertCtlSync();\n");
            puts("VlGpuResidentModel model{};\n");
            puts("model.m_stride = stride;\n");
            puts("model.m_deferOffset = deferOffset;\n");
            puts("model.m_finishOffset = offsetof(" + state + ", "
                 + V3GpuCapture::memberName(V3Gpu::timingFinishVarp()) + ");\n");
            puts("model.m_fatalOffset = offsetof(" + state + ", "
                 + V3GpuCapture::memberName(V3Gpu::timingFatalVarp()) + ");\n");
            puts("model.m_fatalMsgsp = s_gpuFatalMsgs;\n");
            puts("model.m_fatalCount = " + std::to_string(V3Gpu::fatalMessages().size()) + "U;\n");
            puts("model.m_tbaseOffset = offsetof(" + state + ", "
                 + V3GpuCapture::memberName(V3Gpu::timingTbaseVarp()) + ");\n");
            puts("model.m_sharedp = s_gpuShared;\n");
            puts("model.m_devicep = s_gpuDevice;\n");
            puts("model.m_snapshotp = hostStatep;\n");
            puts("model.m_convergeLimit = " + std::to_string(v3Global.opt.convergeLimit())
                 + "U;\n");
            puts("model.m_launch = &" + prefix + "__gpuResidentLaunch;\n");
            puts("model.m_replay = &gpuReplay;\n");
            puts("model.m_userp = vlSelf;\n");
            puts("model.m_sharedNamesp = s_gpuSharedNames;\n");
            puts("model.m_deviceNamesp = s_gpuDeviceNames;\n");
            puts("VerilatedGpu::residentRun(devStatep, n, model);\n");
            puts("}\n");
        }
        closeOutputFile();
    }
    void visit(AstNode*) override {}
};

}  // namespace

void V3EmitC::emitcGpu() {
    UINFO(2, __FUNCTION__ << ":");
    if (!v3Global.opt.gpu()) return;
    const EmitCParentModule emitCParentModule;
    const GpuMembers members = collectMembers();
    { EmitCGpuState{members}; }
    { EmitCGpuFunc{V3Gpu::modulep()}; }
    { EmitCGpuHost{members}; }
}
