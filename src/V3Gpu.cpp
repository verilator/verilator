// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: GPU model partitioning and resident mode
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

#include "V3PchAstNoMT.h"

#include "V3Gpu.h"

#include "V3EmitCBase.h"
#include "V3ExecGraph.h"
#include "V3File.h"
#include "V3Stats.h"

#include <fstream>
#include <iomanip>
#include <map>
#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

enum class GpuClass : uint8_t { DEVICE = 0, DEFER = 1, HOST = 2 };

const char* gpuClassName(GpuClass cls) {
    switch (cls) {
    case GpuClass::DEVICE: return "device";
    case GpuClass::DEFER: return "deferred";
    default: return "host";
    }
}

struct GpuFinding final {
    GpuClass m_cls = GpuClass::DEVICE;  // Where the statement can run
    std::string m_reason;  // Why it cannot run on the device
    const AstNode* m_nodep = nullptr;  // Node that forced the class
};

using GpuFuncReasons = std::unordered_map<const AstCFunc*, std::string>;

bool gpuResidentMode();
bool gpuResidentStmt(const AstNode* nodep);

class GpuStmtClassifier final : public VNVisitorConst {
    const GpuFuncReasons& m_hostFuncs;  // Functions known to be host-only
    GpuFinding m_found;  // Most restrictive finding so far
    size_t m_nodes = 0;  // Nodes visited, for statistics
    int m_inFormat = 0;  // Inside a format argument (display, sformat)

    void mark(GpuClass cls, const std::string& reason, const AstNode* nodep) {
        if (cls > m_found.m_cls) m_found = GpuFinding{cls, reason, nodep};
    }

    static std::string dtypeReason(const AstNodeDType* dtp) {
        if (const AstBasicDType* const bdtp = VN_CAST(dtp, BasicDType)) {
            if (bdtp->isString()) return "string";
            if (bdtp->isEvent()) return "event";
            if (bdtp->isForkSync()) return "fork sync";
            if (bdtp->isProcessRef()) return "process";
            if (bdtp->isDelayScheduler()) return "delay scheduler";
            if (bdtp->isTriggerScheduler() || bdtp->isDynamicTriggerScheduler())
                return "trigger scheduler";
            return "";
        }
        if (VN_IS(dtp, QueueDType)) return "queue";
        if (VN_IS(dtp, DynArrayDType)) return "dynamic array";
        if (VN_IS(dtp, AssocArrayDType)) return "associative array";
        if (VN_IS(dtp, WildcardArrayDType)) return "wildcard array";
        if (VN_IS(dtp, ClassRefDType)) return "class";
        return "";
    }

    void generic(AstNode* nodep) {
        ++m_nodes;
        if (m_inFormat) {
            iterateChildrenConst(nodep);
            return;
        }
        if (const AstNodeDType* const dtp = nodep->dtypep()) {
            const std::string reason = dtypeReason(dtp->skipRefp());
            if (!reason.empty()) mark(GpuClass::HOST, "type " + reason, nodep);
        }
        iterateChildrenConst(nodep);
    }
    static std::string rawText(const AstNode* nodesp) {
        std::string text;
        for (const AstNode* itemp = nodesp; itemp; itemp = itemp->nextp()) {
            if (const AstText* const textp = VN_CAST(itemp, Text)) {
                text += textp->text();
            } else {
                text += "<" + std::string{itemp->typeName()} + ">";
            }
            if (text.size() > 60) break;
        }
        for (char& c : text) {
            if (c == '\n') c = ' ';
        }
        return text.substr(0, 60);
    }
    void host(AstNode* nodep, const std::string& reason) {
        mark(GpuClass::HOST, reason, nodep);
        generic(nodep);
    }
    void defer(AstNode* nodep, const std::string& reason) {
        mark(GpuClass::DEFER, reason, nodep);
        generic(nodep);
    }
    void timeRef(AstNode* nodep) {
        if (m_inFormat) {
            generic(nodep);
        } else {
            host(nodep, "$time");
        }
    }
    void deferFormat(AstNode* nodep, const std::string& reason) {
        mark(GpuClass::DEFER, reason, nodep);
        ++m_inFormat;
        generic(nodep);
        --m_inFormat;
    }

    void visit(AstDisplay* nodep) override { deferFormat(nodep, "$display"); }
    void visit(AstFinish* nodep) override { deferFormat(nodep, "$finish"); }
    void visit(AstStop* nodep) override { deferFormat(nodep, "$stop"); }
    void visit(AstSFormat* nodep) override { host(nodep, "$sformat"); }
    void visit(AstFOpen* nodep) override { host(nodep, "file I/O"); }
    void visit(AstFOpenMcd* nodep) override { host(nodep, "file I/O"); }
    void visit(AstFClose* nodep) override { host(nodep, "file I/O"); }
    void visit(AstFFlush* nodep) override { host(nodep, "file I/O"); }
    void visit(AstFRead* nodep) override { host(nodep, "file I/O"); }
    void visit(AstFGetC* nodep) override { host(nodep, "file I/O"); }
    void visit(AstFGetS* nodep) override { host(nodep, "file I/O"); }
    void visit(AstFScanF* nodep) override { host(nodep, "file I/O"); }
    void visit(AstSScanF* nodep) override { host(nodep, "$sscanf"); }
    void visit(AstReadMem* nodep) override { host(nodep, "$readmem"); }
    void visit(AstWriteMem* nodep) override { host(nodep, "$writemem"); }
    void visit(AstSystemT* nodep) override { host(nodep, "$system"); }
    void visit(AstSystemF* nodep) override { host(nodep, "$system"); }
    void visit(AstTestPlusArgs* nodep) override { host(nodep, "plusargs"); }
    void visit(AstValuePlusArgs* nodep) override { host(nodep, "plusargs"); }
    void visit(AstTime* nodep) override {
        if (gpuResidentMode()) {
            generic(nodep);
            return;
        }
        timeRef(nodep);
    }
    void visit(AstTimeD* nodep) override {
        if (gpuResidentMode()) {
            generic(nodep);
            return;
        }
        timeRef(nodep);
    }
    void visit(AstRand* nodep) override { host(nodep, "random"); }
    void visit(AstRandRNG* nodep) override { host(nodep, "random"); }
    void visit(AstURandomRange* nodep) override { host(nodep, "random"); }
    void visit(AstRandCase* nodep) override { host(nodep, "random"); }
    void visit(AstCAwait* nodep) override { host(nodep, "timing"); }
    void visit(AstDelay* nodep) override { host(nodep, "timing"); }
    void visit(AstFork* nodep) override { host(nodep, "timing"); }
    void visit(AstWait* nodep) override { host(nodep, "timing"); }
    void visit(AstEventControl* nodep) override { host(nodep, "timing"); }
    void visit(AstFireEvent* nodep) override { host(nodep, "timing"); }
    void visit(AstCoverInc* nodep) override { host(nodep, "coverage"); }
    void visit(AstExecGraph* nodep) override { host(nodep, "exec graph"); }
    void visit(AstCStmt* nodep) override {
        if (V3Gpu::isGpuNoopStmt(nodep)) return;
        if (gpuResidentMode()) {
            if (gpuResidentStmt(nodep)) {
                ++m_nodes;
                return;
            }
            if (V3Gpu::isTimingDeviceStmt(nodep)) {
                ++m_nodes;
                for (AstNode* itemp = nodep->nodesp(); itemp; itemp = itemp->nextp()) {
                    iterateConst(itemp);
                }
                return;
            }
            bool known = false;
            V3Gpu::deviceCStmtText(nodep, known);
            if (known) {
                ++m_nodes;
                return;
            }
        }
        host(nodep, gpuResidentMode() ? "raw C: " + rawText(nodep->nodesp()) : "raw C");
    }
    void visit(AstCStmtUser* nodep) override { host(nodep, "raw C"); }
    void visit(AstCExpr* nodep) override {
        if (V3Gpu::isGpuAssertCtlExpr(nodep)) {
            generic(nodep);
            return;
        }
        if (gpuResidentMode()) {
            if (V3Gpu::isTimingDeviceStmt(nodep)) {
                ++m_nodes;
                for (AstNode* itemp = nodep->nodesp(); itemp; itemp = itemp->nextp()) {
                    iterateConst(itemp);
                }
                return;
            }
            if (!V3Gpu::deviceCExprText(nodep).empty()) {
                ++m_nodes;
                return;
            }
            host(nodep, "raw C: " + rawText(nodep->nodesp()));
            return;
        }
        host(nodep, "raw C");
    }
    void visit(AstCExprUser* nodep) override { host(nodep, "raw C"); }
    void visit(AstCMethodHard* nodep) override {
        if (gpuResidentMode()
            && (nodep->method() == VCMethod::UNPACKED_FILL
                || nodep->method() == VCMethod::UNPACKED_ASSIGN
                || nodep->method() == VCMethod::UNPACKED_NEQ)) {
            generic(nodep);
            return;
        }
        host(nodep, "method " + nodep->name());
    }
    void visit(AstCMethodCall* nodep) override { host(nodep, "class method"); }
    void visit(AstNodeCCall* nodep) override {
        const AstCFunc* const funcp = nodep->funcp();
        if (funcp->dpiImportWrapper() || funcp->dpiImportPrototype()) {
            if (!V3Gpu::isGpuDpi(funcp)) mark(GpuClass::HOST, "DPI " + funcp->name(), nodep);
        } else {
            const auto it = m_hostFuncs.find(funcp);
            if (it != m_hostFuncs.end() && !it->second.empty()) {
                mark(GpuClass::HOST, it->second, nodep);
            }
        }
        generic(nodep);
    }
    void visit(AstNode* nodep) override { generic(nodep); }

public:
    explicit GpuStmtClassifier(const GpuFuncReasons& hostFuncs)
        : m_hostFuncs{hostFuncs} {}
    GpuFinding classify(AstNode* stmtp, size_t& nodes) {
        m_found = GpuFinding{};
        m_nodes = 0;
        iterateConst(stmtp);
        nodes = m_nodes;
        return m_found;
    }
};

struct GpuTally final {
    size_t m_stmts = 0;  // Statements counted
    size_t m_nodes = 0;  // Nodes counted
    void add(size_t nodes) {
        ++m_stmts;
        m_nodes += nodes;
    }
};

struct GpuReasonInfo final {
    GpuClass m_cls = GpuClass::DEVICE;  // Class of statements with this reason
    GpuTally m_tally;  // Statements and nodes with this reason
    std::vector<std::string> m_samples;  // Example locations
};

class GpuAnalysis final {
    std::vector<AstCFunc*> m_funcps;  // Functions analyzed
    GpuFuncReasons m_hostFuncs;  // Host-only functions and why
    GpuTally m_tally[2][3];
    std::map<std::string, GpuReasonInfo> m_reasons[2];
    std::map<std::string, GpuTally> m_hostByFunc;

    void computeHostFuncs() {
        for (AstCFunc* const funcp : m_funcps) m_hostFuncs[funcp] = "";
        bool changed = true;
        while (changed) {
            changed = false;
            GpuStmtClassifier classifier{m_hostFuncs};
            for (AstCFunc* const funcp : m_funcps) {
                if (!m_hostFuncs[funcp].empty()) continue;
                for (AstNode* stmtp = funcp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                    size_t nodes = 0;
                    const GpuFinding found = classifier.classify(stmtp, nodes);
                    if (found.m_cls == GpuClass::HOST) {
                        m_hostFuncs[funcp] = found.m_reason;
                        changed = true;
                        break;
                    }
                }
            }
        }
    }

    void tallyOne(GpuStmtClassifier& classifier, AstNode* nodep, const AstCFunc* funcp, int slow) {
        size_t nodes = 0;
        const GpuFinding found = classifier.classify(nodep, nodes);
        m_tally[slow][static_cast<int>(found.m_cls)].add(nodes);
        if (found.m_cls == GpuClass::DEVICE) return;
        GpuReasonInfo& info = m_reasons[slow][found.m_reason];
        info.m_cls = found.m_cls;
        info.m_tally.add(nodes);
        if (info.m_samples.size() < 5) {
            info.m_samples.push_back(found.m_nodep->fileline()->ascii() + "  in " + funcp->name());
        }
        if (!slow && found.m_cls == GpuClass::HOST) m_hostByFunc[funcp->name()].add(nodes);
    }

    void tallyList(GpuStmtClassifier& classifier, AstNode* listp, const AstCFunc* funcp,
                   int slow) {
        for (AstNode* stmtp = listp; stmtp; stmtp = stmtp->nextp()) {
            if (const AstStmtExpr* const sep = VN_CAST(stmtp, StmtExpr)) {
                if (const AstCCall* const callp = VN_CAST(sep->exprp(), CCall)) {
                    const AstCFunc* const calleep = callp->funcp();
                    if (!calleep->dpiImportWrapper() && !calleep->dpiImportPrototype()) continue;
                }
            }
            if (AstIf* const ifp = VN_CAST(stmtp, If)) {
                tallyOne(classifier, ifp->condp(), funcp, slow);
                tallyList(classifier, ifp->thensp(), funcp, slow);
                tallyList(classifier, ifp->elsesp(), funcp, slow);
            } else if (AstLoop* const loopp = VN_CAST(stmtp, Loop)) {
                tallyList(classifier, loopp->stmtsp(), funcp, slow);
            } else if (AstJumpBlock* const blockp = VN_CAST(stmtp, JumpBlock)) {
                tallyList(classifier, blockp->stmtsp(), funcp, slow);
            } else if (AstNodeBlock* const blockp = VN_CAST(stmtp, NodeBlock)) {
                tallyList(classifier, blockp->stmtsp(), funcp, slow);
            } else {
                tallyOne(classifier, stmtp, funcp, slow);
            }
        }
    }

    void tally() {
        GpuStmtClassifier classifier{m_hostFuncs};
        for (AstCFunc* const funcp : m_funcps) {
            tallyList(classifier, funcp->stmtsp(), funcp, funcp->slow() ? 1 : 0);
        }
    }

    static std::string pct(size_t part, size_t total) {
        if (!total) return "0.0%";
        std::ostringstream os;
        os << std::fixed << std::setprecision(1) << (100.0 * part / total) << "%";
        return os.str();
    }

    void report() {
        const std::string filename
            = v3Global.opt.makeDir() + "/" + v3Global.opt.prefix() + "__gpu_report.txt";
        const std::unique_ptr<std::ofstream> ofp{V3File::new_ofstream(filename)};
        if (ofp->fail()) v3fatal("Can't write file: " << filename);
        std::ostream& os = *ofp;
        for (const int slow : {0, 1}) {
            size_t totalStmts = 0;
            size_t totalNodes = 0;
            for (const GpuTally& t : m_tally[slow]) {
                totalStmts += t.m_stmts;
                totalNodes += t.m_nodes;
            }
            os << (slow ? "Slow path (initial, settle, static)" : "Fast path (every evaluation)")
               << ": " << totalStmts << " statements, " << totalNodes << " AST nodes\n";
            for (int cls = 0; cls < 3; ++cls) {
                const GpuTally& t = m_tally[slow][cls];
                os << "  " << std::left << std::setw(9) << gpuClassName(static_cast<GpuClass>(cls))
                   << std::right << std::setw(9) << t.m_stmts << " stmts  " << std::setw(10)
                   << t.m_nodes << " nodes  " << std::setw(6) << pct(t.m_nodes, totalNodes)
                   << "\n";
                V3Stats::addStat(std::string{"GPU, "} + (slow ? "slow " : "fast ")
                                     + gpuClassName(static_cast<GpuClass>(cls)) + " nodes",
                                 t.m_nodes);
            }
            os << "  Reasons:\n";
            std::vector<std::pair<std::string, const GpuReasonInfo*>> sorted;
            for (const auto& it : m_reasons[slow]) sorted.emplace_back(it.first, &it.second);
            std::stable_sort(sorted.begin(), sorted.end(), [](const auto& a, const auto& b) {
                return a.second->m_tally.m_nodes > b.second->m_tally.m_nodes;
            });
            for (const auto& it : sorted) {
                const GpuReasonInfo& info = *it.second;
                os << "    " << std::left << std::setw(9) << gpuClassName(info.m_cls)
                   << std::setw(48) << it.first << std::right << std::setw(9)
                   << info.m_tally.m_stmts << " stmts  " << std::setw(10) << info.m_tally.m_nodes
                   << " nodes\n";
                for (const std::string& sample : info.m_samples) {
                    os << "        " << sample << "\n";
                }
            }
            os << "\n";
        }
        os << "Fast-path functions with host statements:\n";
        std::vector<std::pair<std::string, GpuTally>> funcs{m_hostByFunc.begin(),
                                                            m_hostByFunc.end()};
        std::stable_sort(funcs.begin(), funcs.end(), [](const auto& a, const auto& b) {
            return a.second.m_nodes > b.second.m_nodes;
        });
        for (const auto& it : funcs) {
            os << "  " << std::left << std::setw(60) << it.first << std::right << std::setw(9)
               << it.second.m_stmts << " stmts  " << std::setw(10) << it.second.m_nodes
               << " nodes\n";
        }
    }

public:
    explicit GpuAnalysis(AstNetlist* netlistp) {
        netlistp->foreach([this](AstCFunc* funcp) {
            if (funcp->dpiImportPrototype()) return;
            m_funcps.push_back(funcp);
        });
        computeHostFuncs();
        tally();
        report();
    }
    const GpuFuncReasons& hostFuncs() const { return m_hostFuncs; }
};

struct GpuRegistry final {
    GpuFuncReasons m_hostFuncs;  // Host-only functions and why
    std::vector<AstCFunc*> m_deviceFuncs;  // Functions emitted for the device
    std::unordered_set<const AstCFunc*> m_deviceSet;
    std::unordered_set<const AstCFunc*> m_kernelBodies;
    std::vector<V3GpuGroup> m_groups;  // Hybrid-mode kernel groups
    std::vector<V3GpuReplay> m_replays;  // Deferred output records
    std::unordered_map<const AstNode*, int> m_replayIds;
    std::unordered_set<const AstVar*> m_members;
    std::unordered_set<const AstVar*> m_hostMembers;
    AstNodeModule* m_modp = nullptr;  // Top module
    bool m_residentMode = false;  // Resident mode is used
    V3GpuResident m_resident;  // Resident-mode structure
    std::unordered_map<const AstNode*, std::pair<int, int>> m_graphPoints;
    std::unordered_set<const AstNode*> m_residentStmts;
    std::unordered_map<const AstNode*, AstVar*> m_graphPointPcs;
    std::unordered_set<const AstCFunc*> m_graphFuncs;
    std::vector<std::string> m_fatalMsgs;  // Messages of device fatal errors
};

GpuRegistry& registry() {
    static GpuRegistry s_registry;
    return s_registry;
}

bool gpuResidentMode() { return registry().m_residentMode; }
bool gpuResidentStmt(const AstNode* nodep) {
    return registry().m_residentStmts.count(nodep) || registry().m_graphPoints.count(nodep);
}

bool isDeferredStmt(const AstNode* nodep) {
    return VN_IS(nodep, Display) || VN_IS(nodep, Stop) || VN_IS(nodep, Finish);
}

void gpuMakeReplay(AstNode* stmtp, AstNodeModule* modp) {
    GpuRegistry& m_reg = registry();  // GPU state of this Verilation
    AstNodeModule* const m_modp = modp;  // Module receiving replay functions
    if (m_reg.m_replayIds.count(stmtp)) return;
    const int id = static_cast<int>(m_reg.m_replays.size());
    FileLine* const flp = stmtp->fileline();
    AstCFunc* const funcp = new AstCFunc{flp, "__Vgpu_replay_" + std::to_string(id), nullptr};
    funcp->isLoose(true);
    funcp->isConst(false);
    funcp->declPrivate(false);
    funcp->dontCombine(true);
    funcp->slow(true);
    const std::vector<AstVar*> vars = V3GpuCapture::vars(stmtp);
    std::string load = "const uint8_t* __Vgpu_p = VerilatedGpu::replayCursor();\n";
    std::string restore;
    int saveNum = 0;
    for (AstVar* const varp : vars) {
        if (!V3Gpu::isMember(varp)) {
            funcp->addVarsp(varp->cloneTree(false));
            const std::string ref = varp->nameProtect();
            load += "std::memcpy(&" + ref + ", __Vgpu_p, sizeof(" + ref + ")); __Vgpu_p += sizeof("
                    + ref + ");\n";
        } else {
            const std::string ref = "vlSelfRef." + V3GpuCapture::memberName(varp);
            const std::string save = "__Vgpu_save_" + std::to_string(saveNum++);
            load += "auto " + save + " = " + ref + ";\n";
            load += "std::memcpy(&" + ref + ", __Vgpu_p, sizeof(" + ref + ")); __Vgpu_p += sizeof("
                    + ref + ");\n";
            restore += ref + " = " + save + ";\n";
        }
    }
    funcp->addStmtsp(new AstCStmt{flp, load});
    funcp->addStmtsp(VN_AS(stmtp->cloneTree(false), NodeStmt));
    if (!restore.empty()) funcp->addStmtsp(new AstCStmt{flp, restore});
    m_modp->addStmtsp(funcp);
    m_reg.m_replayIds.emplace(stmtp, id);
    m_reg.m_replays.push_back(V3GpuReplay{id, funcp});
}

class GpuPartition final {
    GpuRegistry& m_reg = registry();  // GPU state of this Verilation
    GpuStmtClassifier m_classifier{m_reg.m_hostFuncs};  // Classifies statements
    std::unordered_set<const AstCFunc*> m_mtaskFuncs;
    std::unordered_set<const AstCFunc*> m_graphHostFuncs;
    std::unordered_set<const AstCFunc*> m_splitTasks;
    AstNodeModule* m_modp = nullptr;  // Top module
    int m_nextGroup = 0;  // Number of the next kernel group

    bool deviceCapable(const AstCFunc* funcp) const {
        if (funcp->slow() || !funcp->isLoose() || funcp->isStatic()) return false;
        if (funcp->argsp() || funcp->isCoroutine() || funcp->needsVlProcess()) return false;
        if (funcp->dpiImportWrapper() || funcp->dpiImportPrototype() || funcp->dpiExportImpl())
            return false;
        if (funcp->entryPoint() || funcp->isConstructor() || funcp->isDestructor()) return false;
        if (!funcp->ifdef().empty()) return false;
        if (funcp->voidSelf() && !m_mtaskFuncs.count(funcp)) return false;
        if (!funcp->rtnTypeVoid().empty() && funcp->rtnTypeVoid() != "void") return false;
        const auto it = m_reg.m_hostFuncs.find(funcp);
        return it != m_reg.m_hostFuncs.end() && it->second.empty();
    }

    bool outlinable(AstNode* stmtp) {
        if (!VN_IS(stmtp, NodeStmt)) return false;
        if (VN_IS(stmtp, CReturn) || VN_IS(stmtp, JumpGo) || VN_IS(stmtp, JumpBlock)) return false;
        size_t nodes = 0;
        if (m_classifier.classify(stmtp, nodes).m_cls == GpuClass::HOST) return false;
        bool ok = true;
        stmtp->foreach([&](const AstNode* nodep) {
            if (!ok) return;
            if (const AstNodeCCall* const callp = VN_CAST(nodep, NodeCCall)) {
                if (V3Gpu::isGpuDpi(callp->funcp())) return;
                if (callp->argsp() || !m_reg.m_deviceSet.count(callp->funcp())) ok = false;
            } else if (const AstVarRef* const refp = VN_CAST(nodep, VarRef)) {
                const AstVar* const varp = refp->varp();
                if (!varp->constPoolEntry() && !m_reg.m_members.count(varp)) ok = false;
            } else if (VN_IS(nodep, CReturn) || VN_IS(nodep, JumpGo) || VN_IS(nodep, JumpBlock)) {
                ok = false;
            }
        });
        return ok;
    }

    static std::string runCall(int id, int levelBegin, int levelEnd) {
        const std::string prefix = v3Global.opt.prefix();
        return "extern void " + prefix
               + "__gpuRun(void* vlSelf, int groupId, int levelBegin, int levelEnd);\n" + prefix
               + "__gpuRun(vlSelf, " + std::to_string(id) + ", " + std::to_string(levelBegin)
               + ", " + std::to_string(levelEnd) + ");";
    }

    AstNode* outline(std::vector<AstNode*>& run, AstCFunc* hostp) {
        const int id = m_nextGroup++;
        FileLine* const flp = run.front()->fileline();
        const std::string base = "__Vgpu_group_" + std::to_string(id);
        AstCFunc* const bodyp = new AstCFunc{flp, base + "__body", hostp->scopep()};
        bodyp->isLoose(true);
        bodyp->isConst(false);
        bodyp->declPrivate(true);
        bodyp->dontCombine(true);
        bodyp->ifdef(V3Gpu::kernelBodyIfdef());
        AstCFunc* const launchp = new AstCFunc{flp, base, hostp->scopep()};
        launchp->isLoose(true);
        launchp->isConst(false);
        launchp->declPrivate(true);
        launchp->dontCombine(true);
        launchp->addStmtsp(new AstCStmt{flp, runCall(id, 0, 0)});
        AstNode* const firstp = run.front();
        AstCCall* const callp = new AstCCall{flp, launchp};
        callp->dtypeSetVoid();
        callp->selfPointer(VSelfPointerText{VSelfPointerText::This{}});
        AstNode* const replacementp = callp->makeStmt();
        firstp->replaceWith(replacementp);
        bodyp->addStmtsp(VN_AS(firstp, NodeStmt));
        for (size_t i = 1; i < run.size(); ++i) {
            bodyp->addStmtsp(VN_AS(run[i]->unlinkFrBack(), NodeStmt));
        }
        m_modp->addStmtsp(bodyp);
        m_modp->addStmtsp(launchp);
        m_reg.m_kernelBodies.insert(bodyp);
        m_reg.m_groups.push_back(V3GpuGroup{id, launchp, bodyp, {}, {}});
        run.clear();
        return replacementp;
    }

    bool graphOnDevice(AstExecGraph* graphp) const {
        for (const AstCCall* callp = graphp->callsp(); callp;
             callp = VN_AS(callp->nextp(), CCall)) {
            if (m_reg.m_deviceSet.count(callp->funcp())) return true;
        }
        return false;
    }

    AstCFunc* extractPiece(AstCFunc* taskp, bool lead) {
        std::vector<AstNode*> stmts;
        if (lead) {
            for (AstNode* stmtp = taskp->stmtsp(); stmtp && outlinable(stmtp);
                 stmtp = stmtp->nextp()) {
                stmts.push_back(stmtp);
            }
        } else {
            std::vector<AstNode*> all;
            for (AstNode* stmtp = taskp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                all.push_back(stmtp);
            }
            for (auto it = all.rbegin(); it != all.rend() && outlinable(*it); ++it) {
                stmts.push_back(*it);
            }
            std::reverse(stmts.begin(), stmts.end());
        }
        if (stmts.empty()) return nullptr;
        FileLine* const flp = stmts.front()->fileline();
        AstCFunc* const funcp = new AstCFunc{
            flp, taskp->name() + (lead ? "__Vgpu_lead" : "__Vgpu_trail"), taskp->scopep()};
        funcp->isLoose(true);
        funcp->isConst(false);
        funcp->declPrivate(true);
        funcp->dontCombine(true);
        funcp->ifdef(V3Gpu::kernelBodyIfdef());
        for (AstNode* const stmtp : stmts)
            funcp->addStmtsp(VN_AS(stmtp->unlinkFrBack(), NodeStmt));
        m_modp->addStmtsp(funcp);
        m_reg.m_kernelBodies.insert(funcp);
        m_reg.m_deviceFuncs.push_back(funcp);
        m_reg.m_deviceSet.insert(funcp);
        V3Stats::addStatSum("GPU, host graph tasks split", 1);
        return funcp;
    }

    AstNode* outlineGraph(AstExecGraph* graphp, AstCFunc* hostp) {
        std::vector<AstNode*> run{graphp};
        AstNode* const replacementp = outline(run, hostp);
        V3GpuGroup& group = m_reg.m_groups.back();
        std::unordered_map<const V3GraphVertex*, int> levels;
        std::unordered_map<const AstCFunc*, const V3GraphVertex*> vertexOf;
        for (const V3GraphVertex& vtx : graphp->depGraphp()->vertices()) {
            vertexOf.emplace(vtx.as<ExecMTask>()->funcp(), &vtx);
        }
        const auto place = [&](int level, AstCFunc* funcp, bool device) {
            if (static_cast<int>(group.m_levels.size()) <= level) {
                group.m_levels.resize(level + 1);
                group.m_hostLevels.resize(level + 1);
            }
            (device ? group.m_levels : group.m_hostLevels)[level].push_back(funcp);
        };
        std::vector<AstCFunc*> hostTasks;
        for (AstCCall* callp = graphp->callsp(); callp; callp = VN_AS(callp->nextp(), CCall)) {
            AstCFunc* const taskp = callp->funcp();
            const V3GraphVertex* const vtxp = vertexOf.at(taskp);
            int level = 0;
            for (const V3GraphEdge& edge : vtxp->inEdges()) {
                const auto it = levels.find(edge.fromp());
                UASSERT_OBJ(it != levels.end(), callp, "MTask calls not in topological order");
                level = std::max(level, it->second + 1);
            }
            int outLevel = level;
            if (m_reg.m_deviceSet.count(taskp)) {
                place(level, taskp, true);
            } else {
                AstCFunc* const leadp = extractPiece(taskp, true);
                AstCFunc* const trailp = taskp->stmtsp() ? extractPiece(taskp, false) : nullptr;
                if (leadp) place(level, leadp, true);
                if (taskp->stmtsp()) {
                    place(level, taskp, false);
                    hostTasks.push_back(taskp);
                }
                if (trailp) {
                    outLevel = level + 1;
                    place(outLevel, trailp, true);
                }
            }
            levels.emplace(vtxp, outLevel);
        }
        AstCFunc* const launchp = group.m_launchp;
        FileLine* const flp = graphp->fileline();
        while (AstNode* const oldp = launchp->stmtsp())
            VL_DO_DANGLING(oldp->unlinkFrBack()->deleteTree(), oldp);
        int begin = 0;
        const int nLevels = static_cast<int>(group.m_levels.size());
        for (int level = 0; level < nLevels; ++level) {
            if (group.m_hostLevels[level].empty() && level + 1 < nLevels) continue;
            launchp->addStmtsp(new AstCStmt{flp, runCall(group.m_id, begin, level + 1)});
            for (AstCFunc* const taskp : group.m_hostLevels[level]) {
                AstCCall* const callp = new AstCCall{flp, taskp};
                callp->dtypeSetVoid();
                callp->selfPointer(VSelfPointerText{VSelfPointerText::This{}});
                launchp->addStmtsp(callp->makeStmt());
                V3Stats::addStatSum("GPU, host graph tasks", 1);
            }
            begin = level + 1;
        }
        if (AstCFunc* const runp = graphp->runfuncp()) {
            m_graphHostFuncs.insert(runp);
            runp->foreach(
                [&](const AstAddrOfCFunc* addrp) { m_graphHostFuncs.insert(addrp->funcp()); });
        }
        V3Stats::addStat("GPU, graph levels", group.m_levels.size());
        V3Stats::addStat("GPU, graph segments",
                         std::count_if(group.m_hostLevels.begin(), group.m_hostLevels.end(),
                                       [](const std::vector<AstCFunc*>& v) { return !v.empty(); })
                             + 1);
        for (AstCFunc* const taskp : hostTasks) processList(taskp->stmtsp(), taskp);
        return replacementp;
    }

    void processList(AstNode* listp, AstCFunc* hostp) {
        std::vector<std::vector<AstNode*>> runs;
        std::vector<AstNode*> run;
        for (AstNode* stmtp = listp; stmtp; stmtp = stmtp->nextp()) {
            if (AstExecGraph* const graphp = VN_CAST(stmtp, ExecGraph)) {
                if (graphOnDevice(graphp)) {
                    if (!run.empty()) runs.push_back(std::move(run));
                    run.clear();
                    for (std::vector<AstNode*>& r : runs) outline(r, hostp);
                    runs.clear();
                    stmtp = outlineGraph(graphp, hostp);
                    continue;
                }
            }
            if (outlinable(stmtp)) {
                run.push_back(stmtp);
                continue;
            }
            if (!run.empty()) runs.push_back(std::move(run));
            run.clear();
            if (AstIf* const ifp = VN_CAST(stmtp, If)) {
                processList(ifp->thensp(), hostp);
                processList(ifp->elsesp(), hostp);
            } else if (AstLoop* const loopp = VN_CAST(stmtp, Loop)) {
                processList(loopp->stmtsp(), hostp);
            } else if (AstJumpBlock* const blockp = VN_CAST(stmtp, JumpBlock)) {
                processList(blockp->stmtsp(), hostp);
            } else if (AstNodeBlock* const blockp = VN_CAST(stmtp, NodeBlock)) {
                processList(blockp->stmtsp(), hostp);
            }
        }
        if (!run.empty()) runs.push_back(std::move(run));
        for (std::vector<AstNode*>& r : runs) outline(r, hostp);
    }

    void makeReplay(AstNode* stmtp) { gpuMakeReplay(stmtp, m_modp); }

    void findReplays(AstCFunc* funcp) {
        funcp->foreach([this](AstNode* nodep) {
            if (isDeferredStmt(nodep)) makeReplay(nodep);
        });
    }

    void collectHostMembers(const std::vector<AstCFunc*>& funcps) {
        std::unordered_set<const AstCFunc*> reached;
        std::vector<const AstCFunc*> work;
        for (const AstCFunc* const funcp : funcps) {
            if (funcp->slow() || m_reg.m_deviceSet.count(funcp)) continue;
            if (m_graphHostFuncs.count(funcp)) continue;
            if (reached.insert(funcp).second) work.push_back(funcp);
        }
        for (const V3GpuGroup& group : m_reg.m_groups) {
            if (reached.insert(group.m_launchp).second) work.push_back(group.m_launchp);
        }
        while (!work.empty()) {
            const AstCFunc* const funcp = work.back();
            work.pop_back();
            funcp->foreach([&](const AstNode* nodep) {
                if (const AstNodeCCall* const callp = VN_CAST(nodep, NodeCCall)) {
                    const AstCFunc* const calleep = callp->funcp();
                    if (calleep->slow() || m_reg.m_kernelBodies.count(calleep)) return;
                    if (m_graphHostFuncs.count(calleep)) return;
                    if (reached.insert(calleep).second) work.push_back(calleep);
                } else if (const AstVarRef* const refp = VN_CAST(nodep, VarRef)) {
                    if (m_reg.m_members.count(refp->varp())) {
                        m_reg.m_hostMembers.insert(refp->varp());
                    }
                }
            });
        }
        V3Stats::addStat("GPU, host-reachable functions", reached.size());
        V3Stats::addStat("GPU, host-referenced members", m_reg.m_hostMembers.size());
    }

public:
    explicit GpuPartition(AstNetlist* netlistp) {
        m_modp = netlistp->topModulep();
        m_reg.m_modp = m_modp;
        for (AstNode* nodep = m_modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstVar* const varp = VN_CAST(nodep, Var)) m_reg.m_members.insert(varp);
        }
        std::vector<AstCFunc*> funcps;
        netlistp->foreach([&](AstCFunc* funcp) { funcps.push_back(funcp); });
        netlistp->foreach([&](const AstExecGraph* graphp) {
            for (const AstCCall* callp = graphp->callsp(); callp;
                 callp = VN_AS(callp->nextp(), CCall)) {
                m_mtaskFuncs.insert(callp->funcp());
            }
        });
        for (AstCFunc* const funcp : funcps) {
            if (deviceCapable(funcp)) {
                m_reg.m_deviceFuncs.push_back(funcp);
                m_reg.m_deviceSet.insert(funcp);
            }
        }
        netlistp->foreach([&](AstExecGraph* graphp) {
            if (!graphOnDevice(graphp)) return;
            if (AstCFunc* const runp = graphp->runfuncp()) m_graphHostFuncs.insert(runp);
            for (const AstCCall* callp = graphp->callsp(); callp;
                 callp = VN_AS(callp->nextp(), CCall)) {
                if (!m_reg.m_deviceSet.count(callp->funcp())) m_splitTasks.insert(callp->funcp());
            }
        });
        for (AstCFunc* const funcp : funcps) {
            if (m_reg.m_deviceSet.count(funcp)) continue;
            bool callsTask = false;
            funcp->foreach([&](const AstCCall* callp) {
                if (!m_mtaskFuncs.count(callp->funcp())) return;
                const AstNode* headp = callp;
                while (headp->backp() && headp->backp()->nextp() == headp) headp = headp->backp();
                if (!VN_IS(headp->backp(), ExecGraph)) callsTask = true;
            });
            if (callsTask) m_graphHostFuncs.insert(funcp);
        }
        for (AstCFunc* const funcp : funcps) {
            if (funcp->slow() || funcp->isCoroutine() || m_reg.m_deviceSet.count(funcp)) continue;
            if (m_graphHostFuncs.count(funcp) || m_splitTasks.count(funcp)) continue;
            if (funcp->name().rfind("_eval_triggers", 0) == 0) continue;
            processList(funcp->stmtsp(), funcp);
        }
        for (const V3GpuGroup& group : m_reg.m_groups) {
            m_reg.m_deviceFuncs.push_back(group.m_bodyp);
            m_reg.m_deviceSet.insert(group.m_bodyp);
        }
        for (AstCFunc* const funcp : m_reg.m_deviceFuncs) findReplays(funcp);
        collectHostMembers(funcps);
        V3Stats::addStat("GPU, device functions", m_reg.m_deviceFuncs.size());
        V3Stats::addStat("GPU, kernel groups", m_reg.m_groups.size());
        V3Stats::addStat("GPU, deferred statements", m_reg.m_replays.size());
    }
};

}  // namespace

bool V3Gpu::isGpuNoopStmt(const AstNode* nodep) {
    const AstCStmt* const cstmtp = VN_CAST(nodep, CStmt);
    if (!cstmtp) return false;
    std::string text;
    for (const AstNode* itemp = cstmtp->nodesp(); itemp; itemp = itemp->nextp()) {
        const AstText* const textp = VN_CAST(itemp, Text);
        if (!textp) return false;
        text += textp->text();
    }
    return text.rfind("Verilated::mtaskId(", 0) == 0
           || text.rfind("Verilated::endOfThreadMTask(", 0) == 0;
}

namespace {
const std::string& assertCtlHostPrefix() {
    static const std::string s_prefix = "vlSymsp->_vm_contextp__->assertCtlGet<";
    return s_prefix;
}
}  // namespace

std::string V3Gpu::gpuAssertCtlText(const AstNode* nodep) {
    const AstCExpr* const exprp = VN_CAST(nodep, CExpr);
    if (!exprp) return "";
    std::string text;
    for (const AstNode* itemp = exprp->nodesp(); itemp; itemp = itemp->nextp()) {
        const AstText* const textp = VN_CAST(itemp, Text);
        if (!textp) return "";
        text += textp->text();
    }
    const std::string& prefix = assertCtlHostPrefix();
    std::string result;
    size_t pos = 0;
    bool found = false;
    while (true) {
        const size_t at = text.find(prefix, pos);
        if (at == std::string::npos) break;
        result += text.substr(pos, at - pos) + "vlGpuAssertCtlGet<";
        pos = at + prefix.size();
        found = true;
    }
    result += text.substr(pos);
    if (!found) return "";
    if (result.find("vlSymsp") != std::string::npos || result.find("vlSelf") != std::string::npos)
        return "";
    return result;
}

bool V3Gpu::isGpuAssertCtlExpr(const AstNode* nodep) { return !gpuAssertCtlText(nodep).empty(); }

std::string V3Gpu::dpiName(const AstCFunc* funcp) {
    static std::unordered_map<const AstCFunc*, std::string> s_names;
    const auto it = s_names.find(funcp);
    if (it != s_names.end()) return it->second;
    std::string name;
    if (funcp->dpiImportPrototype()) {
        name = funcp->cname();
    } else if (funcp->dpiImportWrapper()) {
        funcp->foreach([&](const AstNodeCCall* callp) {
            if (name.empty() && callp->funcp()->dpiImportPrototype())
                name = callp->funcp()->cname();
        });
    }
    if (name.empty()) name = funcp->cname();
    s_names.emplace(funcp, name);
    return name;
}

bool V3Gpu::isGpuDpi(const AstCFunc* funcp) {
    if (!funcp->dpiImportWrapper()) return false;
    const std::string name = dpiName(funcp);
    return !name.empty() && v3Global.opt.gpuDpis().count(name) > 0;
}

std::vector<AstVar*> V3GpuCapture::vars(const AstNode* stmtp) {
    std::vector<AstVar*> result;
    std::unordered_set<const AstVar*> seen;
    stmtp->foreach([&](const AstVarRef* refp) {
        AstVar* const varp = refp->varp();
        if (varp->constPoolEntry()) return;
        if (seen.insert(varp).second) result.push_back(varp);
    });
    return result;
}

std::string V3GpuCapture::memberName(const AstVar* varp) {
    return EmitCBaseVisitorConst::varName(varp);
}

void V3Gpu::analyze(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    GpuAnalysis analysis{nodep};
    registry().m_hostFuncs = analysis.hostFuncs();
}

void V3Gpu::partition(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    const EmitCParentModule emitCParentModule;
    GpuPartition{nodep};
}

bool V3Gpu::isDeviceFunc(const AstCFunc* funcp) { return registry().m_deviceSet.count(funcp) > 0; }
bool V3Gpu::isKernelBody(const AstCFunc* funcp) {
    return registry().m_kernelBodies.count(funcp) > 0;
}
const std::vector<AstCFunc*>& V3Gpu::deviceFuncs() { return registry().m_deviceFuncs; }
const std::vector<V3GpuGroup>& V3Gpu::groups() { return registry().m_groups; }
const std::vector<V3GpuReplay>& V3Gpu::replays() { return registry().m_replays; }
int V3Gpu::replayId(const AstNode* stmtp) {
    const auto it = registry().m_replayIds.find(stmtp);
    return it == registry().m_replayIds.end() ? -1 : it->second;
}
AstNodeModule* V3Gpu::modulep() { return registry().m_modp; }
bool V3Gpu::isMember(const AstVar* varp) { return registry().m_members.count(varp) > 0; }
bool V3Gpu::isHostMember(const AstVar* varp) { return registry().m_hostMembers.count(varp) > 0; }

namespace {

const AstCFunc* enclosingCFunc(const AstNode* nodep) {
    const AstNode* curp = nodep;
    while (curp) {
        if (const AstCFunc* const funcp = VN_CAST(curp, CFunc)) return funcp;
        const AstNode* backp = curp->backp();
        while (backp && backp->nextp() == curp) {
            curp = backp;
            backp = curp->backp();
        }
        curp = backp;
    }
    return nullptr;
}

class GpuResidentPrepare final {
    GpuRegistry& m_reg = registry();  // GPU state of this Verilation
    AstNetlist* const m_netlistp;  // Netlist being prepared
    AstNodeModule* m_modp = nullptr;  // Top module
    std::map<std::string, AstCFunc*> m_funcs;

    void addMember(AstVar* varp) {
        for (AstNode* nodep = m_modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            const AstVar* const curp = VN_CAST(nodep, Var);
            if (!curp
                || (curp->isModelState() && !curp->isPrimaryIO()
                    && !curp->isTriviallyConstructible())
                || !curp->isModelState()) {
                nodep->addHereThisAsNext(varp);
                return;
            }
        }
        m_modp->addStmtsp(varp);
    }
    AstVar* newMember(const std::string& name) {
        AstVar* const varp = new AstVar{m_modp->fileline(), VVarType::MODULETEMP, name,
                                        m_netlistp->findUInt32DType()};
        addMember(varp);
        return varp;
    }
    static AstVarRef* ref(AstVar* varp, VAccess access = VAccess::READ) {
        AstVarRef* const refp = new AstVarRef{varp->fileline(), varp, access};
        refp->selfPointer(VSelfPointerText{VSelfPointerText::This{}});
        return refp;
    }
    AstCStmt* stmt(FileLine* flp) {
        AstCStmt* const stmtp = new AstCStmt{flp};
        m_reg.m_residentStmts.insert(stmtp);
        return stmtp;
    }

    bool isRegion(const AstCFunc* funcp) const {
        const V3GpuResident& r = m_reg.m_resident;
        return funcp == r.m_icop || funcp == r.m_actp || funcp == r.m_inactp || funcp == r.m_nbap
               || funcp == r.m_obsp || funcp == r.m_reactp;
    }

    V3GpuResidentGraph graphInfo(AstExecGraph* graphp) {
        V3GpuResidentGraph info;
        info.m_levels = graphLevels(graphp);
        std::unordered_map<const AstCFunc*, int> indexOf;
        for (const std::vector<AstCFunc*>& level : info.m_levels) {
            for (AstCFunc* const funcp : level) {
                indexOf.emplace(funcp, static_cast<int>(info.m_order.size()));
                info.m_order.push_back(funcp);
            }
        }
        info.m_preds.resize(info.m_order.size());
        for (const V3GraphVertex& vtx : graphp->depGraphp()->vertices()) {
            const int to = indexOf.at(vtx.as<ExecMTask>()->funcp());
            for (const V3GraphEdge& edge : vtx.inEdges()) {
                info.m_preds[to].push_back(indexOf.at(edge.fromp()->as<ExecMTask>()->funcp()));
            }
        }
        return info;
    }

    std::vector<std::vector<AstCFunc*>> graphLevels(AstExecGraph* graphp) {
        std::vector<std::vector<AstCFunc*>> levels;
        std::unordered_map<const V3GraphVertex*, int> levelOf;
        std::unordered_map<const AstCFunc*, const V3GraphVertex*> vertexOf;
        for (const V3GraphVertex& vtx : graphp->depGraphp()->vertices()) {
            vertexOf.emplace(vtx.as<ExecMTask>()->funcp(), &vtx);
        }
        for (AstCCall* callp = graphp->callsp(); callp; callp = VN_AS(callp->nextp(), CCall)) {
            const V3GraphVertex* const vtxp = vertexOf.at(callp->funcp());
            int level = 0;
            for (const V3GraphEdge& edge : vtxp->inEdges()) {
                level = std::max(level, levelOf.at(edge.fromp()) + 1);
            }
            levelOf.emplace(vtxp, level);
            if (static_cast<int>(levels.size()) <= level) levels.resize(level + 1);
            levels[level].push_back(callp->funcp());
        }
        return levels;
    }

    void protothread(AstCFunc* funcp,
                     const std::vector<std::pair<AstNode*, AstExecGraph*>>& points) {
        FileLine* const flp = funcp->fileline();
        AstVar* const pcp = newMember("__Vgpu_rpc_" + funcp->name());
        std::vector<AstVar*> locals;
        funcp->foreach([&](AstVar* varp) {
            if (!varp->isIO()) locals.push_back(varp);
        });
        std::unordered_set<const AstVar*> localSet{locals.begin(), locals.end()};
        funcp->foreach([&](AstVarRef* refp) {
            if (localSet.count(refp->varp())) {
                refp->selfPointer(VSelfPointerText{VSelfPointerText::This{}});
            }
        });
        for (AstVar* const varp : locals) {
            varp->unlinkFrBack();
            varp->name("__Vgpu_rl_" + funcp->name() + "__" + varp->name());
            varp->funcLocal(false);
            varp->varType(VVarType::MODULETEMP);
            varp->lifetime(VLifetime::STATIC_EXPLICIT);
            addMember(varp);
        }
        int label = 1;
        for (const auto& point : points) {
            AstNode* const callStmtp = point.first;
            AstExecGraph* const graphp = point.second;
            const int graph = static_cast<int>(m_reg.m_resident.m_graphs.size());
            m_reg.m_resident.m_graphs.push_back(graphInfo(graphp));
            AstCStmt* const pointp = new AstCStmt{callStmtp->fileline()};
            callStmtp->replaceWith(pointp);
            pointp->add(callStmtp);
            m_reg.m_graphPoints.emplace(pointp, std::make_pair(graph, label++));
            m_reg.m_graphPointPcs.emplace(pointp, pcp);
        }
        std::vector<AstCReturn*> returns;
        funcp->foreach([&](AstCReturn* returnp) { returns.push_back(returnp); });
        for (AstCReturn* const returnp : returns) {
            AstCStmt* const stmtp = stmt(returnp->fileline());
            stmtp->add("{\n");
            stmtp->add(ref(pcp, VAccess::WRITE));
            stmtp->add(" = 0U;\nreturn ");
            if (AstNodeExpr* const lhsp = returnp->lhsp()) stmtp->add(lhsp->unlinkFrBack());
            stmtp->add(";\n}\n");
            returnp->replaceWith(stmtp);
            VL_DO_DANGLING(returnp->deleteTree(), returnp);
        }
        AstCStmt* const prologuep = stmt(flp);
        prologuep->add("switch (");
        prologuep->add(ref(pcp));
        prologuep->add(") {\ncase 0:;\n");
        AstCStmt* const epiloguep = stmt(flp);
        epiloguep->add("}\n");
        epiloguep->add(ref(pcp, VAccess::WRITE));
        epiloguep->add(" = 0U;\n");
        if (funcp->rtnTypeVoid() != "void") epiloguep->add("return 0;\n");
        AstNode* const stmtsp
            = funcp->stmtsp() ? funcp->stmtsp()->unlinkFrBackWithNext() : nullptr;
        funcp->addStmtsp(prologuep);
        if (stmtsp) funcp->addStmtsp(VN_AS(stmtsp, NodeStmt));
        funcp->addStmtsp(epiloguep);
    }

public:
    explicit GpuResidentPrepare(AstNetlist* netlistp)
        : m_netlistp{netlistp} {
        m_modp = netlistp->topModulep();
        for (AstNode* nodep = m_modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (AstCFunc* const funcp = VN_CAST(nodep, CFunc)) m_funcs[funcp->name()] = funcp;
        }
        V3GpuResident& r = m_reg.m_resident;
        const auto find = [&](const char* namep) -> AstCFunc* {
            const auto it = m_funcs.find(namep);
            return it == m_funcs.end() ? nullptr : it->second;
        };
        r.m_icop = find("_eval_ico");
        r.m_actp = find("_eval_act");
        r.m_inactp = find("_eval_inact");
        r.m_nbap = find("_eval_nba");
        r.m_obsp = find("_eval_obs");
        r.m_reactp = find("_eval_react");
        r.m_samplep = find("_eval_sample");
        r.m_postponedp = find("_eval_postponed");
        UASSERT_OBJ(r.m_actp && r.m_nbap, m_modp,
                    "GPU-resident mode: scheduler regions not found");
        r.m_suspp = newMember("__Vgpu_susp");
        std::map<AstCFunc*, std::vector<std::pair<AstNode*, AstExecGraph*>>> byRegion;
        std::vector<AstExecGraph*> graphs;
        netlistp->foreach([&](AstExecGraph* graphp) { graphs.push_back(graphp); });
        for (AstExecGraph* const graphp : graphs) {
            AstCFunc* const ownerp = const_cast<AstCFunc*>(enclosingCFunc(graphp));
            UASSERT_OBJ(
                ownerp && ownerp->stmtsp() == graphp && !graphp->nextp() && !ownerp->argsp(),
                graphp, "GPU-resident mode: multithreaded graph mixed with other statements");
            m_reg.m_graphFuncs.insert(ownerp);
            std::vector<AstNodeCCall*> calls;
            netlistp->foreach([&](AstNodeCCall* callp) {
                if (callp->funcp() == ownerp) calls.push_back(callp);
            });
            for (AstNodeCCall* const callp : calls) {
                AstCFunc* const regionp = const_cast<AstCFunc*>(enclosingCFunc(callp));
                AstStmtExpr* const stmtp = VN_CAST(callp->backp(), StmtExpr);
                UASSERT_OBJ(regionp && isRegion(regionp) && stmtp, callp,
                            "GPU-resident mode: multithreaded graph called outside a region");
                byRegion[regionp].emplace_back(stmtp, graphp);
            }
        }
        for (auto& it : byRegion) protothread(it.first, it.second);
        m_reg.m_residentMode = true;
        m_reg.m_resident.m_enabled = true;
        V3Stats::addStat("GPU, resident graphs", m_reg.m_resident.m_graphs.size());
    }
};

class GpuResidentPartition final {
    GpuRegistry& m_reg = registry();  // GPU state of this Verilation

    bool capable(const AstCFunc* funcp, std::string& why) const {
        if (funcp->isCoroutine())
            why = "coroutine";
        else if (funcp->needsVlProcess())
            why = "process";
        else if (funcp->dpiImportWrapper() || funcp->dpiImportPrototype())
            why = "host DPI " + V3Gpu::dpiName(funcp);
        else if (funcp->dpiExportImpl())
            why = "DPI export";
        else if (funcp->isConstructor() || funcp->isDestructor())
            why = "constructor";
        else if (funcp->isVirtual())
            why = "virtual";
        else if (!funcp->ifdef().empty())
            why = "ifdef " + funcp->ifdef();
        else if (!funcp->isLoose() && !funcp->isStatic())
            why = "class method";
        else {
            const auto it = m_reg.m_hostFuncs.find(funcp);
            if (it != m_reg.m_hostFuncs.end() && !it->second.empty()) why = it->second;
        }
        return why.empty();
    }

public:
    explicit GpuResidentPartition(AstNetlist* netlistp) {
        AstNodeModule* const modp = netlistp->topModulep();
        m_reg.m_modp = modp;
        for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstVar* const varp = VN_CAST(nodep, Var)) m_reg.m_members.insert(varp);
        }
        const V3GpuResident& r = m_reg.m_resident;
        std::vector<AstCFunc*> work;
        const auto add = [&](AstCFunc* funcp) {
            if (funcp && m_reg.m_graphFuncs.count(funcp)) return;
            if (funcp && m_reg.m_deviceSet.insert(funcp).second) {
                m_reg.m_deviceFuncs.push_back(funcp);
                work.push_back(funcp);
            }
        };
        for (AstCFunc* const funcp :
             {r.m_icop, r.m_actp, r.m_inactp, r.m_nbap, r.m_obsp, r.m_reactp, r.m_samplep,
              r.m_postponedp, V3Gpu::timingNextTimeFuncp()}) {
            add(funcp);
        }
        for (const V3GpuResidentGraph& graph : r.m_graphs) {
            for (const std::vector<AstCFunc*>& level : graph.m_levels) {
                for (AstCFunc* const funcp : level) add(funcp);
            }
        }
        while (!work.empty()) {
            AstCFunc* const funcp = work.back();
            work.pop_back();
            funcp->foreach([&](AstNodeCCall* callp) {
                AstCFunc* const calleep = callp->funcp();
                if (V3Gpu::isGpuDpi(calleep)) return;
                if (calleep->ifdef() == "VL_DEBUG") return;
                if (const AstNode* const upp = callp->backp()) {
                    if (VN_IS(upp, ExecGraph)) return;
                }
                add(calleep);
            });
        }
        int errors = 0;
        for (AstCFunc* const funcp : m_reg.m_deviceFuncs) {
            std::string why;
            if (capable(funcp, why)) continue;
            if (errors++ < 20) {
                funcp->v3warn(E_UNSUPPORTED,
                              "Unsupported: GPU-resident mode: " << funcp->name() << ": " << why);
            }
        }
        for (AstCFunc* const funcp : m_reg.m_deviceFuncs) {
            funcp->foreach([this](AstNode* nodep) {
                if (isDeferredStmt(nodep)) makeResidentReplay(nodep);
            });
        }
        V3Stats::addStat("GPU, device functions", m_reg.m_deviceFuncs.size());
        V3Stats::addStat("GPU, deferred statements", m_reg.m_replays.size());
    }
    void makeResidentReplay(AstNode* stmtp) { gpuMakeReplay(stmtp, m_reg.m_modp); }
};

}  // namespace

void V3Gpu::residentPrepare(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { GpuResidentPrepare{nodep}; }
    V3Global::dumpCheckGlobalTree("gpu-resident", 0, dumpTreeEitherLevel() >= 3);
}

void V3Gpu::residentPartition(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    const EmitCParentModule emitCParentModule;
    GpuResidentPartition{nodep};
}

bool V3Gpu::residentMode() { return registry().m_residentMode; }
const V3GpuResident& V3Gpu::resident() { return registry().m_resident; }

bool V3Gpu::isResidentGraphPoint(const AstNode* nodep, int& graph, int& label) {
    const auto it = registry().m_graphPoints.find(nodep);
    if (it == registry().m_graphPoints.end()) return false;
    graph = it->second.first;
    label = it->second.second;
    return true;
}

namespace {
std::string gpuTextOnly(const AstNode* nodesp, bool& ok) {
    std::string text;
    ok = true;
    for (const AstNode* itemp = nodesp; itemp; itemp = itemp->nextp()) {
        const AstText* const textp = VN_CAST(itemp, Text);
        if (!textp) {
            ok = false;
            return "";
        }
        text += textp->text();
    }
    return text;
}
}  // namespace

std::string V3Gpu::deviceCExprText(const AstNode* nodep) {
    const std::string assertText = gpuAssertCtlText(nodep);
    if (!assertText.empty()) return assertText;
    const AstCExpr* const exprp = VN_CAST(nodep, CExpr);
    if (!exprp) return "";
    bool ok = false;
    const std::string text = gpuTextOnly(exprp->nodesp(), ok);
    if (!ok) return "";
    if (isTimingNowExpr(nodep)) return "@@VLGPU_NOW@@";
    if (isTimingFinishExpr(nodep)) return "@@VLGPU_FINISH@@";
    std::string result = text;
    const auto replaceAll = [&](const std::string& from, const std::string& to) {
        for (size_t pos = result.find(from); pos != std::string::npos;
             pos = result.find(from, pos + to.size())) {
            result.replace(pos, from.size(), to);
        }
    };
    replaceAll("vlSymsp->_vm_contextp__->gotFinish()", "@@VLGPU_FINISH@@");
    replaceAll("vlSymsp->_vm_contextp__->debug()", "false");
    replaceAll("vlSymsp->_vm_contextp__->time()", "@@VLGPU_NOW@@");
    replaceAll("vlSymsp->__Vm_didInit", "true");
    if (result.find("vlSymsp") != std::string::npos || result.find("vlSelf") != std::string::npos
        || result.find("this->") != std::string::npos) {
        return "";
    }
    return result;
}

std::string V3Gpu::deviceCStmtText(const AstNode* nodep, bool& known) {
    known = false;
    const AstCStmt* const stmtp = VN_CAST(nodep, CStmt);
    if (!stmtp) return "";
    const AstText* const firstp = VN_CAST(stmtp->nodesp(), Text);
    if (firstp && firstp->text().rfind("#ifdef VL_DEBUG", 0) == 0) {
        known = true;
        return "";
    }
    bool ok = false;
    const std::string text = gpuTextOnly(stmtp->nodesp(), ok);
    if (!ok) return "";
    if (isGpuNoopStmt(nodep)) {
        known = true;
        return "";
    }
    if (text.rfind("#ifdef VL_DEBUG", 0) == 0 || text.rfind("#endif", 0) == 0) {
        known = true;
        return text;
    }
    if (text.rfind("VL_"
                   "FATAL_MT(",
                   0)
        == 0) {
        known = true;
        std::vector<std::string> lits;
        bool inStr = false;
        std::string cur;
        for (size_t i = 0; i < text.size(); ++i) {
            const char c = text[i];
            if (!inStr) {
                if (c == '"') {
                    inStr = true;
                    cur.clear();
                }
            } else if (c == '\\' && i + 1 < text.size()) {
                cur += text[++i];
            } else if (c == '"') {
                inStr = false;
                lits.push_back(cur);
            } else {
                cur += c;
            }
        }
        std::string msg = lits.empty() ? std::string{"fatal error"} : lits.back();
        const size_t open = text.find('(');
        if (lits.size() >= 3 && open + 1 < text.size() && text[open + 1] == '"') {
            const size_t comma = text.find(',', open + 2 + lits.front().size());
            const size_t comma2 = comma == std::string::npos ? comma : text.find(',', comma + 1);
            std::string line;
            if (comma2 != std::string::npos) line = text.substr(comma + 1, comma2 - comma - 1);
            line.erase(0, line.find_first_not_of(' '));
            msg = lits.front() + ":" + line + ": " + msg;
        }
        std::vector<std::string>& msgs = registry().m_fatalMsgs;
        size_t idx = 0;
        while (idx < msgs.size() && msgs[idx] != msg) ++idx;
        if (idx == msgs.size()) msgs.push_back(msg);
        return "@@VLGPU_FATAL@@" + std::to_string(idx + 1) + "@@";
    }
    return "";
}

const std::vector<std::string>& V3Gpu::fatalMessages() { return registry().m_fatalMsgs; }

AstVar* V3Gpu::residentGraphPc(const AstNode* nodep) {
    const auto it = registry().m_graphPointPcs.find(nodep);
    return it == registry().m_graphPointPcs.end() ? nullptr : it->second;
}

bool V3Gpu::isResidentStmt(const AstNode* nodep) {
    return registry().m_residentStmts.count(nodep) > 0;
}
