// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Lower timing processes to resumable GPU step functions
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
#include "V3Stats.h"

#include <map>
#include <unordered_set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

struct GpuTimingState final {
    bool m_lowered = false;  // Timing was lowered for the GPU
    AstCFunc* m_eventsPendingp = nullptr;  // Lowered eventsPending()
    AstCFunc* m_nextTimeSlotp = nullptr;  // Lowered nextTimeSlot()
    std::unordered_set<const AstNode*> m_nowExprs;
    std::unordered_set<const AstNode*> m_finishExprs;
    std::unordered_set<const AstNode*> m_deviceStmts;
    std::unordered_set<const AstNode*> m_deviceExprs;
    std::vector<AstVar*> m_slotPcs;  // Resume point of every process slot
    AstVar* m_overflowp = nullptr;  // Set when a process ran out of fork slots
    AstVar* m_finishp = nullptr;  // Set by $finish, $stop or a fatal error
    AstVar* m_fatalp = nullptr;  // Index of the fatal error message, 0 for none
    AstVar* m_tbasep = nullptr;  // Time base of the copy, for refilled slots
    AstCFunc* m_nextTimep = nullptr;  // Earliest wake-up time of all slots
};

GpuTimingState& timingState() {
    static GpuTimingState s_state;
    return s_state;
}

class GpuTimingLower final {
    struct Slot final {
        AstVar* m_pcp = nullptr;  // Resume point, 0 when idle
        AstVar* m_wakep = nullptr;  // Time at which it resumes
        AstVar* m_seqp = nullptr;  // Order of wake-ups at the same time
        AstVar* m_zerop = nullptr;  // Waiting on a zero delay
        AstCFunc* m_stepp = nullptr;  // Function that runs it to the next delay
        int m_index = 0;  // Slot number within its process
    };
    struct Proc final {
        AstCFunc* m_origp = nullptr;  // Original coroutine function
        std::vector<AstNodeCCall*> m_sites;  // Calls that start it
        std::vector<Slot> m_slots;  // Its slots
        AstCFunc* m_spawnp = nullptr;  // Function that starts it in a free slot
    };

    GpuTimingState& m_state = timingState();
    AstNetlist* const m_netlistp;
    AstNodeModule* m_modp = nullptr;
    AstVar* m_schedp = nullptr;
    AstVar* m_gseqp = nullptr;
    AstVar* m_activep = nullptr;

    template <typename T_Node>
    void addActive(T_Node* nodep, const Slot* slotp) {
        if (m_activep) {
            nodep->add("((");
            nodep->add(ref(m_activep));
            nodep->add(" >> " + std::to_string(slotp->m_index) + ") & 1ULL)");
        } else {
            nodep->add("(");
            nodep->add(ref(slotp->m_pcp));
            nodep->add(" != 0U)");
        }
    }
    template <typename T_Node>
    void setActive(T_Node* nodep, const Slot* slotp, bool on) {
        if (!m_activep) return;
        nodep->add(ref(m_activep, VAccess::READWRITE));
        nodep->add(std::string{on ? " |= " : " &= ~"} + "(1ULL << "
                   + std::to_string(slotp->m_index) + ");\n");
    }
    std::vector<Proc> m_procs;
    std::vector<Slot*> m_slots;
    std::string m_whyNot;
    const AstNode* m_whyNotp = nullptr;
    const int m_forkSlots;

    void unsupported(const AstNode* nodep, const std::string& why) {
        if (m_whyNot.empty()) {
            m_whyNot = why;
            m_whyNotp = nodep;
        }
    }

    static const AstCFunc* enclosingFunc(const AstNode* nodep) {
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

    bool isSchedRef(const AstNode* nodep) const {
        const AstVarRef* const refp = VN_CAST(nodep, VarRef);
        return refp && refp->varp() == m_schedp;
    }

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

    AstVar* newMember(const std::string& name, AstNodeDType* dtypep) {
        AstVar* const varp = new AstVar{m_modp->fileline(), VVarType::MODULETEMP, name, dtypep};
        addMember(varp);
        return varp;
    }

    AstVarRef* ref(AstVar* varp, VAccess access = VAccess::READ) const {
        AstVarRef* const refp = new AstVarRef{varp->fileline(), varp, access};
        refp->selfPointer(VSelfPointerText{VSelfPointerText::This{}});
        return refp;
    }

    AstCExpr* nowExpr(FileLine* flp) {
        AstCExpr* const exprp = new AstCExpr{flp, "vlSymsp->_vm_contextp__->time()", 64};
        m_state.m_nowExprs.insert(exprp);
        return exprp;
    }
    AstCExpr* finishExpr(FileLine* flp) {
        AstCExpr* const exprp = new AstCExpr{flp, "vlSymsp->_vm_contextp__->gotFinish()", 1};
        m_state.m_finishExprs.insert(exprp);
        return exprp;
    }
    AstCStmt* deviceStmt(FileLine* flp) {
        AstCStmt* const stmtp = new AstCStmt{flp};
        m_state.m_deviceStmts.insert(stmtp);
        return stmtp;
    }

    void check() {
        m_netlistp->foreach([&](AstVar* varp) {
            const AstBasicDType* const bdtp = VN_CAST(varp->dtypeSkipRefp(), BasicDType);
            if (!bdtp) return;
            if (bdtp->isDelayScheduler()) {
                if (m_schedp && m_schedp != varp) unsupported(varp, "multiple delay schedulers");
                m_schedp = varp;
            }
        });
        m_netlistp->foreach([&](const AstVarRef* refp) {
            const AstBasicDType* const bdtp = VN_CAST(refp->varp()->dtypeSkipRefp(), BasicDType);
            if (!bdtp) return;
            if (bdtp->isTriggerScheduler() || bdtp->isDynamicTriggerScheduler())
                unsupported(refp, "event control (@) in a process");
            if (bdtp->isForkSync()) unsupported(refp, "fork/join");
            if (bdtp->isProcessRef()) unsupported(refp, "process control");
            if (bdtp->isEvent()) unsupported(refp, "named events");
        });
        m_netlistp->foreach([&](AstCFunc* funcp) {
            if (!funcp->isCoroutine()) return;
            if (funcp->argsp()) unsupported(funcp, "task with timing called with arguments");
            if (funcp->needsVlProcess()) unsupported(funcp, "process control");
            m_procs.push_back(Proc{funcp, {}, {}, nullptr});
        });
        std::map<const AstCFunc*, Proc*> procOf;
        for (Proc& proc : m_procs) procOf.emplace(proc.m_origp, &proc);
        m_netlistp->foreach([&](AstNodeCCall* callp) {
            const auto it = procOf.find(callp->funcp());
            if (it == procOf.end()) return;
            if (!VN_IS(callp->backp(), StmtExpr))
                unsupported(callp, "awaiting a task with timing");
            it->second->m_sites.push_back(callp);
        });
        m_netlistp->foreach([&](AstCAwait* awaitp) {
            const AstCMethodHard* const methodp = VN_CAST(awaitp->exprp(), CMethodHard);
            if (!methodp || methodp->method() != VCMethod::SCHED_DELAY
                || !isSchedRef(methodp->fromp())) {
                unsupported(awaitp, "timing control other than a delay");
            }
        });
        m_netlistp->foreach([&](AstCMethodHard* methodp) {
            if (!isSchedRef(methodp->fromp())) return;
            switch (methodp->method()) {
            case VCMethod::SCHED_DELAY:
                if (!VN_IS(methodp->backp(), CAwait)) unsupported(methodp, "delay outside await");
                break;
            case VCMethod::SCHED_AWAITING_CURRENT_TIME:
            case VCMethod::SCHED_AWAITING_ZERO_DELAY: break;
            case VCMethod::SCHED_RESUME:
            case VCMethod::SCHED_RESUME_ZERO_DELAY:
                if (!VN_IS(methodp->backp(), StmtExpr))
                    unsupported(methodp, "scheduler resume in expression");
                break;
            default:
                unsupported(methodp, std::string{"delay scheduler "} + methodp->method().ascii());
            }
        });
        m_netlistp->foreach([&](const AstVarRef* refp) {
            if (refp->varp() != m_schedp) return;
            if (const AstNodeAssign* const assignp = VN_CAST(refp->backp(), NodeAssign)) {
                if (assignp->lhsp() == refp) return;
            }
            if (!VN_IS(refp->backp(), CMethodHard))
                unsupported(refp, std::string{"delay scheduler reference in "}
                                      + refp->backp()->typeName());
        });
    }

    void makeSlot(Proc& proc, int pid, int s) {
        Slot slot;
        slot.m_index = static_cast<int>(m_state.m_slotPcs.size());
        const std::string base = "__Vgpu_proc" + std::to_string(pid) + "_" + std::to_string(s);
        AstNodeDType* const u32p = m_netlistp->findUInt32DType();
        AstNodeDType* const u64p = m_netlistp->findUInt64DType();
        slot.m_pcp = newMember(base + "_pc", u32p);
        slot.m_wakep = newMember(base + "_wake", u64p);
        slot.m_seqp = newMember(base + "_seq", u64p);
        slot.m_zerop = newMember(base + "_zero", u32p);
        AstCFunc* const stepp = proc.m_origp->cloneTree(false);
        stepp->name(proc.m_origp->name() + "__Vgpu_step" + std::to_string(s));
        stepp->rtnType("");
        stepp->slow(false);
        std::vector<AstVar*> locals;
        stepp->foreach([&](AstVar* varp) { locals.push_back(varp); });
        std::unordered_set<const AstVar*> localSet{locals.begin(), locals.end()};
        stepp->foreach([&](AstVarRef* refp) {
            if (localSet.count(refp->varp())) {
                refp->selfPointer(VSelfPointerText{VSelfPointerText::This{}});
            }
        });
        for (AstVar* const varp : locals) {
            varp->unlinkFrBack();
            varp->name(base + "__" + varp->name());
            varp->funcLocal(false);
            varp->varType(VVarType::MODULETEMP);
            varp->lifetime(VLifetime::STATIC_EXPLICIT);
            addMember(varp);
        }
        FileLine* const flp = stepp->fileline();
        int next = 2;
        std::vector<AstCAwait*> awaits;
        stepp->foreach([&](AstCAwait* awaitp) { awaits.push_back(awaitp); });
        for (AstCAwait* const awaitp : awaits) {
            AstCMethodHard* const methodp = VN_AS(awaitp->exprp(), CMethodHard);
            AstNodeExpr* const delayp = methodp->pinsp()->unlinkFrBack();
            const int k = next++;
            AstCStmt* const stmtp = deviceStmt(awaitp->fileline());
            stmtp->add("{\nconst uint64_t __Vgpu_d = ");
            stmtp->add(delayp);
            stmtp->add(";\nif (__Vgpu_d == 0) {\n");
            stmtp->add(ref(slot.m_zerop, VAccess::WRITE));
            stmtp->add(" = 1U;\n} else {\n");
            stmtp->add(ref(slot.m_zerop, VAccess::WRITE));
            stmtp->add(" = 0U;\n");
            stmtp->add(ref(slot.m_wakep, VAccess::WRITE));
            stmtp->add(" = ");
            stmtp->add(nowExpr(flp));
            stmtp->add(" + (__Vgpu_d == ~0ULL ? 0ULL : __Vgpu_d);\n}\n");
            stmtp->add(ref(slot.m_seqp, VAccess::WRITE));
            stmtp->add(" = ");
            stmtp->add(ref(m_gseqp, VAccess::READWRITE));
            stmtp->add("++;\n");
            stmtp->add(ref(slot.m_pcp, VAccess::WRITE));
            stmtp->add(" = " + std::to_string(k) + "U;\nreturn;\n}\ncase " + std::to_string(k)
                       + ":;\n");
            awaitp->replaceWith(stmtp);
            VL_DO_DANGLING(awaitp->deleteTree(), awaitp);
        }
        std::vector<AstCReturn*> returns;
        stepp->foreach([&](AstCReturn* returnp) { returns.push_back(returnp); });
        for (AstCReturn* const returnp : returns) {
            AstCStmt* const stmtp = deviceStmt(returnp->fileline());
            stmtp->add(ref(slot.m_pcp, VAccess::WRITE));
            stmtp->add(" = 0U;\n");
            setActive(stmtp, &slot, false);
            stmtp->add("return;\n");
            returnp->replaceWith(stmtp);
            VL_DO_DANGLING(returnp->deleteTree(), returnp);
        }
        AstCStmt* const prologuep = deviceStmt(flp);
        prologuep->add("switch (");
        prologuep->add(ref(slot.m_pcp));
        prologuep->add(") {\ndefault: return;\ncase 1:;\n");
        AstCStmt* const epiloguep = deviceStmt(flp);
        epiloguep->add("}\n");
        epiloguep->add(ref(slot.m_pcp, VAccess::WRITE));
        epiloguep->add(" = 0U;\n");
        setActive(epiloguep, &slot, false);
        AstNode* const stmtsp
            = stepp->stmtsp() ? stepp->stmtsp()->unlinkFrBackWithNext() : nullptr;
        stepp->addStmtsp(prologuep);
        if (stmtsp) stepp->addStmtsp(VN_AS(stmtsp, NodeStmt));
        stepp->addStmtsp(epiloguep);
        m_modp->addStmtsp(stepp);
        slot.m_stepp = stepp;
        proc.m_slots.push_back(slot);
        m_state.m_slotPcs.push_back(slot.m_pcp);
    }

    AstCFunc* newFunc(FileLine* flp, const std::string& name) {
        AstCFunc* const funcp = new AstCFunc{flp, name, m_procs.front().m_origp->scopep()};
        funcp->isLoose(true);
        funcp->isConst(false);
        funcp->declPrivate(true);
        funcp->dontCombine(true);
        m_modp->addStmtsp(funcp);
        return funcp;
    }

    AstCCall* call(FileLine* flp, AstCFunc* funcp) {
        AstCCall* const callp = new AstCCall{flp, funcp};
        callp->dtypeSetVoid();
        callp->selfPointer(VSelfPointerText{VSelfPointerText::This{}});
        return callp;
    }

    void makeSpawn(Proc& proc, int pid) {
        FileLine* const flp = proc.m_origp->fileline();
        AstCFunc* const spawnp = newFunc(flp, "__Vgpu_spawn" + std::to_string(pid));
        AstCStmt* const stmtp = deviceStmt(flp);
        for (const Slot& slot : proc.m_slots) {
            stmtp->add("if (");
            stmtp->add(ref(slot.m_pcp));
            stmtp->add(" == 0U) {\n");
            stmtp->add(ref(slot.m_pcp, VAccess::WRITE));
            stmtp->add(" = 1U;\n");
            setActive(stmtp, &slot, true);
            stmtp->add(call(flp, slot.m_stepp));
            stmtp->add(";\n} else ");
        }
        stmtp->add("{\n");
        stmtp->add(ref(m_state.m_overflowp, VAccess::WRITE));
        stmtp->add(" = 1U;\n}\n");
        spawnp->addStmtsp(stmtp);
        proc.m_spawnp = spawnp;
        for (AstNodeCCall* const sitep : proc.m_sites) {
            AstCCall* const newp = call(sitep->fileline(), spawnp);
            sitep->replaceWith(newp);
            VL_DO_DANGLING(sitep->deleteTree(), sitep);
        }
    }

    AstCExpr* awaitingExpr(FileLine* flp, bool zero) {
        AstCExpr* const exprp = new AstCExpr{flp, "", 1};
        m_state.m_deviceExprs.insert(exprp);
        exprp->add("(!");
        exprp->add(finishExpr(flp));
        exprp->add(" && (false");
        for (const Slot* const slotp : m_slots) {
            exprp->add(" || (");
            addActive(exprp, slotp);
            exprp->add(" && ");
            exprp->add(ref(slotp->m_zerop));
            if (zero) {
                exprp->add(" != 0U)");
            } else {
                exprp->add(" == 0U && ");
                exprp->add(ref(slotp->m_wakep));
                exprp->add(" <= ");
                exprp->add(nowExpr(flp));
                exprp->add(")");
            }
        }
        exprp->add("))");
        return exprp;
    }

    AstCStmt* resumeStmt(FileLine* flp, bool zero) {
        AstCStmt* const stmtp = deviceStmt(flp);
        stmtp->add("if (");
        stmtp->add(finishExpr(flp));
        stmtp->add(") {\n");
        for (const Slot* const slotp : m_slots) {
            stmtp->add(ref(slotp->m_pcp, VAccess::WRITE));
            stmtp->add(" = 0U;\n");
        }
        if (m_activep) {
            stmtp->add(ref(m_activep, VAccess::WRITE));
            stmtp->add(" = 0ULL;\n");
        }
        stmtp->add("} else {\n");
        if (zero) {
            stmtp->add("uint8_t __Vgpu_snap[" + std::to_string(m_slots.size()) + "];\n");
            for (size_t i = 0; i < m_slots.size(); ++i) {
                stmtp->add("__Vgpu_snap[" + std::to_string(i) + "] = ");
                addActive(stmtp, m_slots[i]);
                stmtp->add(" && ");
                stmtp->add(ref(m_slots[i]->m_zerop));
                stmtp->add(" != 0U;\n");
            }
        }
        stmtp->add("for (;;) {\nint __Vgpu_b = -1;\nuint64_t __Vgpu_s = 0;\n");
        for (size_t i = 0; i < m_slots.size(); ++i) {
            const Slot* const slotp = m_slots[i];
            stmtp->add("if (");
            if (zero) {
                stmtp->add("__Vgpu_snap[" + std::to_string(i) + "]");
            } else {
                addActive(stmtp, slotp);
                stmtp->add(" && ");
                stmtp->add(ref(slotp->m_zerop));
                stmtp->add(" == 0U && ");
                stmtp->add(ref(slotp->m_wakep));
                stmtp->add(" == ");
                stmtp->add(nowExpr(flp));
            }
            stmtp->add(" && (__Vgpu_b < 0 || ");
            stmtp->add(ref(slotp->m_seqp));
            stmtp->add(" < __Vgpu_s)) {\n__Vgpu_b = " + std::to_string(i) + ";\n__Vgpu_s = ");
            stmtp->add(ref(slotp->m_seqp));
            stmtp->add(";\n}\n");
        }
        stmtp->add("if (__Vgpu_b < 0) break;\nswitch (__Vgpu_b) {\n");
        for (size_t i = 0; i < m_slots.size(); ++i) {
            stmtp->add("case " + std::to_string(i) + ":\n");
            if (zero) {
                stmtp->add("__Vgpu_snap[" + std::to_string(i) + "] = 0;\n");
                stmtp->add(ref(m_slots[i]->m_zerop, VAccess::WRITE));
                stmtp->add(" = 0U;\n");
            }
            stmtp->add(call(flp, m_slots[i]->m_stepp));
            stmtp->add(";\nbreak;\n");
        }
        stmtp->add("default: break;\n}\n}\n}\n");
        return stmtp;
    }

    void replaceSchedCalls() {
        std::vector<AstCMethodHard*> methods;
        m_netlistp->foreach([&](AstCMethodHard* methodp) {
            if (isSchedRef(methodp->fromp())) methods.push_back(methodp);
        });
        for (AstCMethodHard* const methodp : methods) {
            FileLine* const flp = methodp->fileline();
            switch (methodp->method()) {
            case VCMethod::SCHED_AWAITING_CURRENT_TIME:
            case VCMethod::SCHED_AWAITING_ZERO_DELAY: {
                const bool zero = methodp->method() == VCMethod::SCHED_AWAITING_ZERO_DELAY;
                AstCExpr* const newp = awaitingExpr(flp, zero);
                newp->dtypeFrom(methodp);
                methodp->replaceWith(newp);
                VL_DO_DANGLING(methodp->deleteTree(), methodp);
                break;
            }
            case VCMethod::SCHED_RESUME:
            case VCMethod::SCHED_RESUME_ZERO_DELAY: {
                const bool zero = methodp->method() == VCMethod::SCHED_RESUME_ZERO_DELAY;
                AstNode* const stmtp = methodp->backp();
                stmtp->replaceWith(resumeStmt(flp, zero));
                VL_DO_DANGLING(stmtp->deleteTree(), stmtp);
                break;
            }
            default: break;
            }
        }
    }

    void makeModelQueries() {
        FileLine* const flp = m_modp->fileline();
        AstCFunc* const pendingp = newFunc(flp, "__Vgpu_eventsPending");
        pendingp->rtnType("bool");
        pendingp->slow(true);
        AstCStmt* const pstmtp = new AstCStmt{flp};
        pstmtp->add("return !");
        pstmtp->add(finishExpr(flp));
        pstmtp->add(" && (false");
        for (const Slot* const slotp : m_slots) {
            pstmtp->add(" || ");
            addActive(pstmtp, slotp);
        }
        pstmtp->add(");\n");
        pendingp->addStmtsp(pstmtp);
        AstCFunc* const nextp = newFunc(flp, "__Vgpu_nextTimeSlot");
        nextp->rtnType("uint64_t");
        nextp->slow(true);
        AstCStmt* const nstmtp = new AstCStmt{flp};
        nstmtp->add("uint64_t __Vgpu_t = ~0ULL;\nbool __Vgpu_z = false;\n");
        for (const Slot* const slotp : m_slots) {
            nstmtp->add("if (");
            addActive(nstmtp, slotp);
            nstmtp->add(") {\nif (");
            nstmtp->add(ref(slotp->m_zerop));
            nstmtp->add(" != 0U) {\n__Vgpu_z = true;\n} else if (");
            nstmtp->add(ref(slotp->m_wakep));
            nstmtp->add(" < __Vgpu_t) {\n__Vgpu_t = ");
            nstmtp->add(ref(slotp->m_wakep));
            nstmtp->add(";\n}\n}\n");
        }
        nstmtp->add("if (__Vgpu_t != ~0ULL) return __Vgpu_t;\nif (__Vgpu_z) return ");
        nstmtp->add(nowExpr(flp));
        nstmtp->add(";\nVL_FATAL_MT(__FILE__, __LINE__, \"\", \"There is no next time slot "
                    "scheduled\");\nreturn 0;\n");
        nextp->addStmtsp(nstmtp);
        m_state.m_eventsPendingp = pendingp;
        m_state.m_nextTimeSlotp = nextp;
        AstCFunc* const devNextp = newFunc(flp, "__Vgpu_nextTime");
        devNextp->rtnType("uint64_t");
        AstCStmt* const dstmtp = deviceStmt(flp);
        dstmtp->add("uint64_t __Vgpu_t = ~0ULL;\n");
        for (const Slot* const slotp : m_slots) {
            dstmtp->add("if (");
            addActive(dstmtp, slotp);
            dstmtp->add(") {\nif (");
            dstmtp->add(ref(slotp->m_zerop));
            dstmtp->add(" != 0U) {\n__Vgpu_t = ");
            dstmtp->add(nowExpr(flp));
            dstmtp->add(";\n} else if (");
            dstmtp->add(ref(slotp->m_wakep));
            dstmtp->add(" < __Vgpu_t) {\n__Vgpu_t = ");
            dstmtp->add(ref(slotp->m_wakep));
            dstmtp->add(";\n}\n}\n");
        }
        dstmtp->add("return __Vgpu_t;\n");
        devNextp->addStmtsp(dstmtp);
        m_state.m_nextTimep = devNextp;
    }

public:
    GpuTimingLower(AstNetlist* netlistp, int forkSlots)
        : m_netlistp{netlistp}
        , m_forkSlots{forkSlots} {
        m_modp = netlistp->topModulep();
        check();
        if (!m_schedp || m_procs.empty()) {
            if (m_procs.empty() && m_schedp) unsupported(m_schedp, "scheduler without processes");
            if (!m_schedp) return;
        }
        if (!m_whyNot.empty()) return;
        m_gseqp = newMember("__Vgpu_seq", netlistp->findUInt64DType());
        m_state.m_overflowp = newMember("__Vgpu_forkOverflow", netlistp->findUInt32DType());
        m_state.m_finishp = newMember("__Vgpu_finish", netlistp->findUInt32DType());
        m_state.m_fatalp = newMember("__Vgpu_fatal", netlistp->findUInt32DType());
        m_state.m_tbasep = newMember("__Vgpu_tbase", netlistp->findUInt64DType());
        std::vector<int> slotCounts;
        int totalSlots = 0;
        for (size_t pid = 0; pid < m_procs.size(); ++pid) {
            bool slowOnly = true;
            for (const AstNodeCCall* const sitep : m_procs[pid].m_sites) {
                const AstCFunc* const ownerp = enclosingFunc(sitep);
                if (!ownerp
                    || (!ownerp->slow() && ownerp->name().rfind("_eval_initial", 0) != 0)) {
                    slowOnly = false;
                }
            }
            slotCounts.push_back(slowOnly ? 1 : m_forkSlots);
            totalSlots += slotCounts.back();
        }
        if (totalSlots <= 64) m_activep = newMember("__Vgpu_active", netlistp->findUInt64DType());
        for (size_t pid = 0; pid < m_procs.size(); ++pid) {
            Proc& proc = m_procs[pid];
            const int slots = slotCounts[pid];
            for (int s = 0; s < slots; ++s) makeSlot(proc, static_cast<int>(pid), s);
        }
        for (Proc& proc : m_procs) {
            for (Slot& slot : proc.m_slots) m_slots.push_back(&slot);
        }
        for (size_t pid = 0; pid < m_procs.size(); ++pid) {
            makeSpawn(m_procs[pid], static_cast<int>(pid));
        }
        replaceSchedCalls();
        makeModelQueries();
        for (Proc& proc : m_procs) {
            VL_DO_DANGLING(proc.m_origp->unlinkFrBack()->deleteTree(), proc.m_origp);
        }
        m_state.m_lowered = true;
        V3Stats::addStat("GPU, timing processes", m_procs.size());
        V3Stats::addStat("GPU, timing process slots", m_slots.size());
    }
    const std::string& whyNot() const { return m_whyNot; }
    const AstNode* whyNotp() const { return m_whyNotp; }
};

}  // namespace

bool V3Gpu::lowerTiming(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    GpuTimingLower lower{nodep, v3Global.opt.gpuForkSlots()};
    if (!lower.whyNot().empty()) {
        if (!v3Global.opt.gpuHybrid()) {
            lower.whyNotp()->v3warn(E_UNSUPPORTED,
                                    "Unsupported: GPU-resident mode: "
                                        << lower.whyNot() << "\n"
                                        << lower.whyNotp()->warnMore()
                                        << "... Use --gpu-hybrid to run it with CPU assistance");
        }
        return false;
    }
    V3Global::dumpCheckGlobalTree("gpu-timing", 0, dumpTreeEitherLevel() >= 3);
    return timingState().m_lowered;
}

bool V3Gpu::timingLowered() { return timingState().m_lowered; }
AstCFunc* V3Gpu::eventsPendingFuncp() { return timingState().m_eventsPendingp; }
AstCFunc* V3Gpu::nextTimeSlotFuncp() { return timingState().m_nextTimeSlotp; }
bool V3Gpu::isTimingNowExpr(const AstNode* nodep) { return timingState().m_nowExprs.count(nodep); }
bool V3Gpu::isTimingFinishExpr(const AstNode* nodep) {
    return timingState().m_finishExprs.count(nodep);
}
bool V3Gpu::isTimingDeviceStmt(const AstNode* nodep) {
    return timingState().m_deviceStmts.count(nodep) || timingState().m_deviceExprs.count(nodep);
}
AstVar* V3Gpu::timingFinishVarp() { return timingState().m_finishp; }
AstVar* V3Gpu::timingFatalVarp() { return timingState().m_fatalp; }
AstVar* V3Gpu::timingOverflowVarp() { return timingState().m_overflowp; }
AstVar* V3Gpu::timingTbaseVarp() { return timingState().m_tbasep; }
AstCFunc* V3Gpu::timingNextTimeFuncp() { return timingState().m_nextTimep; }
