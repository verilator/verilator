// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit RepCut kernels and state publication
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

// Materialize a validated partition plan while its AST bindings remain live.
// Native scheduling groups sinks by sensitivity domain and preserves each
// partition's data/control closure. Source lowering retains optimized expression
// trees and procedural branches; graph lowering handles exceptional cones inside
// the same kernel. Both paths produce ordinary Verilator AST and bounded helper
// functions. These helpers are sequential calls within a partition, not
// independent runtime tasks.
//
// Evaluation normally writes private candidates. Scalar values, memory write
// enables/addresses/data, and effect arguments must remain stable until their
// corresponding publication or replay. Native NBAs or dependency-visible POST
// dispatches publish state after evaluation; memory writes retain source order.
// The caller replays captured effects and foreign procedure bodies exactly once.
// Separate checks admit early scalar publication only where no remaining reader
// or observer needs the old value. Ownership alone does not establish that proof.
//
// Scheduling dependencies stay explicit even when the implementation is a CFunc
// call. Analysis-only arguments expose its model reads and writes to scheduling,
// tracing and optimization; removeDependencyArgs removes them after ExecGraph
// implementation. Eligible kernels are marked for later batching, when V3Sched
// has remapped sensitivities to native triggers. Batching must preserve each
// domain's guard and publication ordering rather than treating a union of clocks
// as permission to publish every domain's state.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3RepCutEmit.h"

#include "V3DfgContext.h"
#include "V3ExecGraph.h"
#include "V3File.h"
#include "V3InstrCount.h"
#include "V3MergeCond.h"
#include "V3RepCut.h"
#include "V3RepCutChunk.h"
#include "V3RepCutDecoder.h"
#include "V3RepCutNative.h"
#include "V3RepCutOptimize.h"
#include "V3RepCutProgram.h"
#include "V3RepCutShare.h"
#include "V3Stats.h"

#include <algorithm>
#include <array>
#include <fstream>
#include <iomanip>
#include <memory>
#include <sstream>
#include <unordered_map>
#include <unordered_set>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace V3RepCut {
namespace {
// RepCut emits partition code after V3Unknown, where master forbids four-state dtypes.
// Newly constructed nodes can default to four-state; normalize only RepCut-created
// functions (never the retained native netlist) to the two-state equivalent.
class RepCutTwoState final : public VNVisitor {
    void visit(AstNodeExpr* nodep) override {
        if (AstBasicDType* const bdtp = VN_CAST(nodep->dtypep(), BasicDType)) {
            if (bdtp->isFourstate()) {
                nodep->dtypep(v3Global.rootp()->findBitDType(
                    bdtp->width(), bdtp->width(),
                    bdtp->isSigned() ? VSigning::SIGNED : VSigning::UNSIGNED));
            }
        }
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit RepCutTwoState(AstNode* nodep) { iterate(nodep); }
    ~RepCutTwoState() override = default;
};

// An initializer cannot observe an edge if it consists only of immediate
// constants or a validated compiler-generated decoder-cache initialization.
// Prune accepted initializers so their private fill operation is not mistaken
// for an arbitrary effect elsewhere in the design.
class NativeStateObserverVisitor final : public VNVisitorConst {
    bool m_observer = false;

    void observer(AstNode* nodep) {
        UINFO(3, "RepCut state-release observer: " << nodep);
        if (debug() >= 9) nodep->dumpTree(std::cout);
        m_observer = true;
    }

    static bool constantInitialization(const AstNode* nodep) {
        for (; nodep; nodep = nodep->nextp()) {
            if (const AstAssign* const assignp = VN_CAST(nodep, Assign)) {
                if (!VN_IS(assignp->lhsp(), VarRef) || !VN_IS(assignp->rhsp(), Const)
                    || assignp->timingControlp()
                    || !assignp->lhsp()->dtypep()->skipRefp()->isIntegralOrPacked())
                    return false;
            } else if (const AstBegin* const beginp = VN_CAST(nodep, Begin)) {
                if (!constantInitialization(beginp->stmtsp())) return false;
            } else if (!VN_IS(nodep, Comment)) {
                return false;
            }
        }
        return true;
    }
    void visit(AstInitial* nodep) override {
        if (!constantInitialization(nodep->stmtsp())) observer(nodep);
    }
    void visit(AstInitialStatic* nodep) override {
        if (!constantInitialization(nodep->stmtsp()) && !isNativeDecoderInitialization(nodep))
            observer(nodep);
    }
    void visit(AstCFunc* nodep) override {
        // Elaborated-away modules can leave imports and internal wrappers
        // behind. These definitions cannot run by themselves. Calls from any
        // executable process are rejected separately; public entry points stay
        // forbidden even if they have no visible caller in this netlist.
        if (nodep->entryPoint() || nodep->funcPublic() || nodep->dpiExportImpl()
            || nodep->dpiExportDispatcher()) {
            observer(nodep);
        } else if (nodep->dpiImportWrapper()) {
            return;
        } else if (!nodep->dpiImportPrototype() || nodep->stmtsp() || nodep->varsp()) {
            observer(nodep);
        }
    }
    void visit(AstNode* nodep) override {
        if (m_observer) return;
        if (VN_IS(nodep, InitialAutomatic) || VN_IS(nodep, Final) || VN_IS(nodep, NodeCCall)
            || VN_IS(nodep, AddrOfCFunc) || VN_IS(nodep, AlwaysPost) || VN_IS(nodep, CStmt)
            || VN_IS(nodep, Display) || VN_IS(nodep, Stop) || VN_IS(nodep, Finish)
            || VN_IS(nodep, CoverInc)) {
            observer(nodep);
        } else if (AstNodeExpr* const exprp = VN_CAST(nodep, NodeExpr)) {
            if (!exprp->isPure())
                observer(nodep);
            else
                iterateChildrenConst(nodep);
        } else {
            iterateChildrenConst(nodep);
        }
    }

public:
    explicit NativeStateObserverVisitor(AstNetlist* nodep) { iterateConst(nodep); }
    bool hasObserver() const { return m_observer; }
};

// Eligible native kernels have only pure expressions, local blocking
// temporaries, and NBAs. Retain the original guards and local temporaries for
// coverage, while all state updates are supplied by the partition kernels.
// Coverage increments must execute once under native scheduling.
class NativeCoverageVisitor final : public VNVisitor {
    void visit(AstAssignDly* nodep) override { pushDeletep(nodep->unlinkFrBack()); }
    void visit(AstDisplay* nodep) override { pushDeletep(nodep->unlinkFrBack()); }
    void visit(AstStop* nodep) override { pushDeletep(nodep->unlinkFrBack()); }
    void visit(AstFinish* nodep) override { pushDeletep(nodep->unlinkFrBack()); }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit NativeCoverageVisitor(AstAlways* nodep) { iterate(nodep); }
};

// Native kernel bodies access model storage directly. Their arguments expose
// reads and writes to scheduling and optimization, but are never consumed by
// the callee. Retain them until all such passes (including ExecGraph) finish,
// then remove both sides of the call before C++ generation. Removing them
// earlier can hide a dependency or allow a live value to be localized.
class NativeDependencyVisitor final : public VNVisitor {
    std::vector<AstCFunc*> m_funcps;
    size_t m_operands = 0;  // Number of dependency operands removed from call interfaces

    void visit(AstCFunc* nodep) override {
        if (nodep->repcutDependencyArgs()) m_funcps.push_back(nodep);
        iterateChildren(nodep);
    }
    void visit(AstNodeCCall* nodep) override {
        if (nodep->funcp()->repcutDependencyArgs()) {
            for (AstNode* argp = nodep->argsp(); argp; argp = argp->nextp()) {
                UASSERT_OBJ(!argp->exists([](AstNode* exprp) { return !exprp->isPure(); }), argp,
                            "Side effect in native RepCut dependency operand");
                ++m_operands;
            }
            if (AstNodeExpr* const argsp = nodep->argsp())
                pushDeletep(argsp->unlinkFrBackWithNext());
            // A dependency-only scheduling marker has no runtime operation.
            // Keep it through ordering and ExecGraph, then erase the call.
            if (!nodep->funcp()->stmtsp() && !nodep->funcp()->varsp()) {
                AstStmtExpr* const stmtp = VN_AS(nodep->backp(), StmtExpr);
                pushDeletep(stmtp->unlinkFrBack());
                return;
            }
        }
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit NativeDependencyVisitor(AstNetlist* netlistp) {
        iterate(netlistp);
        // Keep callee markers and declarations intact while visiting all calls.
        for (AstCFunc* const funcp : m_funcps) {
            if (!funcp->stmtsp() && !funcp->varsp()) {
                pushDeletep(funcp->unlinkFrBack());
                continue;
            }
            if (AstNode* const argsp = funcp->argsp()) pushDeletep(argsp->unlinkFrBackWithNext());
            funcp->repcutDependencyArgs(false);
        }
        V3Stats::addStat("RepCut native, dependency wrappers lowered", m_funcps.size());
        V3Stats::addStat("RepCut native, dependency operands removed", m_operands);
    }
};

using StatementSizes = std::unordered_map<const AstNodeStmt*, size_t>;

// Cache subtree sizes after optimization, for one chunking operation only.
// No cached nodes are deleted during chunking. Retaining this cache across
// optimizations would let reused addresses inherit deleted nodes' sizes.
class StatementSizeVisitor final : public VNVisitorConst {
    StatementSizes& m_sizes;
    size_t m_count = 0;  // AST nodes counted in the current statement body
    void visit(AstNode* nodep) override {
        const size_t before = m_count++;
        iterateChildrenConst(nodep);
        if (const AstNodeStmt* const stmtp = VN_CAST(nodep, NodeStmt))
            m_sizes.emplace(stmtp, m_count - before);
    }

public:
    StatementSizeVisitor(StatementSizes& sizes, const std::vector<AstNodeStmt*>& statements)
        : m_sizes{sizes} {
        for (AstNodeStmt* const stmtp : statements) iterateConst(stmtp);
    }
};

// Optimization can introduce private temporaries after the original graph was
// lowered. All assignments in an evaluation block still belong to its partition.
class PrivateStorageVisitor final : public VNVisitor {
    const uint32_t m_group;
    void visit(AstVarRef* nodep) override {
        if (!nodep->access().isWriteOrRW()) return;
        AstVar* const varp = nodep->varp();
        UASSERT_OBJ(!varp->repcutStorageGroup() || varp->repcutStorageGroup() == m_group, varp,
                    "RepCut evaluation writes another partition's storage");
        varp->repcutStorageGroup(m_group);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    PrivateStorageVisitor(const std::vector<AstNodeStmt*>& statements, uint32_t group)
        : m_group{group} {
        for (AstNodeStmt* const stmtp : statements) iterate(stmtp);
    }
};

class Emitter final {
    AstNetlist* const m_netlistp;  // Design receiving the generated kernels
    const Graph& m_graph;  // Normalized graph used for partition emission
    const Bindings& m_bindings;  // Live AST bindings used to resolve graph identities
    std::unordered_set<const AstNodeModule*>
        m_sharedModules;  // Common layout for multiple instances
    AstScope* const m_scopep;  // Scope owning generated partition storage and functions
    FileLine* const m_flp;  // Source location assigned to generated scaffolding
    // A lower bound admits each atomic normalized assignment/store. This is an
    // AST construction budget; later wide lowering can expand individual nodes.
    const size_t m_limit
        = std::max(32, v3Global.opt.outputSplitCFuncs() ? v3Global.opt.outputSplitCFuncs()
                                                        : V3Options::REPCUT_DEFAULT_CFUNCS);
    std::vector<AstVarScope*> m_values;  // Materialized variable bindings indexed by graph node ID
    std::vector<AstNodeExpr*> m_expressions;  // Inline expressions indexed by graph node ID
    std::vector<size_t> m_uses;  // Operand use counts for canonical graph values
    std::vector<size_t> m_consumers;  // Consumer node ID used when a value has exactly one use
    std::vector<size_t>
        m_expressionSizes;  // Estimated AST expression sizes indexed by graph node ID
    std::vector<size_t> m_representatives;  // Original node ID to canonical shared representative
    std::vector<size_t> m_regionDepth;  // Nesting depth of each graph control region
    std::vector<bool>
        m_directUpdates;  // Sinks whose state update is already performed by a worker
    std::vector<Candidates> m_candidates;  // Captured publication slots indexed by sink ID
    std::vector<std::vector<AstVarScope*>>
        m_effectArguments;  // Captured effect argument storage indexed by sink ID
    std::vector<std::array<AstCFunc*, 2>> m_phases;
    std::map<size_t, AstVarScope*> m_nativeInputps;  // SystemC values captured before dispatch
    std::unique_ptr<std::ofstream> m_reportp;  // Optional report of emitted functions and chunks
    std::unique_ptr<std::ofstream>
        m_cutReportp;  // Optional report of chunk boundaries and live spans
    std::unique_ptr<std::ofstream>
        m_publicationReportp;  // Optional report of state publication decisions
    std::unique_ptr<std::ofstream>
        m_nativeCostReportp;  // Optional report of native statement costs
    size_t m_cutGroups = 0;  // Next chunk-plan report group index
    size_t m_functions = 0;  // Number of generated helper functions
    std::vector<AstCFunc*> m_createdFuncps;  // Functions created during emission
    size_t m_temporaries = 0;  // Number of generated temporary bindings
    size_t m_maxBody = 0;  // Largest generated function body in AST nodes
    size_t m_guardFunctions = 0;  // Number of functions created to bound guard bodies
    size_t m_inlined = 0;  // Number of graph expressions emitted inline
    size_t m_guards = 0;  // Number of emitted predicate guards
    size_t m_copies = 0;  // Number of emitted value-copy assignments
    uint32_t m_storageGroup = 0;  // Current partition's candidate/temporary region
    V3DfgContext m_dfgContext{"__VrepcutDfg"};  // Partition-local optimization context

    struct Frame final {
        size_t m_region;  // Control region represented by this emission frame
        AstIf* m_ifp;  // Conditional receiving statements in this frame
        bool m_taken;  // Branch polarity selected by this frame
    };

    size_t expressionLimit() const { return std::max<size_t>(2, (m_limit - 8) / 4); }
    static size_t statementSize(AstNodeStmt* stmtp, StatementSizes& sizes) {
        const auto it = sizes.find(stmtp);
        if (it != sizes.end()) return it->second;
        // Only fresh, shallow helper calls are created while this cache is live.
        return sizes.emplace(stmtp, stmtp->nodeCount()).first->second;
    }

    AstVarScope* storage(size_t id) const { return m_bindings.m_storageps.at(id); }
    AstVarScope* inputStorage(size_t id) const {
        const auto it = m_nativeInputps.find(id);
        return it != m_nativeInputps.end() ? it->second : storage(id);
    }
    AstVarRef* ref(AstVarScope* vscp, VAccess access = VAccess::READ) const {
        return new AstVarRef{m_flp, vscp, access};
    }
    AstVarScope* temp(const std::string& name, int width, bool sign) {
        AstVarScope* const vscp = v3Global.rootp()->topScopep()->createTemp(
            name,
            m_scopep->findBitDType(width, width, sign ? VSigning::SIGNED : VSigning::UNSIGNED));
        vscp->varp()->noReset(true);  // Every candidate is assigned before use.
        vscp->varp()->trace(false);
        vscp->varp()->isInternal(true);
        vscp->varp()->repcutStorageGroup(m_storageGroup);
        ++m_temporaries;
        return vscp;
    }
    AstConst* constant(const Vertex& vertex) const {
        // Construct from value words, never from the diagnostic label.
        std::ostringstream literal;
        literal << vertex.m_width << (vertex.m_signed ? "'sh" : "'h") << std::hex
                << std::setfill('0');
        for (auto it = vertex.m_words.rbegin(); it != vertex.m_words.rend(); ++it)
            literal << std::setw(8) << *it;
        const std::string text = literal.str();
        // The Verilog literal constructor yields a four-state number. RepCut emits after
        // V3Unknown, where master forbids four-state dtypes, so rebuild the same value bits as
        // a two-state number (extracted constants carry no X/Z).
        const V3Number literalNum{m_flp, V3Number::VerilogNumberLiteral{}, text.c_str()};
        V3Number number{m_flp, static_cast<int>(vertex.m_width), 0};
        number.opBitsOne(literalNum);
        number.isSigned(vertex.m_signed);
        return new AstConst{m_flp, number};
    }
    AstNodeExpr* operand(const Vertex& original) {
        const Vertex& vertex = *m_graph.m_vertexps[m_representatives[original.m_id]];
        if (vertex.m_kind == Op::CONSTANT) return constant(vertex);
        if (vertex.m_kind == Op::INPUT || vertex.m_kind == Op::OLD || vertex.m_kind == Op::OLDMEM
            || vertex.m_kind == Op::INIT || vertex.m_kind == Op::EXTERNAL) {
            return ref(inputStorage(vertex.m_storage));
        }
        if (AstNodeExpr* const exprp = m_expressions[vertex.m_id]) {
            m_expressions[vertex.m_id] = nullptr;
            return exprp;
        }
        UASSERT(m_values[vertex.m_id], "RepCut operand not lowered before use");
        return ref(m_values[vertex.m_id]);
    }
    AstNodeExpr* expression(const Vertex& vertex) {
        const auto arg = [&](size_t i) { return operand(*vertex.m_inputps.at(i)); };
        AstNodeExpr* resultp = nullptr;
        switch (vertex.m_kind) {
        case Op::CONTEXT:
            resultp = const_cast<AstNodeExpr*>(m_bindings.m_contextps.at(vertex.m_aux))
                          ->cloneTree(false);
            break;
        case Op::COUNTONES: resultp = new AstCountOnes{m_flp, arg(0)}; break;
        case Op::LOGNOT: resultp = new AstLogNot{m_flp, arg(0)}; break;
        case Op::NEGATE: resultp = new AstNegate{m_flp, arg(0)}; break;
        case Op::NOT: resultp = new AstNot{m_flp, arg(0)}; break;
        case Op::REDAND: resultp = new AstRedAnd{m_flp, arg(0)}; break;
        case Op::BRANCH:
        case Op::REDOR: resultp = new AstRedOr{m_flp, arg(0)}; break;
        case Op::REDXOR: resultp = new AstRedXor{m_flp, arg(0)}; break;
        case Op::ADD: resultp = new AstAdd{m_flp, arg(0), arg(1)}; break;
        case Op::AND: resultp = new AstAnd{m_flp, arg(0), arg(1)}; break;
        case Op::CONCAT: {
            AstConcat* const concatp = new AstConcat{m_flp, arg(0), arg(1)};
            // Emitted after V3Unknown; master forbids four-state dtypes, so pin the 2-state
            // equivalent (AstConcat defaults to four-state if an operand had no dtype yet).
            concatp->dtypep(v3Global.rootp()->findBitDType(
                static_cast<int>(vertex.m_width), static_cast<int>(vertex.m_width),
                vertex.m_signed ? VSigning::SIGNED : VSigning::UNSIGNED));
            resultp = concatp;
            break;
        }
        case Op::EQ: resultp = new AstEq{m_flp, arg(0), arg(1)}; break;
        case Op::GT: resultp = new AstGt{m_flp, arg(0), arg(1)}; break;
        case Op::GTE: resultp = new AstGte{m_flp, arg(0), arg(1)}; break;
        case Op::GTES: resultp = new AstGteS{m_flp, arg(0), arg(1)}; break;
        case Op::GTS: resultp = new AstGtS{m_flp, arg(0), arg(1)}; break;
        case Op::LOGAND: resultp = new AstLogAnd{m_flp, arg(0), arg(1)}; break;
        case Op::LOGOR: resultp = new AstLogOr{m_flp, arg(0), arg(1)}; break;
        case Op::LT: resultp = new AstLt{m_flp, arg(0), arg(1)}; break;
        case Op::LTE: resultp = new AstLte{m_flp, arg(0), arg(1)}; break;
        case Op::LTES: resultp = new AstLteS{m_flp, arg(0), arg(1)}; break;
        case Op::LTS: resultp = new AstLtS{m_flp, arg(0), arg(1)}; break;
        case Op::MUL: resultp = new AstMul{m_flp, arg(0), arg(1)}; break;
        case Op::DIV: resultp = new AstDiv{m_flp, arg(0), arg(1)}; break;
        case Op::DIVS: resultp = new AstDivS{m_flp, arg(0), arg(1)}; break;
        case Op::MODDIV: resultp = new AstModDiv{m_flp, arg(0), arg(1)}; break;
        case Op::MODDIVS: resultp = new AstModDivS{m_flp, arg(0), arg(1)}; break;
        case Op::MULS: resultp = new AstMulS{m_flp, arg(0), arg(1)}; break;
        case Op::NEQ: resultp = new AstNeq{m_flp, arg(0), arg(1)}; break;
        case Op::OR: resultp = new AstOr{m_flp, arg(0), arg(1)}; break;
        case Op::REPLICATE: resultp = new AstReplicate{m_flp, arg(0), arg(1)}; break;
        case Op::SUB: resultp = new AstSub{m_flp, arg(0), arg(1)}; break;
        case Op::XOR: resultp = new AstXor{m_flp, arg(0), arg(1)}; break;
        case Op::EXTEND: resultp = new AstExtend{m_flp, arg(0), vertex.m_width}; break;
        case Op::EXTENDS: resultp = new AstExtendS{m_flp, arg(0), vertex.m_width}; break;
        case Op::SHIFTL: resultp = new AstShiftL{m_flp, arg(0), arg(1), vertex.m_width}; break;
        case Op::SHIFTR: resultp = new AstShiftR{m_flp, arg(0), arg(1), vertex.m_width}; break;
        case Op::SHIFTRS: resultp = new AstShiftRS{m_flp, arg(0), arg(1), vertex.m_width}; break;
        case Op::COND:
        case Op::JOIN: resultp = new AstCond{m_flp, arg(0), arg(1), arg(2)}; break;
        case Op::SEL: resultp = new AstSel{m_flp, arg(0), arg(1), vertex.m_width}; break;
        case Op::MEMREAD: resultp = new AstArraySel{m_flp, arg(0), arg(1)}; break;
        case Op::VAR:
        case Op::NEXT:
        case Op::OUTPUT: resultp = arg(0); break;
        default: v3fatalSrc("Unexpected RepCut operation in expression lowering");
        }
        // Like DFG lowering, extensions and shifts need explicit result widths.
        // Every normalized packed operation also preserves its signedness here.
        resultp->dtypeSetLogicSized(vertex.m_width,
                                    vertex.m_signed ? VSigning::SIGNED : VSigning::UNSIGNED);
        return resultp;
    }
    AstCFunc* function(const std::string& name, std::vector<AstNodeStmt*>& statements,
                       bool entry = false) {
        AstCFunc* const funcp = new AstCFunc{m_flp, name, m_scopep};
        funcp->entryPoint(entry);
        funcp->funcPublic(entry);
        funcp->isLoose(!entry);
        funcp->isStatic(false);
        funcp->isConst(false);
        funcp->dontCombine(true);
        funcp->noInline(true);
        funcp->isRepCut(true);
        funcp->keepIfEmpty(true);
        size_t size = 0;
        for (AstNodeStmt* const stmtp : statements) {
            // ExecGraph children are analysis-only placeholders. Its actual dispatch
            // is generated later by V3ExecGraph, outside the compilation chunks.
            // Count the final body independently of the planning cache. Each
            // emitted node belongs to one function, keeping this check linear.
            size += VN_IS(stmtp, ExecGraph) ? 1 : stmtp->nodeCount();
            funcp->addStmtsp(stmtp);
        }
        UASSERT_OBJ(size <= m_limit, funcp, "RepCut function construction budget exceeded");
        m_scopep->addBlocksp(funcp);
        if (m_reportp) *m_reportp << name << '\t' << size << '\t' << entry << '\n';
        m_maxBody = std::max(m_maxBody, size);
        ++m_functions;
        m_createdFuncps.push_back(funcp);
        statements.clear();
        return funcp;
    }
    AstNodeStmt* call(AstCFunc* funcp) const {
        AstCCall* const callp = new AstCCall{m_flp, funcp};
        callp->dtypeSetVoid();
        return callp->makeStmt();
    }
    static std::vector<AstNodeStmt*> takeBranch(const AstIf* ifp, bool taken) {
        std::vector<AstNodeStmt*> result;
        while (AstNode* const nodep = taken ? ifp->thensp() : ifp->elsesp()) {
            result.push_back(VN_AS(nodep->unlinkFrBack(), NodeStmt));
        }
        return result;
    }
    void reportCuts(const std::string& tag, const ChunkPlan& plan) {
        const size_t n = plan.m_prefixNodes.size() - 1;
        std::vector<bool> greedy(n + 1, false);
        std::vector<bool> selected(n + 1, false);
        for (const size_t end : plan.m_greedyEnds) greedy[end] = true;
        for (const size_t end : plan.m_ends) selected[end] = true;
        uint64_t greedyBytes = 0;
        uint64_t selectedBytes = 0;
        size_t moved = 0;
        for (size_t i = 0; i <= n; ++i) {
            if (m_cutReportp)
                *m_cutReportp << m_cutGroups << '\t' << tag << '\t' << i << '\t'
                              << plan.m_prefixNodes[i] << '\t' << plan.m_liveValues[i] << '\t'
                              << plan.m_liveBytes[i] << '\t' << greedy[i] << '\t' << selected[i]
                              << '\t' << plan.m_analyzed << '\n';
            if (greedy[i]) greedyBytes += plan.m_liveBytes[i];
            if (selected[i]) selectedBytes += plan.m_liveBytes[i];
        }
        for (size_t i = 0; i < plan.m_ends.size(); ++i)
            moved += plan.m_ends[i] != plan.m_greedyEnds[i];
        ++m_cutGroups;
        V3Stats::addStatSum("RepCut chunks, analyzed groups", plan.m_analyzed);
        V3Stats::addStatSum("RepCut chunks, moved boundaries", moved);
        V3Stats::addStatSum("RepCut chunks, greedy span bytes", greedyBytes);
        V3Stats::addStatSum("RepCut chunks, selected span bytes", selectedBytes);
    }
    void boundGuard(const std::string& tag, AstNodeStmt* stmtp, StatementSizes& cache) {
        AstIf* const ifp = VN_CAST(stmtp, If);
        if (!ifp || statementSize(ifp, cache) <= m_limit) return;
        // Reduce descendants first. Outlining both arms before doing this turns
        // a deep priority chain into a tiny non-inline function at every level.
        // Cached child sizes avoid rescanning the surviving conditional trees.
        std::array<size_t, 2> sizes{0, 0};
        size_t size = 1 + ifp->condp()->nodeCount();
        for (const bool taken : {true, false}) {
            for (AstNode* nodep = taken ? ifp->thensp() : ifp->elsesp(); nodep;
                 nodep = nodep->nextp()) {
                AstNodeStmt* const childp = VN_AS(nodep, NodeStmt);
                boundGuard(tag, childp, cache);
                sizes[taken] += statementSize(childp, cache);
            }
            size += sizes[taken];
        }
        // Keep small arms in their parent. Only outline another arm if the
        // condition and remaining body still exceed the construction budget.
        const bool larger = sizes[true] >= sizes[false];
        for (const bool taken : {larger, !larger}) {
            if (size <= m_limit) break;
            if (!sizes[taken]) continue;
            std::vector<AstNodeStmt*> body = takeBranch(ifp, taken);
            AstNodeStmt* const callp = call(chunksSized(
                tag + "__guard" + cvtToStr(m_guardFunctions++), std::move(body), cache, false));
            if (taken)
                ifp->addThensp(callp);
            else
                ifp->addElsesp(callp);
            size = size - sizes[taken] + statementSize(callp, cache);
        }
        cache[ifp] = size;
        UASSERT_OBJ(size <= m_limit, ifp, "RepCut conditional exceeds construction budget");
    }
    AstCFunc* chunksSized(const std::string& tag, std::vector<AstNodeStmt*> statements,
                          StatementSizes& cache, bool entry) {
        // Calls stay under the original branch, after local optimization.
        for (AstNodeStmt* const stmtp : statements) boundGuard(tag, stmtp, cache);
        size_t ordinal = 0;
        // Also bound dispatch functions; a large partition cannot turn into one
        // enormous function containing calls to all its leaf chunks.
        while (true) {
            size_t total = 0;
            std::vector<size_t> sizes;
            sizes.reserve(statements.size());
            for (AstNodeStmt* const stmtp : statements) {
                const size_t count = statementSize(stmtp, cache);
                UASSERT_OBJ(count <= m_limit, stmtp, "Atomic RepCut statement exceeds budget");
                sizes.push_back(count);
                total += count;
            }
            if (total <= m_limit) { return function(tag, statements, entry); }
            const ChunkPlan plan = planChunks(statements, sizes, m_limit);
            reportCuts(tag, plan);
            std::vector<AstNodeStmt*> group;
            std::vector<AstNodeStmt*> calls;
            size_t begin = 0;
            for (const size_t end : plan.m_ends) {
                for (; begin < end; ++begin) group.push_back(statements[begin]);
                calls.push_back(call(function(tag + "__chunk" + cvtToStr(ordinal++), group)));
            }
            statements = std::move(calls);
        }
    }
    AstCFunc* chunks(const std::string& tag, std::vector<AstNodeStmt*> statements,
                     bool entry = true) {
        StatementSizes sizes;
        StatementSizeVisitor{sizes, statements};
        return chunksSized(tag, std::move(statements), sizes, entry);
    }
    static void append(std::vector<AstNodeStmt*>& root, const Frame& frame, AstNodeStmt* stmtp) {
        if (!frame.m_ifp)
            root.push_back(stmtp);
        else if (frame.m_taken)
            frame.m_ifp->addThensp(stmtp);
        else
            frame.m_ifp->addElsesp(stmtp);
    }
    void enterRegion(std::vector<AstNodeStmt*>& root, std::vector<Frame>& frames, size_t target) {
        std::vector<size_t> enter;
        const auto depth
            = [&](size_t region) { return region == NO_ID ? 0 : m_regionDepth[region]; };
        while (frames.back().m_region != target) {
            if (depth(frames.back().m_region) >= depth(target)) {
                frames.pop_back();
            } else {
                enter.push_back(target);
                target = m_graph.m_regions[target].m_parent;
            }
        }
        for (auto it = enter.rbegin(); it != enter.rend(); ++it) {
            const Region& region = m_graph.m_regions[*it];
            AstIf* const ifp = new AstIf{m_flp, operand(*region.m_predicatep), nullptr};
            append(root, frames.back(), ifp);
            frames.push_back({*it, ifp, region.m_taken});
            ++m_guards;
        }
    }
    std::vector<AstNodeStmt*> evaluationStatements(const std::string& tag,
                                                   const std::vector<size_t>& original,
                                                   AstVarScope* effectPendingp,
                                                   const NativeGraphBoundary* nativep = nullptr) {
        std::vector<AstNodeStmt*> statements;
        if (effectPendingp && !nativep) {
            statements.push_back(new AstAssign{m_flp, ref(effectPendingp, VAccess::WRITE),
                                               new AstConst{m_flp, AstConst::BitFalse{}}});
        }
        std::set<AstVarScope*> availableInputs;
        std::set<size_t> inputs;
        std::set<size_t> exports;
        if (nativep) {
            for (const auto& pair : nativep->m_inputs) inputs.insert(pair.first);
            for (const auto& pair : nativep->m_outputs) exports.insert(pair.first);
        }
        SharedPhase shared
            = SharedPhase::make(m_graph, original, inputs, exports, &m_representatives);
        const std::vector<size_t>& sequence = shared.m_sequence;
        V3Stats::addStatSum("RepCut emit, graph expressions shared", shared.m_shared);
        V3Stats::addStatSum("RepCut emit, graph operations pruned", shared.m_pruned);
        if (nativep) {
            for (const auto& pair : nativep->m_inputs) {
                m_values[pair.first] = pair.second;
                m_expressions[pair.first] = nullptr;
                m_expressionSizes[pair.first] = 1;
                availableInputs.insert(pair.second);
            }
        }
        for (const size_t id : sequence) {
            m_values[id] = nullptr;
            m_expressions[id] = nullptr;
            m_expressionSizes[id] = 1;
            m_uses[id] = 0;
        }
        for (const size_t id : sequence) {
            const Vertex& vertex = *m_graph.m_vertexps[id];
            if (vertex.m_kind == Op::INPUT || vertex.m_kind == Op::OLD || vertex.m_kind == Op::INIT
                || vertex.m_kind == Op::EXTERNAL)
                availableInputs.insert(inputStorage(vertex.m_storage));
            for (const Vertex* const inputp : vertex.m_inputps) {
                const size_t input = m_representatives[inputp->m_id];
                ++m_uses[input];
                m_consumers[input] = id;
            }
            if (vertex.m_kind == Op::EFFECT || vertex.m_kind == Op::CALL_CAPTURE) {
                if (vertex.m_kind == Op::EFFECT) {
                    m_candidates[id].effectEnablep()
                        = temp(tag + "__effect" + cvtToStr(id), 1, false);
                    statements.push_back(
                        new AstAssign{m_flp, ref(m_candidates[id].effectEnablep(), VAccess::WRITE),
                                      new AstConst{m_flp, AstConst::BitFalse{}}});
                }
                for (const Vertex* const inputp : vertex.m_inputps) {
                    m_effectArguments[id].push_back(
                        temp(tag + "__effect" + cvtToStr(id) + "_"
                                 + cvtToStr(m_effectArguments[id].size()),
                             inputp->m_width, inputp->m_signed));
                }
                continue;
            }
            if (vertex.m_kind != Op::MEMWRITE) continue;
            for (size_t i = 0; i + 1 < vertex.m_inputps.size(); ++i) {
                const Vertex& input = *vertex.m_inputps[i + 1];
                if (i == 3 && input.m_kind == Op::CONSTANT) continue;
                m_candidates[id].memoryOperand(i) = temp(
                    tag + "__n" + cvtToStr(id) + "_" + cvtToStr(i), input.m_width, input.m_signed);
            }
            // A disabled store must not reuse the previous evaluation's enable.
            statements.push_back(
                new AstAssign{m_flp, ref(m_candidates[id].memoryEnablep(), VAccess::WRITE),
                              new AstConst{m_flp, AstConst::BitFalse{}}});
        }
        std::vector<Frame> frames{{NO_ID, nullptr, false}};
        for (const size_t id : sequence) {
            const Vertex& vertex = *m_graph.m_vertexps[id];
            if (vertex.m_kind == Op::CONSTANT || vertex.m_kind == Op::OLD
                || vertex.m_kind == Op::OLDMEM || vertex.m_kind == Op::INPUT
                || vertex.m_kind == Op::INIT || vertex.m_kind == Op::EXTERNAL)
                continue;
            if (vertex.m_kind == Op::EFFECT || vertex.m_kind == Op::CALL_CAPTURE) {
                enterRegion(statements, frames, vertex.m_region);
                for (size_t i = 0; i < vertex.m_inputps.size(); ++i) {
                    append(statements, frames.back(),
                           new AstAssign{m_flp, ref(m_effectArguments[id][i], VAccess::WRITE),
                                         operand(*vertex.m_inputps[i])});
                }
                if (m_candidates[id].effectEnablep())
                    append(statements, frames.back(),
                           new AstAssign{m_flp,
                                         ref(m_candidates[id].effectEnablep(), VAccess::WRITE),
                                         new AstConst{m_flp, AstConst::BitTrue{}}});
                if (effectPendingp && vertex.m_kind == Op::EFFECT) {
                    append(statements, frames.back(),
                           new AstAssign{m_flp, ref(effectPendingp, VAccess::WRITE),
                                         new AstConst{m_flp, AstConst::BitTrue{}}});
                }
            } else if (vertex.m_kind == Op::MEMWRITE) {
                enterRegion(statements, frames, vertex.m_region);
                for (size_t i = 0; i + 1 < vertex.m_inputps.size(); ++i) {
                    if (!m_candidates[id].memoryOperand(i)) continue;
                    const Vertex& input = *vertex.m_inputps[i + 1];
                    append(statements, frames.back(),
                           new AstAssign{m_flp,
                                         ref(m_candidates[id].memoryOperand(i), VAccess::WRITE),
                                         operand(input)});
                }
            } else {
                size_t size = 1;
                for (const Vertex* const inputp : vertex.m_inputps)
                    size += m_expressionSizes[m_representatives[inputp->m_id]];
                const bool join = vertex.m_kind == Op::JOIN || vertex.m_kind == Op::COND;
                AstVarScope* const exportedp = nativep && nativep->m_outputs.count(id)
                                                   ? nativep->m_outputs.at(id)
                                                   : nullptr;
                if (!exportedp && !join && !vertex.isSink() && !vertex.m_isRegionPredicate
                    && m_uses[id] == 1 && size <= expressionLimit()
                    && m_graph.m_vertexps[m_consumers[id]]->m_region == vertex.m_region) {
                    m_expressions[id] = expression(vertex);
                    m_expressionSizes[id] = size;
                    ++m_inlined;
                    continue;
                }
                enterRegion(statements, frames, vertex.m_region);
                AstVarScope* const valuep = exportedp ? exportedp
                                                      : temp(tag + "__n" + cvtToStr(id),
                                                             vertex.m_width, vertex.m_signed);
                // Intermediate values are defined in this evaluation before every
                // guarded use; they never carry state between calls. Let Localize
                // use that lifetime when all references fit in one CFunc. Values
                // crossing compilation chunks still need shared model storage.
                if (!vertex.isSink()) valuep->varp()->varType(VVarType::BLOCKTEMP);
                AstNodeStmt* stmtp = nullptr;
                if (join) {
                    stmtp = new AstIf{m_flp, operand(*vertex.m_inputps[0]),
                                      new AstAssign{m_flp, ref(valuep, VAccess::WRITE),
                                                    operand(*vertex.m_inputps[1])},
                                      new AstAssign{m_flp, ref(valuep, VAccess::WRITE),
                                                    operand(*vertex.m_inputps[2])}};
                } else {
                    stmtp = new AstAssign{m_flp, ref(valuep, VAccess::WRITE), expression(vertex)};
                }
                append(statements, frames.back(), stmtp);
                m_values[id] = valuep;
                if (vertex.isSink()) m_candidates[id].scalarValuep() = valuep;
            }
        }
        for (const size_t id : sequence) UASSERT(!m_expressions[id], "Unused RepCut expression");
        // Keep the phase in immutable value form until the whole guarded program
        // has been optimized and scheduled. State release would introduce writes
        // to old-state inputs and invalidate the program's single-assignment model.
        std::set<AstVarScope*> preserve;
        if (nativep) {
            for (const auto& pair : nativep->m_outputs) preserve.insert(pair.second);
        }
        for (const size_t id : sequence) {
            if (!m_graph.m_vertexps[id]->isSink()) continue;
            for (AstVarScope* const vscp : m_candidates[id].slots()) {
                if (vscp) preserve.insert(vscp);
            }
            preserve.insert(m_effectArguments[id].begin(), m_effectArguments[id].end());
        }
        if (effectPendingp) preserve.insert(effectPendingp);
        m_copies += eliminateCopies(statements, preserve);
        // A join of already available leaf values can remain an expression.
        // This does not speculate either arm's defining computation.
        if (v3Global.opt.fDfg()) prepareDfg(statements, availableInputs, preserve);
        // Optimize the guarded program as a set of straight-line DFG blocks.
        // The emitter has its own context/prefix, separate from the two
        // whole-netlist passes.
        optimizeProgram(*m_scopep, statements, preserve, expressionLimit(), m_dfgContext);
        if (m_storageGroup) PrivateStorageVisitor{statements, m_storageGroup};
        m_copies += eliminateCopies(statements, preserve);
        V3Stats::addStatSum("RepCut emit, local expressions substituted",
                            substituteLocalExpressions(statements, preserve, expressionLimit()));
        if (v3Global.opt.fMergeCond()) V3MergeCond::mergeScoped(statements);
        return statements;
    }
    AstNodeExpr* memoryTarget(size_t sink) const {
        const Vertex& vertex = *m_graph.m_vertexps[sink];
        const Candidates& candidate = m_candidates[sink];
        AstNodeExpr* lhsp = new AstArraySel{m_flp, ref(storage(vertex.m_storage), VAccess::WRITE),
                                            ref(candidate.memoryAddressp())};
        if (vertex.m_inputps.size() == 5) {
            const Vertex& offset = *vertex.m_inputps[4];
            AstNodeExpr* const offsetp = offset.m_kind == Op::CONSTANT
                                             ? static_cast<AstNodeExpr*>(constant(offset))
                                             : ref(candidate.memoryOffsetp());
            lhsp = new AstSel{m_flp, lhsp, offsetp, vertex.m_width};
        }
        return lhsp;
    }
    ExecMTask* phaseTask(AstExecGraph* graphp, AstCFunc* funcp, size_t part,
                         AstVarScope* trigVscp) {
        // Master's V3ExecGraph::addTriggerMasks derives each MTask's run mask from the
        // AstTriggered tests in its body, and the runtime runs a MTask only when its mask
        // intersects the set triggers. Wrap the partition call in such a test (bit 0, which
        // dispatch() sets before invoking the graph).
        AstIf* const bodyp = new AstIf{m_flp, new AstTriggered{m_flp, trigVscp, {0}}, call(funcp)};
        ExecMTask* const taskp = new ExecMTask{graphp, m_scopep, bodyp};
        taskp->funcp()->isRepCut(true);
        // Partition zero stays on the caller, subsequent partitions on workers.
        const size_t threads = v3Global.opt.threads();
        taskp->fixedThread(static_cast<uint32_t>((part + threads - 1) % threads));
        taskp->cost(1);  // V3ExecGraph recomputes final costs before thread packing.
        taskp->priority(1);
        AstCCall* const callp = new AstCCall{m_flp, taskp->funcp()};
        callp->dtypeSetVoid();
        graphp->addCallsp(callp);
        return taskp;
    }
    AstNodeStmt* dispatch(AstExecGraph* graphp, const std::string& tag, AstVarScope* trigVscp) {
        // Set the graph's trigger word so every partition MTask (mask bit 0) runs when the
        // graph is invoked. The invocation is already placed where the region is active.
        AstNodeStmt* const setp
            = new AstAssign{m_flp,
                            new AstArraySel{m_flp, new AstVarRef{m_flp, trigVscp, VAccess::WRITE},
                                            new AstConst{m_flp, AstConst::WidthedValue{}, 32, 0}},
                            new AstConst{m_flp, AstConst::WidthedValue{}, 64, 1}};
        // Existing ExecGraph traversal requires the graph directly under CFunc.
        // Put the edge condition around a call, not around the graph itself.
        std::vector<AstNodeStmt*> body{setp, graphp};
        AstCFunc* const dispatchp = function("__V" + tag + "_dispatch", body, true);
        dispatchp->isLoose(true);
        dispatchp->funcPublic(false);
        return call(dispatchp);
    }
    AstNodeStmt* parallelPhase(size_t phase, const std::string& tag) {
        if (v3Global.opt.threads() <= 1) {
            std::vector<AstNodeStmt*> calls;
            for (const auto& functions : m_phases) {
                if (functions[phase]->stmtsp()) calls.push_back(call(functions[phase]));
            }
            return call(chunks("__V" + tag + "_serial", std::move(calls)));
        }
        bool active = false;
        for (const auto& functions : m_phases) active |= functions[phase]->stmtsp() != nullptr;
        if (!active) return nullptr;
        // The graph's trigger vector: one 64-bit word (master requires an unpacked array so
        // that addTriggerMasks/addTriggerCosts see an UnpackArrayDType).
        AstNodeDType* const wordDTypep
            = v3Global.rootp()->findBitDType(64, 64, VSigning::UNSIGNED);
        AstUnpackArrayDType* const trigDTypep
            = new AstUnpackArrayDType{m_flp, wordDTypep, new AstRange{m_flp, 0, 0}};
        v3Global.rootp()->typeTablep()->addTypesp(trigDTypep);
        AstVarScope* const trigVscp
            = v3Global.rootp()->topScopep()->createTemp("__V" + tag + "_Triggered", trigDTypep);
        AstExecGraph* const graphp = new AstExecGraph{m_flp, tag, trigVscp};
        // Publication already accounts for dispatch cost and owner imbalance when selecting
        // parallel execution. The generic instruction-cost threshold must not override it.
        graphp->forceParallel(phase == 1);
        for (size_t part = 0; part < m_phases.size(); ++part) {
            const auto& functions = m_phases[part];
            if (!functions[phase]->stmtsp()) continue;
            // At most one scheduled task per partition. Its chunks remain calls.
            phaseTask(graphp, functions[phase], part, trigVscp);
        }
        return dispatch(graphp, tag, trigVscp);
    }
    // Keep dependency operands visible to native scheduling without exposing
    // the kernel's implementation. Const-reference inputs avoid array copies;
    // output-reference operands identify the candidate values written by it.
    // These operands are erased after optimization, before C++ generation.
    void nativeArgument(AstCCall* callp, AstVarScope* vscp, bool output, size_t ordinal) {
        AstVar* const varp = new AstVar{m_flp, VVarType::BLOCKTEMP,
                                        "__Vdependency" + cvtToStr(ordinal), vscp->dtypep()};
        varp->funcLocal(true);
        varp->direction(output ? VDirection::OUTPUT : VDirection::CONSTREF);
        if (!output) varp->isConst(true);
        callp->funcp()->addArgsp(varp);
        callp->addArgsp(ref(vscp, output ? VAccess::WRITE : VAccess::READ));
    }
    bool nativeParallelPublication(const Plan& plan, size_t domain,
                                   const std::vector<size_t>& sinks) {
        // This is a conservative work heuristic, not a prediction in cycles.
        // Four units represent one unconditional scalar copy or enable check.
        // Discount enabled copies to one-quarter activity; shared enables are
        // checked once in serial code, but once per owner in parallel code.
        // Wide copies count their 32-bit words (a <=64-bit copy is scalar).
        // A dispatch allowance of 512 scalar copies and a 25% serial-work
        // margin avoid dispatching domains with little removable caller work.
        // Cache residency and actual activity are unknown at compile time.
        static constexpr uint64_t FULL_WORK = 4;
        static constexpr uint64_t DISPATCH_WORK = 512 * FULL_WORK;
        struct OwnerWork final {
            uint64_t m_scalars = 0;  // Scalar state publications assigned to this owner
            uint64_t m_memoryPorts = 0;  // Memory write ports assigned to this owner
            uint64_t m_copies = 0;  // Estimated scalar or word-copy work for this owner
            uint64_t m_guards = 0;  // Estimated guard work for this owner
            std::set<AstVarScope*>
                m_enables;  // Distinct publication enable bindings used by this owner
        };
        std::vector<OwnerWork> owners(m_phases.size());
        std::set<AstVarScope*> serialEnables;
        uint64_t serial = 0;
        for (const size_t id : sinks) {
            const Vertex& vertex = *m_graph.m_vertexps[id];
            if (storage(vertex.m_storage)->varp()->isSc()) continue;
            const size_t owner = plan.m_ownership.m_stateOwners[vertex.m_storage];
            UASSERT(owner < owners.size(), "Native publication has no partition owner");
            OwnerWork& work = owners[owner];
            const auto& candidate = m_candidates[id];
            const bool scalar = vertex.m_kind == Op::NEXT;
            UASSERT(scalar || vertex.m_kind == Op::MEMWRITE, "Unexpected publication sink");
            const AstVarScope* const valuep
                = (scalar ? candidate.scalarValuep() : candidate.memoryValuep());
            const uint64_t words = valuep->width() <= 64 ? 1 : valuep->widthWords();
            AstVarScope* const enablep
                = (scalar ? candidate.scalarEnablep() : candidate.memoryEnablep());
            const uint64_t copies = words * (enablep ? 1 : FULL_WORK);
            work.m_copies += copies;
            serial += copies;
            if (scalar) {
                ++work.m_scalars;
                if (enablep) {
                    if (work.m_enables.insert(enablep).second) work.m_guards += FULL_WORK;
                    if (serialEnables.insert(enablep).second) serial += FULL_WORK;
                }
            } else {
                ++work.m_memoryPorts;
                // Memory ports retain separate enable checks and index loads.
                work.m_guards += 2 * FULL_WORK;
                serial += 2 * FULL_WORK;
            }
        }
        uint64_t maximum = 0;
        size_t participants = 0;
        for (const OwnerWork& work : owners) {
            maximum = std::max(maximum, work.m_copies + work.m_guards);
            if (work.m_scalars || work.m_memoryPorts) ++participants;
        }
        const uint64_t margin = (serial + FULL_WORK - 1) / FULL_WORK;
        bool parallel = false;
        const char* reason;
        if (v3Global.opt.threads() <= 1) {
            reason = "single-thread";
        } else if (!participants) {
            reason = "no-eligible-writes";
        } else {
            if (participants < 2) {
                reason = "one-owner";
            } else if (serial <= maximum + margin) {
                reason = "owner-imbalance";
            } else if (serial <= maximum + DISPATCH_WORK + margin) {
                reason = "dispatch-cost";
            } else {
                parallel = true;
                reason = "estimated-benefit";
            }
            V3Stats::addStatSum(parallel ? "RepCut native publication, auto parallel domains"
                                         : "RepCut native publication, auto serial domains",
                                1);
        }
        for (size_t owner = 0; m_publicationReportp && owner < owners.size(); ++owner) {
            const OwnerWork& work = owners[owner];
            *m_publicationReportp << domain << '\t' << owner << '\t' << work.m_scalars << '\t'
                                  << work.m_memoryPorts << '\t' << work.m_copies << '\t'
                                  << work.m_guards << '\t' << work.m_copies + work.m_guards << '\t'
                                  << serial << '\t' << maximum << '\t' << DISPATCH_WORK << '\t'
                                  << margin << "\tauto\t" << (parallel ? "parallel" : "serial")
                                  << '\t' << reason << '\n';
        }
        return parallel;
    }
    AstNodeExpr* publicationEnabled(std::vector<AstNodeExpr*> operands) const {
        // Balance the short-circuit expression, including for large designs.
        UASSERT(!operands.empty(), "Publication has no enable operands");
        while (operands.size() > 1) {
            std::vector<AstNodeExpr*> next;
            for (size_t i = 0; i < operands.size(); i += 2) {
                next.push_back(i + 1 == operands.size()
                                   ? operands[i]
                                   : new AstLogOr{m_flp, operands[i], operands[i + 1]});
            }
            operands = std::move(next);
        }
        return operands.front();
    }
    AstNodeStmt* guardedPublication(const std::string& tag, const std::vector<size_t>& sinks,
                                    AstNodeStmt* dispatchp) {
        std::set<AstVarScope*> seen;
        std::vector<AstVarScope*> enables;
        for (const size_t id : sinks) {
            const Vertex& vertex = *m_graph.m_vertexps[id];
            if (storage(vertex.m_storage)->varp()->isSc()) continue;
            AstVarScope* const enablep
                = (vertex.m_kind == Op::NEXT ? m_candidates[id].scalarEnablep()
                                             : m_candidates[id].memoryEnablep());
            // An unconditional write requires publication on every invocation.
            if (!enablep) return dispatchp;
            if (seen.insert(enablep).second) enables.push_back(enablep);
        }
        V3Stats::addStatSum("RepCut native publication, guarded dispatches", 1);
        V3Stats::addStatSum("RepCut native publication, dispatch enable operands", enables.size());
        std::vector<AstNodeExpr*> operands;
        for (AstVarScope* const enablep : enables) operands.push_back(ref(enablep));
        size_t ordinal = 0;
        // Bound both the condition and its helper functions. The native POST
        // wrapper retains all dependency arguments, so candidates are complete
        // and old-state readers have finished before this check. Skipping its
        // dispatch leaves the runtime epoch at the last completed invocation.
        while (operands.size() > expressionLimit()) {
            std::vector<AstNodeExpr*> next;
            for (size_t begin = 0; begin < operands.size(); begin += expressionLimit()) {
                const size_t end = std::min(operands.size(), begin + expressionLimit());
                std::vector<AstNodeExpr*> group(operands.begin() + begin, operands.begin() + end);
                std::vector<AstNodeStmt*> body{new AstCReturn{m_flp, publicationEnabled(group)}};
                AstCFunc* const funcp
                    = function("__V" + tag + "_enabled" + cvtToStr(ordinal++), body);
                funcp->rtnType("bool");
                AstCCall* const callp = new AstCCall{m_flp, funcp};
                callp->dtypeSetBit();
                next.push_back(callp);
            }
            operands = std::move(next);
        }
        V3Stats::addStatSum("RepCut native publication, dispatch enable helpers", ordinal);
        return new AstIf{m_flp, publicationEnabled(operands), dispatchp};
    }
    AstAlwaysPost* nativePublication(const Plan& plan, size_t domain,
                                     const std::vector<size_t>& sinks) {
        if (!nativeParallelPublication(plan, domain, sinks)) return nullptr;
        std::vector<std::vector<AstNodeStmt*>> bodies(m_phases.size());
        std::vector<std::map<AstVarScope*, AstIf*>> groups(m_phases.size());
        std::set<AstVarScope*> reads;
        std::set<AstVarScope*> writes;
        std::vector<AstVarScope*> outputs;
        for (const size_t id : sinks) {
            const Vertex& vertex = *m_graph.m_vertexps[id];
            AstVarScope* const targetp = storage(vertex.m_storage);
            // SystemC channel access must remain on the simulation caller.
            if (targetp->varp()->isSc()) continue;
            // Candidate ports may be computed by different partitions. The
            // validated storage owner alone commits all writes to a memory.
            const size_t owner = plan.m_ownership.m_stateOwners[vertex.m_storage];
            UASSERT(owner < bodies.size(), "Native publication has no partition owner");
            const auto& candidate = m_candidates[id];
            for (AstVarScope* const vscp : candidate.slots()) {
                if (vscp) reads.insert(vscp);
            }
            if (writes.insert(targetp).second) outputs.push_back(targetp);
            if (!m_sharedModules.count(targetp->scopep()->modp())) {
                targetp->varp()->repcutStorageGroup(
                    storageGroup(owner, StorageRole::PUBLISHED_STATE));
            }
            if (vertex.m_kind == Op::NEXT) {
                AstAssign* const assignp = new AstAssign{m_flp, ref(targetp, VAccess::WRITE),
                                                         ref(candidate.scalarValuep())};
                if (candidate.scalarEnablep()) {
                    AstIf*& ifp = groups[owner][candidate.scalarEnablep()];
                    if (!ifp) {
                        ifp = new AstIf{m_flp, ref(candidate.scalarEnablep()), nullptr};
                        bodies[owner].push_back(ifp);
                    }
                    ifp->addThensp(assignp);
                } else {
                    bodies[owner].push_back(assignp);
                }
                V3Stats::addStatSum("RepCut native publication, parallel scalars", 1);
            } else {
                UASSERT(vertex.m_kind == Op::MEMWRITE, "Unexpected native publication sink");
                // Sinks are already in source-priority order. All writes to a
                // memory share one owner, including writes to aliased indices.
                bodies[owner].push_back(new AstIf{
                    m_flp, ref(candidate.memoryEnablep()),
                    new AstAssign{m_flp, memoryTarget(id), ref(candidate.memoryValuep())}});
                V3Stats::addStatSum("RepCut native publication, parallel memory ports", 1);
                if (vertex.m_inputps.size() == 5)
                    V3Stats::addStatSum("RepCut native publication, partial memory ports", 1);
            }
        }
        if (writes.empty()) return nullptr;
        const std::string tag = "repcut_native" + cvtToStr(domain) + "_publish";
        for (size_t part = 0; part < bodies.size(); ++part) {
            m_phases[part][1]
                = chunks("__V" + tag + "_p" + cvtToStr(part), std::move(bodies[part]));
        }
        std::vector<AstNodeStmt*> dispatches{
            guardedPublication(tag, sinks, parallelPhase(1, tag))};
        AstCFunc* const funcp = chunks("__V" + tag, std::move(dispatches));
        funcp->entryPoint(false);
        funcp->funcPublic(false);
        funcp->isLoose(true);
        funcp->repcutDependencyArgs(true);
        AstCCall* const callp = new AstCCall{m_flp, funcp};
        callp->dtypeSetVoid();
        size_t ordinal = 0;
        // Use graph/storage order for deterministic dependency operands.
        std::set<AstVarScope*> added;
        for (const size_t id : sinks) {
            for (AstVarScope* const vscp : m_candidates[id].slots()) {
                if (vscp && reads.count(vscp) && added.insert(vscp).second)
                    nativeArgument(callp, vscp, false, ordinal++);
            }
        }
        for (AstVarScope* const vscp : outputs) nativeArgument(callp, vscp, true, ordinal++);
        // The ordinary scheduler's POST dependencies wait for every clocked
        // old-state reader, including retained procedures and other domains.
        // Candidate reads also depend on completion of the compute dispatch.
        // This dispatch joins publication before any scheduled consumer runs.
        AstAlwaysPost* const postp = new AstAlwaysPost{m_flp};
        postp->addStmtsp(callp->makeStmt());
        V3Stats::addStatSum("RepCut native publication, dispatches", 1);
        return postp;
    }
    bool nativeStateReleaseAllowed(const Plan& plan) const {
        // Report every independent restriction, even when an earlier one is
        // sufficient to reject the model. These counts explain why staging is
        // retained; they do not imply that removing one guard would be safe.
        const auto blocked = [](const char* reasonp, size_t count) {
            V3Stats::addStat(std::string{"RepCut native direct-state, blocked "} + reasonp, count);
        };
        blocked("threads", v3Global.opt.threads() != 1);
        blocked("partitions", plan.m_partitions.size() != 1);
        blocked("domains", m_bindings.m_domainps.size() != 1);
        blocked("coverage", v3Global.opt.coverage());
        blocked("tracing", v3Global.opt.trace());
        blocked("VPI", v3Global.opt.vpi());
        blocked("cycle boundaries", m_graph.m_report.m_nativeCycleBoundaries);
        blocked("effects", m_bindings.m_effectps.size());
        blocked("callbacks", m_bindings.m_callbacks.size());
        blocked("context expressions", m_bindings.m_contextps.size());
        size_t retainedObservers = 0;
        for (const AstAlways* const retainedp : m_bindings.m_retainedps) {
            if (!isNativeDecoderUpdate(retainedp)) ++retainedObservers;
        }
        blocked("retained procedures", retainedObservers);
        const bool lifecycleObserver = NativeStateObserverVisitor{m_netlistp}.hasObserver();
        blocked("lifecycle or callable block", lifecycleObserver);
        size_t nonPrimaryClocks = 0;
        for (const AstSenTree* const domainp : m_bindings.m_domainps) {
            if (domainp->exists([](const AstVarRef* refp) {
                    return !refp->varp()->isPrimaryIO() || !refp->varp()->isNonOutput();
                }))
                ++nonPrimaryClocks;
        }
        blocked("non-primary clock domains", nonPrimaryClocks);
        size_t externalStorage = 0;
        for (const AstVarScope* const vscp : m_bindings.m_storageps) {
            const AstVar* const varp = vscp->varp();
            if (varp->isSc() || varp->isSigUserRdPublic() || varp->isSigUserRWPublic())
                ++externalStorage;
        }
        blocked("external storage", externalStorage);
        const auto reject = [](const char* reasonp) {
            V3Stats::addStat(std::string{"RepCut native direct-state, rejected "} + reasonp, 1);
            return false;
        };
        // Native kernels normally defer every state write to the NBA/POST
        // region. Early writes are observable if another process, domain,
        // worker, foreign call, or coverage process can still read old state.
        // Start with closed single-thread kernels; all clocked observers are
        // captured together and the remaining native logic is pure settling.
        // Runtime model descriptors no longer introduce trace CFuncs, so tracing
        // must remain an explicit observer boundary.
        if (v3Global.opt.threads() != 1 || plan.m_partitions.size() != 1
            || m_bindings.m_domainps.size() != 1 || v3Global.opt.coverage() || v3Global.opt.vpi()
            || v3Global.opt.trace() || m_graph.m_report.m_nativeCycleBoundaries
            || !m_bindings.m_effectps.empty() || !m_bindings.m_callbacks.empty()
            || !m_bindings.m_contextps.empty())
            return reject("observers or parallelism");
        if (retainedObservers) return reject("retained observer");
        if (lifecycleObserver) return reject("lifecycle or callable block");
        // Generated clocks need a separate event-region proof. Here the only
        // sensitivity inputs must be externally driven primary inputs.
        if (nonPrimaryClocks) return reject("non-primary clock");
        if (externalStorage) return reject("external storage");
        V3Stats::addStat("RepCut native direct-state, retained decoders allowed",
                         m_bindings.m_retainedps.size());
        return true;
    }
    bool nativeStagedBatchAllowed(const Plan& plan) const {
        // Batching pure captures does not require early state publication.
        // Every state write remains an NBA/POST operation, and every callback
        // or effect remains on the caller after the joined captures. Native
        // callback validation already rejects context imports and blocking
        // writes observable outside the original process. Retained processes
        // still participate in ordinary old-state/publication dependencies.
        // The same old-state observer proof applies to serial shared prefixes.
        if (plan.m_partitions.size() != static_cast<size_t>(v3Global.opt.threads())
            || v3Global.opt.coverage() || v3Global.opt.vpi() || v3Global.opt.trace())
            return false;
        for (const AstVarScope* const vscp : m_bindings.m_storageps) {
            const AstVar* const varp = vscp->varp();
            if (varp->isSc() || varp->isSigUserRdPublic() || varp->isSigUserRWPublic()
                || varp->isWrittenByDpi())
                return false;
        }
        // Reentrant or opaque retained calls can observe or modify model
        // storage outside visible scheduler dependencies. Keep their original
        // capture boundaries. Non-context imports with explicit operands are
        // ordered by the native scheduler, just as before batching.
        for (const AstAlways* const retainedp : m_bindings.m_retainedps) {
            if (retainedp->exists([](const AstNode* nodep) {
                    if (VN_IS(nodep, CStmt)) return true;
                    if (const AstCCall* const callp = VN_CAST(nodep, CCall))
                        return !callp->funcp()->dpiImportWrapper() || callp->funcp()->dpiContext();
                    return false;
                }))
                return false;
        }
        return !m_netlistp->exists([](const AstCFunc* funcp) {
            return funcp->dpiExportImpl() || funcp->dpiExportDispatcher();
        });
    }
    bool nativeConcurrentAllowed(const Plan& plan) const {
        // The first parallel proof is deliberately closed: every clocked reader
        // is in these kernels and no foreign or retained process observes NBA
        // state. Settling consumers remain behind dependency-visible joins.
        if (v3Global.opt.threads() <= 1
            || plan.m_partitions.size() != static_cast<size_t>(v3Global.opt.threads())
            || v3Global.opt.coverage() || v3Global.opt.vpi() || v3Global.opt.trace()
            || m_graph.m_report.m_nativeCycleBoundaries || !m_bindings.m_effectps.empty()
            || !m_bindings.m_callbacks.empty() || !m_bindings.m_contextps.empty()
            || !m_bindings.m_retainedps.empty())
            return false;
        for (const AstVarScope* const vscp : m_bindings.m_storageps) {
            const AstVar* const varp = vscp->varp();
            if (varp->isSc() || varp->isSigUserRdPublic() || varp->isSigUserRWPublic())
                return false;
        }
        for (const AstSenTree* const domainp : m_bindings.m_domainps) {
            const AstSenItem* const itemp = domainp->sensesp();
            if (!itemp || itemp->nextp() || itemp->condp()) return false;
            const AstVarRef* const refp = VN_CAST(itemp->sensp(), VarRef);
            if (!refp || !refp->varp()->isPrimaryIO() || !refp->varp()->isNonOutput()
                || refp->varp()->isSc() || refp->width() != 1)
                return false;
            if (itemp->edgeType() != VEdgeType::ET_POSEDGE
                && itemp->edgeType() != VEdgeType::ET_NEGEDGE)
                return false;
        }
        return !NativeStateObserverVisitor{m_netlistp}.hasObserver();
    }
    struct NativeKernel final {
        size_t m_domain = NO_ID;  // Sensitivity-domain index for this kernel
        std::string m_tag;  // Prefix for kernel functions and storage
        AstCFunc* m_funcp = nullptr;  // Native domain evaluation function
        AstCCall* m_callp = nullptr;  // Call carrying domain scheduling dependencies
        AstAlways* m_alwaysp = nullptr;  // Source-domain procedure invoking the kernel
        std::vector<AstCFunc*> m_parts;  // Per-partition compute entry points
        std::vector<size_t> m_sinks;  // Graph sinks evaluated by this domain
        std::set<AstVarScope*>
            m_candidateArgs;  // Candidate bindings exposed as dependency operands
        size_t m_ordinal = 0;  // Next ordinal for dependency operand names
    };
    void finishConcurrentKernels(const Plan& plan, std::vector<NativeKernel>& kernels) {
        using Reader = std::pair<size_t, size_t>;  // Domain, partition
        std::map<const AstVarScope*, Reader> readers;
        std::map<const AstVarScope*, size_t> writers;
        const std::set<const AstVarScope*> storageps{m_bindings.m_storageps.begin(),
                                                     m_bindings.m_storageps.end()};
        // Inspect actual lowered code, including predicates and bounded helper
        // calls. Graph replication counts do not prove physical read ownership.
        for (const NativeKernel& kernel : kernels) {
            for (const size_t id : kernel.m_sinks)
                ++writers[storage(m_graph.m_vertexps[id]->m_storage)];
            for (size_t part = 0; part < kernel.m_parts.size(); ++part) {
                const Reader reader{kernel.m_domain, part};
                std::set<AstCFunc*> seen;
                std::vector<AstCFunc*> pending{kernel.m_parts[part]};
                while (!pending.empty()) {
                    AstCFunc* const funcp = pending.back();
                    pending.pop_back();
                    if (!seen.insert(funcp).second) continue;
                    funcp->foreach([&](const AstVarRef* refp) {
                        if (!refp->access().isReadOrRW() || !storageps.count(refp->varScopep()))
                            return;
                        const auto result = readers.emplace(refp->varScopep(), reader);
                        if (result.first->second != reader)
                            result.first->second = Reader{NO_ID, NO_ID};
                    });
                    funcp->foreach([&](const AstCCall* callp) {
                        UASSERT_OBJ(callp->funcp()->isRepCut(), callp,
                                    "Unexpected callable in closed native partition");
                        pending.push_back(callp->funcp());
                    });
                }
            }
        }
        size_t published = 0;
        size_t blocked = 0;
        for (NativeKernel& kernel : kernels) {
            std::vector<std::vector<AstNodeStmt*>> bodies(kernel.m_parts.size());
            std::vector<std::map<AstVarScope*, AstIf*>> groups(kernel.m_parts.size());
            for (const size_t id : kernel.m_sinks) {
                const Vertex& vertex = *m_graph.m_vertexps[id];
                if (vertex.m_kind != Op::NEXT) continue;
                AstVarScope* const targetp = storage(vertex.m_storage);
                const size_t owner = plan.m_ownership.m_stateOwners[vertex.m_storage];
                const auto found = readers.find(targetp);
                if (writers.at(targetp) != 1
                    || (found != readers.end()
                        && found->second != Reader{kernel.m_domain, owner})) {
                    ++blocked;
                    continue;
                }
                UASSERT(owner == plan.m_ownership.m_sinkOwners[id],
                        "Scalar evaluation/publication owner mismatch");
                const Candidates& candidate = m_candidates[id];
                AstAssign* const assignp = new AstAssign{m_flp, ref(targetp, VAccess::WRITE),
                                                         ref(candidate.scalarValuep())};
                if (candidate.scalarEnablep()) {
                    AstIf*& ifp = groups[owner][candidate.scalarEnablep()];
                    if (!ifp) {
                        ifp = new AstIf{m_flp, ref(candidate.scalarEnablep()), nullptr};
                        bodies[owner].push_back(ifp);
                    }
                    ifp->addThensp(assignp);
                } else {
                    bodies[owner].push_back(assignp);
                }
                if (!m_sharedModules.count(targetp->scopep()->modp())) {
                    targetp->varp()->repcutStorageGroup(
                        storageGroup(owner, StorageRole::DIRECT_STATE));
                }
                nativeArgument(kernel.m_callp, targetp, true, kernel.m_ordinal++);
                m_directUpdates[id] = true;
                ++published;
            }
            for (size_t part = 0; part < kernel.m_parts.size(); ++part) {
                AstCFunc* funcp = kernel.m_parts[part];
                if (!bodies[part].empty()) {
                    const std::string tag = kernel.m_tag + "_local_p" + cvtToStr(part);
                    AstCFunc* const publishp = chunks(tag + "_publish", std::move(bodies[part]));
                    funcp = chunks(tag, {call(funcp), call(publishp)});
                    funcp->repcutLocalPublish(true);
                }
                m_phases[part][0] = funcp;
            }
            if (AstNodeStmt* const stmtp
                = parallelPhase(0, "repcut_native" + cvtToStr(kernel.m_domain)))
                kernel.m_funcp->addStmtsp(stmtp);
            kernel.m_funcp->repcutNativeBatch(kernels.size() > 1);
            kernel.m_sinks.erase(std::remove_if(kernel.m_sinks.begin(), kernel.m_sinks.end(),
                                                [&](size_t id) { return m_directUpdates[id]; }),
                                 kernel.m_sinks.end());
            finishNativeKernel(plan, kernel);
        }
        V3Stats::addStat("RepCut native concurrent, locally published scalars", published);
        V3Stats::addStat("RepCut native concurrent, blocked shared state", blocked);
    }
    void finishNativeKernel(const Plan& plan, NativeKernel& kernel) {
        const std::string& tag = kernel.m_tag;
        AstCCall* const callp = kernel.m_callp;
        AstAlways* const alwaysp = kernel.m_alwaysp;
        std::vector<size_t>& sinks = kernel.m_sinks;
        std::set<AstVarScope*>& candidateArgs = kernel.m_candidateArgs;
        size_t& ordinal = kernel.m_ordinal;
        std::sort(sinks.begin(), sinks.end(), [&](size_t a, size_t b) {
            const Vertex& lhs = *m_graph.m_vertexps[a];
            const Vertex& rhs = *m_graph.m_vertexps[b];
            return std::make_pair(lhs.m_storage, lhs.m_priority)
                   < std::make_pair(rhs.m_storage, rhs.m_priority);
        });
        AstAlwaysPost* const publicationp = nativePublication(plan, kernel.m_domain, sinks);
        std::map<AstVarScope*, AstIf*> writeGroups;
        for (const size_t sink : sinks) {
            const Vertex& vertex = *m_graph.m_vertexps[sink];
            const auto& candidate = m_candidates[sink];
            for (AstVarScope* const vscp : candidate.slots()) {
                if (vscp && candidateArgs.insert(vscp).second)
                    nativeArgument(callp, vscp, true, ordinal++);
            }
            if (publicationp && !storage(vertex.m_storage)->varp()->isSc()) continue;
            if (vertex.m_kind == Op::NEXT) {
                AstAssignDly* const assignp
                    = new AstAssignDly{m_flp, ref(storage(vertex.m_storage), VAccess::WRITE),
                                       ref(candidate.scalarValuep())};
                if (candidate.scalarEnablep()) {
                    // All scalar sinks have unique destinations. Their
                    // private values and enables are stable after the join,
                    // so coalesce publication under one test per write group.
                    AstIf*& ifp = writeGroups[candidate.scalarEnablep()];
                    if (!ifp) {
                        ifp = new AstIf{m_flp, ref(candidate.scalarEnablep()), nullptr};
                        alwaysp->addStmtsp(ifp);
                    }
                    ifp->addThensp(assignp);
                } else {
                    alwaysp->addStmtsp(assignp);
                }
            } else {
                UASSERT(vertex.m_kind == Op::MEMWRITE, "Non-pure native RepCut kernel");
                alwaysp->addStmtsp(new AstIf{
                    m_flp, ref(candidate.memoryEnablep()),
                    new AstAssignDly{m_flp, memoryTarget(sink), ref(candidate.memoryValuep())}});
            }
        }
        AstSenTree* const senp
            = const_cast<AstSenTree*>(m_bindings.m_domainps[kernel.m_domain])->cloneTree(false);
        AstActive* const activep = new AstActive{m_flp, tag, senp};
        activep->senTreeStorep(senp);
        activep->addProcsp(alwaysp);
        if (publicationp) activep->addProcsp(publicationp);
        m_scopep->addBlocksp(activep);
    }
    using NativeRoots = std::map<size_t, std::vector<size_t>>;
    struct NativeScheduleContext final {
        size_t m_releasedStates = 0;  // Number of private scalar states released early
        std::vector<size_t> m_visited;  // Visited generation tags indexed by graph node ID
        size_t m_generation = 0;  // Current generation for dependency-closure traversal
        size_t m_systemCCaptures = 0;  // Number of SystemC input captures created
        bool m_concurrent = false;  // Closed-model proof permits concurrent native kernels
        bool m_stagedBatch = false;  // Native kernels permit staged capture and batching
        bool m_releaseState = false;  // Old-state analysis permits early scalar state release
        bool m_batchDomains = false;  // Multiple native domains can share a batch dispatch
        std::vector<NativeSharedPartition>
            m_shared;  // Shared source drivers and values for each partition
        std::vector<std::map<size_t, std::vector<AstCFunc*>>> m_prologues;
        VNDeleter m_deleter;  // Deferred disposal of replaced scheduling nodes

        // Need () for sized vectors; braces can select initializer-list overloads.
        NativeScheduleContext(size_t vertices, size_t partitions)
            : m_visited(vertices, NO_ID)
            , m_shared(partitions)
            , m_prologues(partitions) {}
    };
    struct NativeDomainContext final {
        NativeKernel m_kernel;  // Kernel being emitted for the current domain
        const NativeRoots& m_roots;  // Graph roots grouped by sensitivity domain
        std::set<size_t> m_inputs;  // Input graph nodes consumed by this domain
        std::vector<size_t> m_effects;  // Effect sink IDs executed by this domain
        std::vector<size_t> m_callbacks;  // Callback sink IDs belonging to this domain
        std::vector<AstVarScope*>
            m_effectPendingps;  // Per-partition flags for pending caller-side effects

        NativeDomainContext(size_t id, const NativeRoots& roots)
            : m_roots{roots} {
            m_kernel.m_domain = id;
            m_kernel.m_tag = "__Vrepcut_native" + cvtToStr(id);
        }
    };

    void nativeSharedPrologues(const Plan& plan, NativeScheduleContext& ctx) {
        ctx.m_shared = nativeSharedPrograms(m_graph, plan, m_bindings, m_limit);
        uint32_t order = 0;
        for (size_t p = 0; p < ctx.m_shared.size(); ++p) {
            size_t ordinal = 0;
            for (NativeSharedGroup& group : ctx.m_shared[p].m_groups) {
                const std::string tag
                    = "__Vrepcut_shared_p" + cvtToStr(p) + "_g" + cvtToStr(ordinal++);
                AstCFunc* const funcp = chunks(tag, std::move(group.m_statements), false);
                funcp->repcutSharedOrder(++order);
                for (const size_t domain : group.m_domains)
                    ctx.m_prologues[p][domain].push_back(funcp);
            }
        }
    }
    // Preserve the planned closure order, including control predecessors.
    std::vector<size_t> nativeSequence(NativeScheduleContext& ctx, NativeDomainContext& domain,
                                       size_t p) {
        std::vector<size_t> sequence;
        const auto found = domain.m_roots.find(p);
        if (found != domain.m_roots.end()) {
            std::vector<std::pair<size_t, bool>> pending;
            for (const size_t sink : found->second) {
                const Op kind = m_graph.m_vertexps[sink]->m_kind;
                (kind == Op::CALL_CAPTURE ? domain.m_callbacks
                 : kind == Op::EFFECT     ? domain.m_effects
                                          : domain.m_kernel.m_sinks)
                    .push_back(sink);
                pending.emplace_back(sink, false);
                while (!pending.empty()) {
                    const auto item = pending.back();
                    pending.pop_back();
                    if (ctx.m_visited[item.first] == ctx.m_generation) continue;
                    if (item.second) {
                        ctx.m_visited[item.first] = ctx.m_generation;
                        sequence.push_back(item.first);
                        continue;
                    }
                    pending.emplace_back(item.first, true);
                    m_graph.m_vertexps[item.first]->foreachPredecessor(
                        [&](const Vertex& pred, DependencyKind) {
                            if (ctx.m_visited[pred.m_id] != ctx.m_generation)
                                pending.emplace_back(pred.m_id, false);
                            return false;
                        });
                }
            }
        }
        ++ctx.m_generation;
        return sequence;
    }
    void nativeInputs(NativeScheduleContext& ctx, NativeDomainContext& domain,
                      const std::vector<size_t>& sequence) {
        for (const size_t id : sequence) {
            const Vertex& vertex = *m_graph.m_vertexps[id];
            if (vertex.m_kind == Op::INPUT || vertex.m_kind == Op::OLD
                || vertex.m_kind == Op::OLDMEM || vertex.m_kind == Op::INIT
                || vertex.m_kind == Op::EXTERNAL) {
                const size_t input = vertex.m_storage;
                const AstVarScope* const sourcep = storage(input);
                if (domain.m_inputs.insert(input).second && sourcep->varp()->isSc()) {
                    // Convert ports through ordinary assignment lowering on
                    // the caller. Workers and dependency arguments then use
                    // plain values, without accessing the SystemC kernel.
                    AstVarScope* const capturep = v3Global.rootp()->topScopep()->createTemp(
                        domain.m_kernel.m_tag + "_sc" + cvtToStr(input), sourcep->dtypep());
                    capturep->varp()->noReset(true);
                    capturep->varp()->noSubst(true);
                    capturep->varp()->trace(false);
                    capturep->varp()->isInternal(true);
                    m_nativeInputps.emplace(input, capturep);
                    ++ctx.m_systemCCaptures;
                }
            }
        }
    }
    void nativeReleaseState(NativeScheduleContext& ctx, const NativeDomainContext& domain,
                            size_t p, const std::vector<AstNodeStmt*>& statements) {
        const auto found = domain.m_roots.find(p);
        UASSERT(found != domain.m_roots.end(), "Missing single-partition domain");
        std::map<AstVarScope*, AstVarScope*> destinations;
        for (const size_t id : found->second) {
            const Vertex& vertex = *m_graph.m_vertexps[id];
            if (vertex.m_kind == Op::NEXT)
                destinations.emplace(m_candidates[id].scalarValuep(), storage(vertex.m_storage));
        }
        const std::set<AstVarScope*> released
            = releaseGuardedStateCandidates(statements, destinations);
        for (const size_t id : found->second) {
            if (released.count(m_candidates[id].scalarValuep())) {
                m_directUpdates[id] = true;
                ++ctx.m_releasedStates;
            }
        }
    }
    void nativePartition(NativeScheduleContext& ctx, NativeDomainContext& domain, size_t p,
                         const std::vector<size_t>& sequence) {
        m_storageGroup
            = v3Global.opt.threads() > 1 ? storageGroup(p, StorageRole::PRIVATE_EVAL) : 0;
        const std::string partitionTag = domain.m_kernel.m_tag + "_p" + cvtToStr(p);
        AstVarScope* effectPendingp = nullptr;
        if (std::any_of(sequence.begin(), sequence.end(),
                        [&](size_t id) { return m_graph.m_vertexps[id]->m_kind == Op::EFFECT; })) {
            // Each domain invocation clears its own partition-local flag.
            // Serial kernels complete before the caller scans effects;
            // parallel kernels publish it through the compute join.
            effectPendingp = temp(partitionTag + "_effect_pending", 1, false);
            effectPendingp->varp()->noSubst(true);
            domain.m_effectPendingps.push_back(effectPendingp);
        }
        std::vector<AstNodeStmt*> statements;
        size_t graphIsland = 0;
        const NativeGraphLower lowerGraph
            = [&](const std::vector<size_t>& graphSequence, const NativeGraphBoundary& boundary) {
                  return evaluationStatements(partitionTag + "__graph" + cvtToStr(graphIsland++),
                                              graphSequence, effectPendingp, &boundary);
              };
        const NativeProgramContext context{*m_scopep,
                                           m_graph,
                                           m_bindings,
                                           sequence,
                                           partitionTag,
                                           m_storageGroup,
                                           m_limit,
                                           m_nativeInputps,
                                           effectPendingp,
                                           lowerGraph,
                                           ctx.m_shared[p].m_values};
        NativeProgramOutput output{m_candidates, m_effectArguments, statements};
        const NativeLowering lowering = nativeProgram(context, output);
        if (lowering != NativeLowering::GRAPH) {
            std::set<AstVarScope*> preserve;
            if (effectPendingp) preserve.insert(effectPendingp);
            for (const size_t id : sequence) {
                if (!m_graph.m_vertexps[id]->isSink()) continue;
                for (AstVarScope* const vscp : m_candidates[id].slots()) {
                    if (vscp) preserve.insert(vscp);
                }
                preserve.insert(m_effectArguments[id].begin(), m_effectArguments[id].end());
            }
            m_copies += eliminateCopies(statements, preserve);
            substituteLocalExpressions(statements, preserve, expressionLimit());
            if (v3Global.opt.fMergeCond()) V3MergeCond::mergeScoped(statements);
            if (ctx.m_releaseState) nativeReleaseState(ctx, domain, p, statements);
            m_phases[p][0] = chunks(partitionTag, std::move(statements));
        } else {
            m_phases[p][0] = chunks(partitionTag,
                                    evaluationStatements(partitionTag, sequence, effectPendingp));
        }
        const auto prefix = ctx.m_prologues[p].find(domain.m_kernel.m_domain);
        if (prefix != ctx.m_prologues[p].end()) {
            // These calls are correct even before batching: the domain
            // computes its complete pure prefix before its private body.
            // NativeBatch factors the repeated helpers under trigger
            // unions and moves them ahead of this worker's domain calls.
            std::vector<AstNodeStmt*> calls;
            for (AstCFunc* const funcp : prefix->second) calls.push_back(call(funcp));
            calls.push_back(call(m_phases[p][0]));
            m_phases[p][0] = chunks(partitionTag + "_shared", std::move(calls));
        }
        if (m_nativeCostReportp) {
            // Count the partition entry and its bounded helper calls
            // once. This follows local rewrites,
            // but precedes native scheduling and final C++ lowering.
            *m_nativeCostReportp << partitionTag << '\t'
                                 << (lowering == NativeLowering::GRAPH    ? "graph"
                                     : lowering == NativeLowering::SOURCE ? "source"
                                                                          : "hybrid")
                                 << '\t' << sequence.size() << '\t'
                                 << V3InstrCount::count(m_phases[p][0], false) << '\n';
        }
    }
    void nativeDispatch(const NativeScheduleContext& ctx, NativeDomainContext& domain) {
        m_storageGroup = 0;
        std::vector<AstNodeStmt*> dispatches;
        if (!ctx.m_concurrent) {
            if (AstNodeStmt* const stmtp
                = parallelPhase(0, "repcut_native" + cvtToStr(domain.m_kernel.m_domain)))
                dispatches.push_back(stmtp);
        }
        domain.m_kernel.m_funcp
            = chunks(domain.m_kernel.m_tag + "_evaluate", std::move(dispatches));
        domain.m_kernel.m_funcp->entryPoint(false);
        domain.m_kernel.m_funcp->funcPublic(false);
        domain.m_kernel.m_funcp->isLoose(true);
        domain.m_kernel.m_funcp->repcutDependencyArgs(true);
        domain.m_kernel.m_funcp->repcutNativeBatch(ctx.m_batchDomains);
        domain.m_kernel.m_callp = new AstCCall{m_flp, domain.m_kernel.m_funcp};
        domain.m_kernel.m_callp->dtypeSetVoid();
        for (const size_t input : domain.m_inputs)
            nativeArgument(domain.m_kernel.m_callp, inputStorage(input), false,
                           domain.m_kernel.m_ordinal++);
        for (const size_t id : domain.m_kernel.m_sinks) {
            if (m_directUpdates[id])
                nativeArgument(domain.m_kernel.m_callp, storage(m_graph.m_vertexps[id]->m_storage),
                               true, domain.m_kernel.m_ordinal++);
        }
        domain.m_kernel.m_sinks.erase(
            std::remove_if(domain.m_kernel.m_sinks.begin(), domain.m_kernel.m_sinks.end(),
                           [&](size_t id) { return m_directUpdates[id]; }),
            domain.m_kernel.m_sinks.end());
        domain.m_kernel.m_alwaysp = new AstAlways{m_flp, VAlwaysKwd::ALWAYS, nullptr, nullptr};
        for (const auto& capture : m_nativeInputps) {
            domain.m_kernel.m_alwaysp->addStmtsp(new AstAssign{
                m_flp, ref(capture.second, VAccess::WRITE), ref(storage(capture.first))});
        }
        domain.m_kernel.m_alwaysp->addStmtsp(domain.m_kernel.m_callp->makeStmt());
    }
    // Keep foreign bodies on the caller after their captured arguments are ready.
    void nativeCallbacks(NativeScheduleContext& ctx, NativeDomainContext& domain) {
        std::map<size_t, std::map<size_t, AstVarScope*>> callbackInputs;
        for (const size_t id : domain.m_callbacks) {
            const Vertex& vertex = *m_graph.m_vertexps[id];
            UASSERT(m_effectArguments[id].size() == 1, "Non-scalar native callback capture");
            AstVarScope* const valuep = m_effectArguments[id][0];
            callbackInputs[vertex.m_aux].emplace(vertex.m_priority, valuep);
            nativeArgument(domain.m_kernel.m_callp, valuep, true, domain.m_kernel.m_ordinal++);
        }
        for (const auto& callback : callbackInputs) {
            const Callback& binding = m_bindings.m_callbacks.at(callback.first);
            std::map<const AstVarScope*, AstVarScope*> captures;
            AstNodeStmt* packingp = nullptr;
            size_t argument = 0;
            for (size_t i = 0; i < binding.m_inputps.size(); ++i) {
                const AstVarScope* const inputp = binding.m_inputps[i];
                if (const AstUnpackArrayDType* const dtypep
                    = VN_CAST(inputp->dtypep()->skipRefp(), UnpackArrayDType)) {
                    AstVarScope* const arrayp = v3Global.rootp()->topScopep()->createTemp(
                        domain.m_kernel.m_tag + "_callback" + cvtToStr(callback.first) + "_array"
                            + cvtToStr(i),
                        inputp->dtypep());
                    arrayp->varp()->noReset(true);
                    arrayp->varp()->trace(false);
                    arrayp->varp()->isInternal(true);
                    captures.emplace(inputp, arrayp);
                    for (int index = 0; index < dtypep->elementsConst(); ++index) {
                        AstVarScope* const valuep = callback.second.at(argument++);
                        packingp = AstNode::addNextNull(
                            packingp,
                            new AstAssign{
                                m_flp, new AstArraySel{m_flp, ref(arrayp, VAccess::WRITE), index},
                                ref(valuep)});
                    }
                } else {
                    AstVarScope* const valuep = callback.second.at(argument++);
                    captures.emplace(inputp, valuep);
                }
            }
            UASSERT(argument == callback.second.size(), "Callback argument mismatch");
            // Clocked reads in separate processes describe old state and
            // do not order a consumer after a same-edge capture write.
            // Keep the original callback body in this process after the
            // compute join, including array packing, guards, blocking
            // temporaries and NBAs. The native scheduler still sees all
            // callback dependencies, and foreign calls stay on the caller.
            AstAlways* const callbackp = m_bindings.m_nativeCallbackps.at(callback.first);
            callbackp->foreach([&](AstVarRef* refp) {
                const auto found = captures.find(refp->varScopep());
                if (found == captures.end()) return;
                UASSERT_OBJ(refp->access().isReadOnly(), refp, "Writable callback input");
                refp->varScopep(found->second);
                refp->varp(found->second->varp());
            });
            if (packingp) domain.m_kernel.m_alwaysp->addStmtsp(packingp);
            domain.m_kernel.m_alwaysp->addStmtsp(callbackp->stmtsp()->unlinkFrBackWithNext());
            ctx.m_deleter.pushDeletep(callbackp->unlinkFrBack());
        }
    }
    void nativeEffects(NativeDomainContext& domain) {
        std::vector<AstNodeStmt*> effectStatements;
        std::sort(domain.m_effects.begin(), domain.m_effects.end(), [&](size_t a, size_t b) {
            return m_graph.m_vertexps[a]->m_aux < m_graph.m_vertexps[b]->m_aux;
        });
        for (const size_t id : domain.m_effects) {
            // Effect bodies run only on the caller. Both activation and
            // arguments are captured by their unique partition owner.
            for (AstVarScope* const vscp : m_effectArguments[id]) {
                if (domain.m_kernel.m_candidateArgs.insert(vscp).second)
                    nativeArgument(domain.m_kernel.m_callp, vscp, true,
                                   domain.m_kernel.m_ordinal++);
            }
            AstVarScope* const enabledp = m_candidates[id].effectEnablep();
            if (domain.m_kernel.m_candidateArgs.insert(enabledp).second)
                nativeArgument(domain.m_kernel.m_callp, enabledp, true,
                               domain.m_kernel.m_ordinal++);
            effectStatements.push_back(effectStatement(*m_graph.m_vertexps[id]));
        }
        if (!domain.m_effectPendingps.empty()) {
            // Keep the ordered scan in bounded functions. Only the scan is
            // conditional: state publication must run even without effects.
            AstCFunc* const effectsp
                = chunks(domain.m_kernel.m_tag + "_effects", std::move(effectStatements));
            effectsp->entryPoint(false);
            effectsp->funcPublic(false);
            effectsp->isLoose(true);
            effectsp->repcutDependencyArgs(true);
            AstCCall* const effectCallp = new AstCCall{m_flp, effectsp};
            effectCallp->dtypeSetVoid();
            size_t effectOrdinal = 0;
            // Use effect/source order, never pointer order, for arguments.
            std::set<AstVarScope*> added;
            for (const size_t id : domain.m_effects) {
                for (AstVarScope* const vscp : m_effectArguments[id]) {
                    if (added.insert(vscp).second)
                        nativeArgument(effectCallp, vscp, false, effectOrdinal++);
                }
                AstVarScope* const enabledp = m_candidates[id].effectEnablep();
                if (added.insert(enabledp).second)
                    nativeArgument(effectCallp, enabledp, false, effectOrdinal++);
            }
            AstNodeExpr* pendingp = nullptr;
            for (AstVarScope* const vscp : domain.m_effectPendingps) {
                nativeArgument(domain.m_kernel.m_callp, vscp, true, domain.m_kernel.m_ordinal++);
                if (pendingp) {
                    pendingp = new AstOr{m_flp, pendingp, ref(vscp)};
                } else {
                    pendingp = ref(vscp);
                }
            }
            AstIf* const ifp = new AstIf{m_flp, pendingp, effectCallp->makeStmt()};
            ifp->branchPred(VBranchPred::BP_UNLIKELY);
            domain.m_kernel.m_alwaysp->addStmtsp(ifp);
            V3Stats::addStatSum("RepCut native, effect pending flags",
                                domain.m_effectPendingps.size());
            V3Stats::addStatSum("RepCut native, guarded effect scans", 1);
        } else {
            for (AstNodeStmt* const stmtp : effectStatements)
                domain.m_kernel.m_alwaysp->addStmtsp(stmtp);
        }
        V3Stats::addStatSum("RepCut native, captured effects", domain.m_effects.size());
    }
    void nativeSchedule(const Plan& plan) {
        // Equivalent sensitivities share one native process and one closure per
        // partition. The scheduler decides when it runs; candidate publication
        // uses ordinary HDL NBAs or a dependency-visible native POST dispatch.
        // Pure data/control cones retain fine nodes and partition membership.
        std::map<size_t, NativeRoots> roots;
        for (size_t p = 0; p < plan.m_partitions.size(); ++p) {
            for (const size_t id : plan.m_partitions[p].m_next) {
                const Vertex& vertex = *m_graph.m_vertexps[id];
                if (vertex.isSink()) roots[vertex.m_domain][p].push_back(id);
            }
        }
        NativeScheduleContext ctx{m_graph.m_vertexps.size(), plan.m_partitions.size()};
        ctx.m_concurrent = nativeConcurrentAllowed(plan);
        V3Stats::addStat("RepCut native concurrent, eligible", ctx.m_concurrent);
        ctx.m_stagedBatch = !ctx.m_concurrent && nativeStagedBatchAllowed(plan);
        V3Stats::addStat("RepCut native staged batch, eligible", ctx.m_stagedBatch);
        ctx.m_batchDomains = ctx.m_stagedBatch && roots.size() > 1;
        if (ctx.m_batchDomains) nativeSharedPrologues(plan, ctx);
        // A serial batch only pays off when it can reuse a common prefix.
        if (v3Global.opt.threads() == 1 && ctx.m_shared.front().m_groups.empty())
            ctx.m_batchDomains = false;
        std::vector<NativeKernel> kernels;
        ctx.m_releaseState = nativeStateReleaseAllowed(plan);
        V3Stats::addStat("RepCut native direct-state, eligible", ctx.m_releaseState);
        for (const auto& entry : roots) {
            NativeDomainContext domain{entry.first, entry.second};
            m_nativeInputps.clear();
            for (size_t p = 0; p < plan.m_partitions.size(); ++p) {
                const std::vector<size_t> sequence = nativeSequence(ctx, domain, p);
                nativeInputs(ctx, domain, sequence);
                nativePartition(ctx, domain, p, sequence);
            }
            nativeDispatch(ctx, domain);
            nativeCallbacks(ctx, domain);
            nativeEffects(domain);
            for (const auto& phases : m_phases) domain.m_kernel.m_parts.push_back(phases[0]);
            if (ctx.m_concurrent) {
                kernels.push_back(std::move(domain.m_kernel));
            } else {
                finishNativeKernel(plan, domain.m_kernel);
            }
        }
        if (ctx.m_concurrent) finishConcurrentKernels(plan, kernels);
        m_nativeInputps.clear();
        size_t instrumented = 0;
        for (AstAlways* const alwaysp : m_bindings.m_clockedps) {
            if (alwaysp->exists([](const AstCoverInc*) { return true; })) {
                AstAlways* const coveragep = alwaysp->cloneTree(false);
                NativeCoverageVisitor{coveragep};
                alwaysp->replaceWith(coveragep);
                ctx.m_deleter.pushDeletep(alwaysp);
                ++instrumented;
            } else {
                ctx.m_deleter.pushDeletep(alwaysp->unlinkFrBack());
            }
        }
        V3Stats::addStat("RepCut native, domains", roots.size());
        V3Stats::addStat("RepCut native, directly updated scalars", ctx.m_releasedStates);
        V3Stats::addStat("RepCut native, SystemC input captures", ctx.m_systemCCaptures);
        V3Stats::addStat("RepCut native, instrumented procedures", instrumented);
        V3Stats::addStat("RepCut native, replaced procedures", m_bindings.m_clockedps.size());
        V3Stats::addStat("RepCut emit, functions", m_functions);
    }
    AstNodeStmt* effectStatement(const Vertex& vertex) {
        AstNodeStmt* const stmtp
            = const_cast<AstNodeStmt*>(m_bindings.m_effectps.at(vertex.m_aux))->cloneTree(false);
        if (const AstDisplay* const displayp = VN_CAST(stmtp, Display)) {
            size_t index = 0;
            for (AstNodeExpr* argp = displayp->fmtp()->exprsp(); argp;) {
                AstNodeExpr* const nextp = VN_AS(argp->nextp(), NodeExpr);
                const AstConst* const cp = VN_CAST(argp, Const);
                if (!cp || !cp->num().isString()) {
                    argp->replaceWith(ref(m_effectArguments[vertex.m_id].at(index++)));
                    VL_DO_DANGLING(argp->deleteTree(), argp);
                }
                argp = nextp;
            }
            if (AstNodeExpr* const filep = displayp->filep()) {
                filep->replaceWith(ref(m_effectArguments[vertex.m_id].at(index++)));
                VL_DO_DANGLING(filep->deleteTree(), filep);
            }
            UASSERT_OBJ(index == m_effectArguments[vertex.m_id].size(), stmtp,
                        "RepCut effect argument binding mismatch");
        }
        return new AstIf{m_flp, ref(m_candidates[vertex.m_id].effectEnablep()), stmtp};
    }

public:
    // Need () for sized vectors: braces can select initializer-list overloads
    // and create elements containing the sizes instead of one slot per vertex.
    Emitter(AstNetlist* netlistp, const Graph& graph, const Plan& plan, const Bindings& bindings)
        : m_netlistp{netlistp}
        , m_graph{graph}
        , m_bindings{bindings}
        , m_scopep{netlistp->topScopep()->scopep()}
        , m_flp{netlistp->fileline()}
        , m_values(graph.m_vertexps.size(), nullptr)
        , m_expressions(graph.m_vertexps.size(), nullptr)
        , m_uses(graph.m_vertexps.size())
        , m_consumers(graph.m_vertexps.size())
        , m_expressionSizes(graph.m_vertexps.size())
        , m_regionDepth(graph.m_regions.size())
        , m_directUpdates(graph.m_vertexps.size())
        , m_candidates(graph.m_vertexps.size())
        , m_effectArguments(graph.m_vertexps.size())
        , m_phases(plan.m_partitions.size()) {
        UASSERT(bindings.m_storageps.size() == graph.m_storage.size(),
                "Missing live RepCut bindings");
        // A shared class field can have a different worker owner in each instance.
        // Only singleton modules can encode that ownership in their field layout.
        std::unordered_set<const AstNodeModule*> modules;
        netlistp->foreach([&](const AstScope* scopep) {
            if (!modules.emplace(scopep->modp()).second) m_sharedModules.emplace(scopep->modp());
        });
        if (v3Global.opt.debugSelfTest()) {
            selfTestCopies(*m_scopep);
            selfTestStateRelease(*m_scopep);
            selfTestSelections(*m_scopep);
            selfTestProgram(*m_scopep);
            selfTestLocalExpressions(*m_scopep);
            SharedPhase::selfTest();
            selfTestChunks(*m_scopep);
        }
        for (size_t i = 0; i < graph.m_regions.size(); ++i) {
            const size_t parent = graph.m_regions[i].m_parent;
            m_regionDepth[i] = parent == NO_ID ? 1 : m_regionDepth[parent] + 1;
        }
        if (v3Global.opt.repcutDumpGraph()) {
            m_nativeCostReportp.reset(V3File::new_ofstream(v3Global.opt.makeDir() + "/"
                                                           + v3Global.opt.prefix()
                                                           + "__repcut_early.native-costs.tsv"));
            if (m_nativeCostReportp->fail()) v3fatal("Cannot write RepCut native cost report");
            *m_nativeCostReportp << "partition\tlowering\tgraph_nodes\tinstruction_estimate\n";
            const std::string base
                = v3Global.opt.makeDir() + "/" + v3Global.opt.prefix() + "__repcut_early";
            m_reportp.reset(V3File::new_ofstream(base + ".chunks.tsv"));
            m_cutReportp.reset(V3File::new_ofstream(base + ".cuts.tsv"));
            if (m_reportp->fail()) v3fatal("Cannot write RepCut chunk report");
            if (m_cutReportp->fail()) v3fatal("Cannot write RepCut boundary report");
            m_publicationReportp.reset(V3File::new_ofstream(v3Global.opt.makeDir() + "/"
                                                            + v3Global.opt.prefix()
                                                            + "__repcut_early.publication.tsv"));
            if (m_publicationReportp->fail()) v3fatal("Cannot write RepCut publication report");
            *m_publicationReportp << "domain\towner\tscalars\tmemory_ports\tcopy_work\tguard_work"
                                     "\towner_work\tserial_work\tmax_owner_work\tdispatch_work"
                                     "\tmargin_work\tmode\tdecision\treason\n";
            *m_reportp << "function\tbody_nodes\tentry\n";
            *m_cutReportp << "group\tfunction\tboundary\tprefix_nodes\tlive_values\tlive_bytes"
                             "\tgreedy_cut\tselected_cut\tanalyzed\n";
        }
        nativeSchedule(plan);
        // Normalize only the functions RepCut created; the retained native netlist must
        // keep its own form untouched.
        for (AstCFunc* const funcp : m_createdFuncps) RepCutTwoState{funcp};
    }
};

}  // namespace
void emit(AstNetlist* netlistp, const Graph& graph, const Plan& plan, const Bindings& bindings) {
    Emitter{netlistp, graph, plan, bindings};
}
void removeDependencyArgs(AstNetlist* netlistp) {
    NativeDependencyVisitor{netlistp};
    V3Global::dumpCheckGlobalTree("repcut_dependencies", 0, dumpTreeEitherLevel() >= 3);
}
}  // namespace V3RepCut
