// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit structural (primitive-netlist) Verilog
//
// Port of the System-Verilog-suite "structural" backend
// (sv_parse.ml -> sv_transform.ml -> sv_tran_struct.ml -> sv_gen.ml and
// the sv_gen_xilinx_rtl.ml relabeling pass) onto Verilator's own AST.
//
// Process flow, per module, in this order:
//
//   1. Declaration pass.  Every AstVar becomes a port / localparam / wire
//      declaration.  Indexed generate scopes ("blk[3]") prefix the names
//      they declare, exactly like sv_parse.qualify_genblock.  Unpacked
//      arrays above the 128-bit threshold are memory candidates
//      (sv_memory.detect_memories); smaller ones are split into one
//      register per element.
//   2. Lowering pass.  Continuous assigns and always blocks are lowered
//      by symbolic execution: every expression node becomes a primitive
//      cell (adder, bitwise_and, mux2, ...) driving a fresh wire_N, and a
//      per-block environment tracks blocking (=) and non-blocking (<=)
//      values so that if/case become mux2 trees (sv_tran_struct
//      structural_if_as_mux / structural_case) and loops are unrolled
//      with constant-folded induction variables (sv_transform
//      unroll_for_loop).  Function and task calls are inlined
//      (sv_transform inline_function / inline_task).  An always block is
//      classified purely from its sensitivity list and the body's
//      top-level if/else-if reset chain (sv_tran_struct
//      classify_always_block); each register becomes a dff_en / dffn_en
//      cell, with `if (en) q <= d` folded onto the EN pin.
//   3. Memory primitives.  Memory candidates with recorded read/write
//      ports become memory_sp / memory_1w2r / memory_2w2r instances.
//   4. Dead-cell elimination (sv_tran_struct.module_dce): primitive cells
//      and assigns whose outputs nobody consumes are dropped to a fixed
//      point, then orphaned wire declarations.
//   5. Optional Vivado RTL_* relabeling (sv_gen_xilinx_rtl).
//   6. Text emission (sv_gen.generate_sv for a Netlist of structural
//      modules).
//
// Everything is streamed one module at a time with O(module) scratch
// state, which is the point of the exercise: the old path dumped the full
// --json-only tree to disk (hundreds of MB for a core) and then rebuilt
// it twice in OCaml (Yojson tree + sv_ast + the transformed copy).
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3EmitStruct.h"
#include "verilated_config.h"  // VERILATOR_VERSION_INTEGER
#include "V3Os.h"

#include "V3Global.h"

#include <algorithm>
#include <fstream>
#include <unistd.h>
#include <iomanip>
#include <map>
#include <memory>
#include <set>
#include <sstream>
#include <unordered_map>
#include <unordered_set>
#include <vector>

// Verilator after 5.050 splits VL_RESTORER (trivially copyable only) from
// VL_RESTORER_COPY; the same source builds against both
#ifndef VL_RESTORER_COPY
#define VL_RESTORER_COPY(var) VL_RESTORER(var)
#endif

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

//######################################################################
// Small value types

// A lowered expression: a piece of Verilog text (an identifier, a literal,
// or a bit/part select on an identifier) plus what we know about it.
struct SExpr final {
    std::string text;  // Verilog expression text
    int width = 1;  // bit width
    bool isIdent = false;  // plain identifier (wire or variable name)
    bool isConst = false;  // literal
    bool hasVal = false;  // constant value known (width <= 64, no X/Z)
    uint64_t val = 0;  // value when hasVal (masked to width)
    bool isSigned = false;
    std::vector<std::string> refs;  // identifiers read by this expression
};

struct SPin final {
    std::string name;
    std::string expr;
};

// One emitted module item: a primitive cell, a user-module instance, an
// assign, or a comment line.
struct SItem final {
    enum Kind : uint8_t { CELL, USERCELL, ASSIGN, COMMENT };
    Kind kind = CELL;
    std::string prim;  // primitive / module name
    std::string inst;  // instance name
    std::vector<std::pair<std::string, std::string>> params;
    std::vector<SPin> pins;
    std::string lhs;  // ASSIGN
    std::string rhs;  // ASSIGN
    std::vector<std::string> reads;  // identifiers consumed
    std::vector<std::string> writes;  // identifiers driven (root names)
    bool keep = false;  // never removed by DCE (memories, user cells)
    std::string text;  // COMMENT
};

struct SDecl final {
    std::string name;
    int width = 1;
    bool isSigned = false;
    std::string unpacked;  // " [0:3]" for array-typed nets kept as arrays
    VDirection dir;  // NONE for internal
    bool isParam = false;
    std::string paramValue;
};

// A lowered assignment target
struct SLVal final {
    bool ok = false;
    std::string key;  // environment key ("x", "x[4+:4]", "mem__3")
    std::string text;  // Verilog lvalue text
    int width = 1;
    std::vector<std::string> refs;  // identifiers read by the lvalue (indexes)
    // Memory element write (big memory)
    const AstVar* memVarp = nullptr;
    SExpr idx;
    bool memDynamic = false;  // small array with dynamic index
    const AstVar* memSmallVarp = nullptr;
    bool sliceDynamic = false;  // vector[idx +: w] with a non-constant idx
    std::string baseKey;  // sliceDynamic: the vector's key
    int baseWidth = 0;  // sliceDynamic: the vector's width
};

// Memory candidate (sv_memory.memory_info)
struct SMem final {
    std::string name;
    int depth = 0;
    int dataWidth = 0;
    int addrWidth = 0;
    int lo = 0;  // lowest declared index
    bool asRegs = false;  // below threshold: one register per element
    std::vector<std::string> regNames;  // asRegs: element wire names
    std::vector<SExpr> readIdx;  // primitive: read ports (dedup by index text)
    struct Write final {
        SExpr idx, data, en, clk;
    };
    std::vector<Write> writes;  // primitive: write ports
    bool anyWrite = false;
    std::string initFile;  // $readmemh file from an initial block
    std::vector<uint64_t> initWords;  // `initial mem[i] = CONST;` image
    bool hasInitWords = false;
    SExpr clk;  // clock of the block(s) accessing it
    struct SyncRead final {  // read port absorbed into a BRAM output register
        bool used = false;
        SExpr en;
        std::string q;
        std::vector<std::string> qRefs;
        SExpr clk;
    };
    std::vector<SyncRead> sync;
};
// A register whose D came straight from a memory read port: kept aside so it
// can be re-emitted if the memory cannot be made synchronous after all.
struct SDeferredDff final {
    std::string q;
    std::vector<std::string> qRefs;
    SExpr d, en, clk;
    int width;
    bool negedge;
};

// Per-block symbolic-execution environment (sv_transform SSA + the
// sv_tran_struct block_substitutions map, generalised).
struct Env final {
    std::map<std::string, SExpr> cur;  // key -> value visible to later reads
    std::map<std::string, SExpr> next;  // key -> value driven at block end
    std::vector<std::string> order;  // insertion order of `next` keys
    bool halted = false;  // a JumpGo ended this path
    const AstJumpBlock* haltTarget = nullptr;
    struct Pending final {
        SExpr cond;  // condition under which this snapshot applies
        const AstJumpBlock* target;
        std::shared_ptr<Env> env;
    };
    std::vector<Pending> pending;  // halted alternative paths still to fold

    void setNext(const std::string& key, const SExpr& v) {
        if (!next.count(key)) order.push_back(key);
        next[key] = v;
    }
};

std::string sanitizeName(const std::string& s) {
    std::string out;
    out.reserve(s.size());
    for (const char c : s) {
        if (std::isalnum(static_cast<unsigned char>(c)) || c == '_' || c == '$') {
            out += c;
        } else {
            out += '_';
        }
    }
    if (out.empty()) out = "_";
    if (std::isdigit(static_cast<unsigned char>(out[0]))) out = "_" + out;
    return out;
}

uint64_t maskTo(uint64_t v, int width) {
    if (width >= 64) return v;
    if (width <= 0) return 0;
    return v & ((1ULL << width) - 1ULL);
}

int64_t signExt(uint64_t v, int width) {
    if (width >= 64 || width <= 0) return static_cast<int64_t>(v);
    const uint64_t sign = 1ULL << (width - 1);
    if (v & sign) return static_cast<int64_t>(v | ~((sign << 1) - 1ULL));
    return static_cast<int64_t>(v);
}

std::string constText(uint64_t v, int width) {
    if (width == 1) return v ? "1'b1" : "1'b0";
    std::ostringstream os;
    os << width << "'h" << std::hex << maskTo(v, width);
    return os.str();
}

//######################################################################
// Per-module lowering

class StructModule final {
    // STATE
    AstNodeModule* const m_modp;
    const bool m_xilinx;
    const bool m_wideMem;
    const bool m_report;
    std::vector<SDecl> m_decls;  // declared vars/ports/params (source order)
    std::vector<SDecl> m_wires;  // generated wires
    std::vector<SItem> m_items;
    std::vector<std::string> m_warnings;
    std::unordered_map<std::string, int> m_widths;  // identifier -> width
    std::unordered_map<const AstVar*, std::string> m_varName;
    std::unordered_map<const AstVar*, SMem> m_mems;
    std::unordered_set<const AstVar*> m_declared;
    std::unordered_set<std::string> m_declNames;
    std::unordered_map<const AstVar*, SExpr> m_bind;  // function formals -> value
    std::unordered_map<const AstVar*, SLVal> m_alias;  // task output formals -> lvalue
    std::unordered_map<const AstVar*, std::string> m_localKey;  // inlined locals
    int m_counter = 0;
    int m_inlineDepth = 0;
    int m_callSeq = 0;
    int m_alwaysSeq = 0;
    std::string m_genPrefix;
    // mux bookkeeping for enable / reset-value folding
    struct MuxInfo final {
        SExpr sel, in0, in1;
    };
    std::unordered_map<std::string, MuxInfo> m_muxes;
    std::unordered_map<std::string, std::pair<const AstVar*, size_t>> m_readPorts;  // rdata ident -> (mem, port)
    std::vector<SDeferredDff> m_deferred;
    // Procedural context
    bool m_seq = false;
    bool m_latch = false;
    SExpr m_clk;
    bool m_negedge = false;
    bool m_hasRst = false;
    bool m_rstAsync = false;
    SExpr m_rst;  // lowered reset predicate (active-high)
    const AstVar* m_rstVarp = nullptr;
    AstNodeExpr* m_rstCondp = nullptr;
    std::vector<std::pair<SExpr, bool>> m_pathCond;  // (cond, negated)
    std::vector<const AstJumpBlock*> m_jumpStack;
    std::vector<std::pair<std::string, int>> m_regsInBlock;

    static constexpr int MEMORY_THRESHOLD_BITS = 128;  // sv_memory.memory_threshold
    static constexpr int MAX_UNROLL = 1024;  // sv_transform.max_unroll_iterations
    static constexpr int MAX_INLINE_DEPTH = 16;
    static constexpr int MAX_SLICE_SLOTS = 32;  // dynamic slice writes expanded to per-slot enables up to this

public:
    StructModule(AstNodeModule* modp, bool xilinx, bool wideMem, bool report)
        : m_modp{modp}
        , m_xilinx{xilinx}
        , m_wideMem{wideMem}
        , m_report{report} {}

    void run(std::ostream& os) {
        declarePass(m_modp->stmtsp());
        lowerPass(m_modp->stmtsp());
        emitMemories();
        fillStaticInits();
        dce();
        if (m_xilinx) xilinxRelabel();
        print(os);
    }

private:
    // ---- diagnostics ----
    void warn(const std::string& msg) {
        m_warnings.push_back(msg);
        UINFO(4, "struct warning: " << msg);
    }
    void warnNode(const AstNode* nodep, const std::string& msg) {
        warn(msg + " (" + nodep->prettyTypeName() + " at " + nodep->fileline()->ascii() + ")");
    }

    // ---- naming ----
    std::string newName(const std::string& prefix) {
        ++m_counter;
        return prefix + "_" + std::to_string(m_counter);
    }
    std::string varName(const AstVar* varp) {
        const auto it = m_varName.find(varp);
        if (it != m_varName.end()) return it->second;
        const auto lit = m_localKey.find(varp);
        if (lit != m_localKey.end()) return lit->second;
        // Not declared in this module (package var, hierarchical, etc.)
        return sanitizeName(varp->prettyName());
    }
    int widthOf(const std::string& ident) const {
        const auto it = m_widths.find(ident);
        return it == m_widths.end() ? 1 : it->second;
    }
    SExpr newWire(int width) {
        SExpr e;
        e.text = newName("wire");
        e.width = width;
        e.isIdent = true;
        e.refs = {e.text};
        SDecl d;
        d.name = e.text;
        d.width = width;
        d.dir = VDirection::NONE;
        m_wires.push_back(d);
        m_widths[e.text] = width;
        return e;
    }
    static SExpr identExpr(const std::string& name, int width) {
        SExpr e;
        e.text = name;
        e.width = width;
        e.isIdent = true;
        e.refs = {name};
        return e;
    }
    static SExpr constExpr(uint64_t v, int width, bool isSigned = false) {
        SExpr e;
        e.width = width;
        e.isConst = true;
        e.hasVal = width <= 64;
        e.val = maskTo(v, width);
        e.isSigned = isSigned;
        e.text = constText(v, width);
        return e;
    }
    static void addRefs(std::vector<std::string>& into, const std::vector<std::string>& from) {
        into.insert(into.end(), from.begin(), from.end());
    }

    // ---- item construction ----
    void addAssign(const std::string& lhs, const SExpr& rhs,
                   const std::vector<std::string>& lhsRefs = {}) {
        SItem it;
        it.kind = SItem::ASSIGN;
        it.lhs = lhs;
        it.rhs = rhs.text;
        it.reads = rhs.refs;
        addRefs(it.reads, lhsRefs);
        it.writes = {rootIdent(lhs)};
        m_items.push_back(it);
    }
    static std::string rootIdent(const std::string& lvalText) {
        const size_t p = lvalText.find_first_of("[ ");
        return p == std::string::npos ? lvalText : lvalText.substr(0, p);
    }
    SItem& addCell(const std::string& prim, const std::string& inst) {
        SItem it;
        it.kind = SItem::CELL;
        it.prim = prim;
        it.inst = inst;
        m_items.push_back(it);
        return m_items.back();
    }
    static void pinIn(SItem& it, const std::string& name, const SExpr& e) {
        it.pins.push_back({name, e.text});
        addRefs(it.reads, e.refs);
    }
    static void pinOut(SItem& it, const std::string& name, const std::string& text,
                       const std::vector<std::string>& refs = {}) {
        it.pins.push_back({name, text});
        it.writes.push_back(rootIdent(text));
        addRefs(it.reads, refs);
    }

    // Ensure an expression is a plain identifier or literal (so that it can be
    // bit-selected or used as a mux/dff operand without re-evaluation).
    SExpr materialize(const SExpr& e) {
        if (e.isIdent || e.isConst) return e;
        const SExpr w = newWire(e.width);
        addAssign(w.text, e);
        return w;
    }

    // ---- primitives (sv_tran_struct gen_binary_op / gen_unary_op / gen_mux / gen_dff_en) ----
    SExpr genBinary(const std::string& prim, const SExpr& a, const SExpr& b, int opWidth,
                    int outWidth) {
        const SExpr out = newWire(outWidth);
        SItem& it = addCell(prim, newName("op"));
        it.params = {{"WIDTH", std::to_string(opWidth)}};
        pinIn(it, "a", a);
        pinIn(it, "b", b);
        pinOut(it, "out", out.text);
        return out;
    }
    SExpr genUnary(const std::string& prim, const SExpr& a, int opWidth, int outWidth) {
        const SExpr out = newWire(outWidth);
        SItem& it = addCell(prim, newName("op"));
        if (prim != "logical_not") it.params = {{"WIDTH", std::to_string(opWidth)}};
        pinIn(it, "in", a);
        pinOut(it, "out", out.text);
        return out;
    }
    SExpr genMux(const SExpr& sel, const SExpr& in0, const SExpr& in1, int width) {
        if (in0.text == in1.text) return in0;
        if (sel.hasVal) return sel.val ? in1 : in0;
        const SExpr out = newWire(width);
        SItem& it = addCell("mux2", newName("mux"));
        it.params = {{"WIDTH", std::to_string(width)}};
        pinIn(it, "sel", sel);
        pinIn(it, "in0", in0);
        pinIn(it, "in1", in1);
        pinOut(it, "out", out.text);
        m_muxes[out.text] = {sel, in0, in1};
        return out;
    }
    void genDff(const std::string& q, const std::vector<std::string>& qRefs, const SExpr& d,
                const SExpr& en, int width, uint64_t resetVal, bool useRst) {
        if (m_seq) m_regsInBlock.emplace_back(q, width);
        SItem& it = addCell(m_negedge ? "dffn_en" : "dff_en", newName("dff"));
        it.params = {{"WIDTH", std::to_string(width)},
                     {"RESET_VAL", std::to_string(resetVal)},
                     {"IS_ASYNC", (useRst && m_rstAsync) ? "1" : "0"}};
        pinIn(it, "clk", m_clk);
        if (useRst) {
            pinIn(it, "rst", m_rst);
        } else {
            it.pins.push_back({"rst", "1'b0"});
        }
        pinIn(it, "en", en);
        pinIn(it, "d", d);
        pinOut(it, "q", q, qRefs);
    }
    void genLatch(const std::string& q, const std::vector<std::string>& qRefs, const SExpr& en,
                  const SExpr& d, int width) {
        SItem& it = addCell("latch_en", newName("latch"));
        it.params = {{"WIDTH", std::to_string(width)}};
        pinIn(it, "en", en);
        pinIn(it, "d", d);
        pinOut(it, "q", q, qRefs);
    }

    // Logical AND of 1-bit expressions (path conditions)
    SExpr andBits(const SExpr& a, const SExpr& b) {
        if (a.hasVal) return a.val ? b : a;
        if (b.hasVal) return b.val ? a : b;
        return genBinary("bitwise_and", a, b, 1, 1);
    }
    SExpr notBit(const SExpr& a) {
        if (a.hasVal) return constExpr(a.val ? 0 : 1, 1);
        return genUnary("logical_not", toBool(a), 1, 1);
    }
    // Reduce a multi-bit value to a 1-bit truth value
    SExpr toBool(const SExpr& a) {
        if (a.width == 1) return a;
        if (a.hasVal) return constExpr(a.val ? 1 : 0, 1);
        return genUnary("reduction_or", a, a.width, 1);
    }
    SExpr eqConst(const SExpr& a, uint64_t v) {
        if (a.hasVal) return constExpr(maskTo(a.val, a.width) == maskTo(v, a.width), 1);
        return genBinary("comparator_eq", a, constExpr(v, a.width), a.width, 1);
    }
    SExpr pathCondition() {
        SExpr acc = constExpr(1, 1);
        for (const auto& c : m_pathCond) acc = andBits(acc, c.second ? notBit(c.first) : c.first);
        return acc;
    }

    //==================================================================
    // 1. Declaration pass

    static const AstNodeDType* unpackedOf(const AstNodeDType* dtp, int& depth, int& lo) {
        // Returns element dtype, depth = product of unpacked dims (1 if none)
        depth = 1;
        lo = 0;
        const AstNodeDType* d = dtp->skipRefp();
        bool first = true;
        while (const AstUnpackArrayDType* const ap = VN_CAST(d, UnpackArrayDType)) {
            depth *= ap->elementsConst();
            if (first) lo = ap->lo();
            first = false;
            d = ap->subDTypep()->skipRefp();
        }
        return d;
    }

    void declareVar(AstVar* varp, bool procedural) {
        if (m_declared.count(varp)) return;
        m_declared.insert(varp);
        if (varp->isGenVar() || varp->isIfaceRef()) return;
        if (varp->varType() == VVarType::GENVAR) return;
        std::string name = sanitizeName(m_genPrefix + varp->prettyName());
        if (varp->isParam()) {
            if (m_declNames.count(name)) return;  // same localparam in several scopes: folded anyway
        } else {
            // a procedural local shadowing a module-level name gets a scope suffix
            int n = 0;
            const std::string base = name;
            while (m_declNames.count(name)) name = base + "__" + std::to_string(++n);
        }
        m_declNames.insert(name);
        m_varName[varp] = name;
        SDecl d;
        d.name = name;
        d.dir = procedural ? VDirection{VDirection::NONE} : varp->direction();
        if (varp->isParam()) {
            d.isParam = true;
            if (const AstConst* const cp = VN_CAST(varp->valuep(), Const)) {
                d.paramValue = cp->num().ascii(true, true);
            } else {
                return;  // non-constant parameter (type / unresolved) - nothing to emit
            }
            m_decls.push_back(d);
            return;
        }
        int depth = 1;
        int lo = 0;
        const AstNodeDType* const elemp = unpackedOf(varp->dtypep(), depth, lo);
        const int elemWidth = elemp->width();
        d.width = elemWidth;
        d.isSigned = elemp->isSigned();
        if (depth > 1) {
            // Unpacked array (sv_memory.detect_memories)
            const int bits = depth * elemWidth;
            if (!varp->isIO() && bits > MEMORY_THRESHOLD_BITS) {
                SMem m;
                m.name = name;
                m.depth = depth;
                m.dataWidth = elemWidth;
                m.lo = lo;
                m.addrWidth = 1;
                while ((1 << m.addrWidth) < depth) ++m.addrWidth;
                m_mems[varp] = m;
                return;  // replaced by a memory primitive; no declaration
            }
            if (!varp->isIO()) {
                // Small array: one register / wire per element
                SMem m;
                m.name = name;
                m.depth = depth;
                m.dataWidth = elemWidth;
                m.lo = lo;
                m.asRegs = true;
                for (int i = 0; i < depth; ++i) {
                    SDecl e = d;
                    e.name = name + "__" + std::to_string(i);
                    m.regNames.push_back(e.name);
                    m_decls.push_back(e);
                    m_widths[e.name] = elemWidth;
                }
                m_mems[varp] = m;
                return;
            }
            d.unpacked = " [" + std::to_string(lo) + ":" + std::to_string(lo + depth - 1) + "]";
        } else if (m_wideMem && !varp->isIO() && elemWidth > 512 && elemWidth <= 65536) {
            // sv_memory wide-packed-array heuristic (opt-in): infer
            // DATA_WIDTH from a DATA_WIDTH / DATAWIDTH parameter, else 64/32/16/8
            int dw = 0;
            for (AstNode* sp = m_modp->stmtsp(); sp; sp = sp->nextp()) {
                if (const AstVar* const pv = VN_CAST(sp, Var)) {
                    if (pv->isParam() && (pv->name() == "DATA_WIDTH" || pv->name() == "DATAWIDTH")) {
                        if (const AstConst* const cp = VN_CAST(pv->valuep(), Const)) {
                            dw = cp->toSInt();
                        }
                    }
                }
            }
            if (!(dw > 0 && elemWidth % dw == 0)) {
                dw = 0;
                for (const int w : {64, 32, 16, 8}) {
                    if (elemWidth % w == 0 && elemWidth / w >= 4) {
                        dw = w;
                        break;
                    }
                }
            }
            if (dw > 0) {
                warn("wide packed array " + name + " inferred as memory " + std::to_string(elemWidth / dw)
                     + "x" + std::to_string(dw) + " (--struct-only-wide-packed-mem)");
                SMem m;
                m.name = name;
                m.depth = elemWidth / dw;
                m.dataWidth = dw;
                m.addrWidth = 1;
                while ((1 << m.addrWidth) < m.depth) ++m.addrWidth;
                m_mems[varp] = m;
                return;
            }
        }
        m_widths[name] = elemWidth;
        m_decls.push_back(d);
    }

    void declarePass(AstNode* nodep) {
        for (; nodep; nodep = nodep->nextp()) {
            if (AstVar* const varp = VN_CAST(nodep, Var)) {
                declareVar(varp, false);
            } else if (AstGenBlock* const gp = VN_CAST(nodep, GenBlock)) {
                VL_RESTORER_COPY(m_genPrefix);
                if (gp->prettyName().find('[') != std::string::npos) {
                    // sv_parse.qualify_genblock: unrolled iterations share
                    // scope-local names; prefix with the sanitised block name
                    // (Verilator encodes the brackets as __BRA__/__KET__ in
                    // name(); prettyName() restores them)
                    m_genPrefix += sanitizeName(gp->prettyName()) + "_";
                }
                declarePass(gp->genforp());
                declarePass(gp->itemsp());
            } else if (AstNodeProcedure* const pp = VN_CAST(nodep, NodeProcedure)) {
                declareNested(pp->stmtsp());
            } else if (AstBegin* const bp = VN_CAST(nodep, Begin)) {
                declareNested(bp->declsp());
                declareNested(bp->stmtsp());
            }
        }
    }
    // Procedural-scope locals (sv_tran_struct collect_vars): declared as
    // internal wires so the Z3 / lint side sees their width.
    void declareNested(AstNode* nodep) {
        for (; nodep; nodep = nodep->nextp()) {
            if (AstVar* const varp = VN_CAST(nodep, Var)) {
                declareVar(varp, true);
            } else if (AstBegin* const bp = VN_CAST(nodep, Begin)) {
                declareNested(bp->declsp());
                declareNested(bp->stmtsp());
            } else if (AstNodeIf* const ip = VN_CAST(nodep, NodeIf)) {
                declareNested(ip->thensp());
                declareNested(ip->elsesp());
            } else if (AstCase* const cp = VN_CAST(nodep, Case)) {
                for (AstCaseItem* ip = cp->itemsp(); ip; ip = VN_AS(ip->nextp(), CaseItem)) {
                    declareNested(ip->stmtsp());
                }
            } else if (AstLoop* const lp = VN_CAST(nodep, Loop)) {
                declareNested(lp->stmtsp());
                declareNested(lp->contsp());
            } else if (AstJumpBlock* const jp = VN_CAST(nodep, JumpBlock)) {
                declareNested(jp->stmtsp());
            }
        }
    }

    //==================================================================
    // 2. Lowering pass

    void lowerPass(AstNode* nodep) {
        for (; nodep; nodep = nodep->nextp()) {
            if (AstAlways* const ap = VN_CAST(nodep, Always)) {
                lowerAlways(ap);
            } else if (AstAssignW* const ap = VN_CAST(nodep, AssignW)) {
                lowerContAssign(ap);
            } else if (AstCell* const cp = VN_CAST(nodep, Cell)) {
                lowerCell(cp);
            } else if (AstGenBlock* const gp = VN_CAST(nodep, GenBlock)) {
                VL_RESTORER_COPY(m_genPrefix);
                if (gp->prettyName().find('[') != std::string::npos) {
                    m_genPrefix += sanitizeName(gp->prettyName()) + "_";
                }
                lowerPass(gp->itemsp());
            } else if (VN_IS(nodep, Initial) || VN_IS(nodep, InitialStatic)) {
                if (!harvestReadMem(VN_AS(nodep, NodeProcedure)->stmtsp())
                    && !harvestMemInit(VN_AS(nodep, NodeProcedure)->stmtsp())
                    && !harvestNetInit(VN_AS(nodep, NodeProcedure)->stmtsp())
                    && !evalMemInit(VN_AS(nodep, NodeProcedure)->stmtsp())) {
                    if (VN_IS(nodep, InitialStatic)) {
                        noteStaticInit(VN_AS(nodep, NodeProcedure)->stmtsp());
                    } else {
                        warnNode(nodep, "initial block dropped (not synthesisable)");
                    }
                }
            } else if (VN_IS(nodep, Final)) {
                warnNode(nodep, "final block dropped (not synthesisable)");
            } else if (VN_IS(nodep, Var) || VN_IS(nodep, NodeFTask) || VN_IS(nodep, Typedef)
                       || VN_IS(nodep, Comment) || VN_IS(nodep, Pragma)
                       || VN_IS(nodep, Port)) {
                // declarations handled in pass 1; functions inlined at use
            } else if (VN_IS(nodep, NodeCoverOrAssert) || VN_IS(nodep, AlwaysObserved)
                       || VN_IS(nodep, AlwaysReactive)) {
                // verification constructs: no hardware
            } else if (AstBegin* const bp = VN_CAST(nodep, Begin)) {
                lowerPass(bp->stmtsp());
            } else {
                warnNode(nodep, "unsupported module item dropped");
            }
        }
    }

    // `initial $readmemh("file", mem);` -> INIT_FILE on the memory primitive.
    // Returns true if every statement in the block was such an initialiser.
    bool harvestReadMem(AstNode* nodep) {
        bool all = true;
        for (; nodep; nodep = nodep->nextp()) {
            if (AstNodeReadWriteMem* const rp = VN_CAST(nodep, NodeReadWriteMem)) {
                const AstVarRef* const mp = VN_CAST(rp->memp(), VarRef);
                const AstConst* const fp = VN_CAST(rp->filenamep(), Const);
                if (mp && fp && fp->num().isString() && m_mems.count(mp->varp())
                    && VN_IS(rp, ReadMem)) {
                    std::string f = fp->num().ascii(false, false);
                    if (f.size() >= 2 && f.front() == '"' && f.back() == '"') f = f.substr(1, f.size() - 2);
                    m_mems[mp->varp()].initFile = f;
                    continue;
                }
                warnNode(nodep, "$readmem/$writemem dropped");
                all = false;
            } else if (AstBegin* const bp = VN_CAST(nodep, Begin)) {
                all &= harvestReadMem(bp->stmtsp());
            } else if (AstNodeIf* const ip = VN_CAST(nodep, NodeIf)) {
                all &= harvestReadMem(ip->thensp()) & harvestReadMem(ip->elsesp());
            } else if (VN_IS(nodep, Comment) || VN_IS(nodep, Var)) {
            } else {
                all = false;
            }
        }
        return all;
    }

    // `initial begin mem[0] = C0; mem[1] = C1; ... end` (LiteX/liteeth
    // inline a ROM's image this way): the words become the memory's image
    bool harvestMemInit(AstNode* stmtsp) {
        if (!stmtsp) return false;
        const AstVar* memVarp = nullptr;
        for (AstNode* sp = stmtsp; sp; sp = sp->nextp()) {
            if (VN_IS(sp, Comment)) continue;
            const AstNodeAssign* const ap = VN_CAST(sp, NodeAssign);
            if (!ap) return false;
            const AstArraySel* const selp = VN_CAST(ap->lhsp(), ArraySel);
            if (!selp) return false;
            const AstVarRef* const refp = VN_CAST(selp->fromp(), VarRef);
            if (!refp || !VN_IS(selp->bitp(), Const) || !VN_IS(ap->rhsp(), Const)) return false;
            if (!m_mems.count(refp->varp())) return false;
            if (memVarp && memVarp != refp->varp()) return false;
            memVarp = refp->varp();
            if (VN_AS(ap->rhsp(), Const)->num().width() > 64) return false;
        }
        if (!memVarp) return false;
        SMem& m = m_mems[memVarp];
        m.initWords.assign(m.depth, 0);
        for (AstNode* sp = stmtsp; sp; sp = sp->nextp()) {
            const AstNodeAssign* const ap = VN_CAST(sp, NodeAssign);
            if (!ap) continue;
            const AstArraySel* const selp = VN_AS(ap->lhsp(), ArraySel);
            const long long idx = VN_AS(selp->bitp(), Const)->num().toSQuad() - m.lo;
            if (idx < 0 || idx >= m.depth) continue;
            m.initWords[idx] = VN_AS(ap->rhsp(), Const)->num().toUQuad();
        }
        m.hasInitWords = true;
        return true;
    }

    // An `initial` block that computes ROM tables with loops (verilog-ethernet's
    // lfsr.v builds its CRC masks this way) is run here by a small interpreter
    // over the width-resolved AST: integers and vectors up to 64 bits, arrays,
    // blocking assigns to scalars / elements / bit slices, if, loops.  Anything
    // else gives up (and the block is reported as dropped).  Memories it wrote
    // get their image; scalars it wrote are left alone.
    struct InitEval final {
        StructModule& sm;
        std::unordered_map<const AstVar*, uint64_t> scalars;
        std::unordered_map<const AstVar*, std::vector<uint64_t>> arrays;
        std::unordered_set<const AstVar*> written;
        long long steps = 0;
        int depth = 0;
        bool failed = false;
        const AstNode* lastp = nullptr;  // the node being interpreted (for the give-up report)
        uint64_t fail() { failed = true; return 0; }
        explicit InitEval(StructModule& s) : sm{s} {}
        static uint64_t mask(uint64_t v, int w) { return w >= 64 ? v : (v & ((uint64_t{1} << w) - 1)); }
        static int64_t sext(uint64_t v, int w) {
            if (w >= 64 || w <= 0) return static_cast<int64_t>(v);
            const uint64_t m = uint64_t{1} << (w - 1);
            return static_cast<int64_t>((v ^ m) - m);
        }
        std::vector<uint64_t>& arrayOf(const AstVar* varp) {
            auto it = arrays.find(varp);
            if (it == arrays.end()) {
                int depth = 1;
                int lo = 0;
                unpackedOf(varp->dtypep(), depth, lo);
                it = arrays.emplace(varp, std::vector<uint64_t>(depth, 0)).first;
            }
            return it->second;
        }
        int arrayLo(const AstVar* varp) {
            int depth = 1;
            int lo = 0;
            unpackedOf(varp->dtypep(), depth, lo);
            return lo;
        }
        uint64_t eval(AstNodeExpr* ep) {
            if (!failed) lastp = ep;
            if (++steps > 20000000) return fail();
            if (ep->width() > 64) return fail();
            const int w = ep->width();
            if (AstConst* const cp = VN_CAST(ep, Const)) {
                if (cp->num().isFourState() || cp->num().width() > 64) return fail();
                return mask(cp->num().toUQuad(), w);
            }
            if (AstVarRef* const vp = VN_CAST(ep, VarRef)) {
                const auto it = scalars.find(vp->varp());
                if (it == scalars.end()) {
                    // never written here: its declaration value, else 0
                    if (const AstConst* const ip = VN_CAST(vp->varp()->valuep(), Const)) {
                        if (!ip->num().isFourState() && ip->num().width() <= 64) return mask(ip->num().toUQuad(), w);
                    }
                    return 0;
                }
                return mask(it->second, w);
            }
            if (AstArraySel* const ap = VN_CAST(ep, ArraySel)) {
                AstVarRef* const vp = VN_CAST(ap->fromp(), VarRef);
                if (!vp) return fail();
                std::vector<uint64_t>& arr = arrayOf(vp->varp());
                const long long i = static_cast<long long>(eval(ap->bitp())) - arrayLo(vp->varp());
                if (i < 0 || i >= static_cast<long long>(arr.size())) return 0;
                return mask(arr[i], w);
            }
            if (AstSel* const sp = VN_CAST(ep, Sel)) {
                const uint64_t from = eval(sp->fromp());
                const uint64_t lsb = eval(sp->lsbp());
                if (lsb >= 64) return 0;
                return mask(from >> lsb, sp->widthConst());
            }
            if (AstCond* const cp = VN_CAST(ep, Cond)) return mask(eval(cp->condp()) ? eval(cp->thenp()) : eval(cp->elsep()), w);
            if (VN_IS(ep, CReset)) return 0;
            if (AstFuncRef* const fp = VN_CAST(ep, FuncRef)) {
                // a function call: bind the arguments to the formals, run the
                // body, read the return variable; the callee's variables are
                // saved and restored so recursion and nesting work
                AstNodeFTask* const taskp = fp->taskp();
                if (!taskp || taskp->dpiImport() || taskp->prototype() || ++depth > 64) return fail();
                std::vector<AstVar*> formals, locals;
                sm.collectFtaskVars(taskp->stmtsp(), formals, locals);
                AstVar* const retp = VN_CAST(taskp->fvarp(), Var);
                std::vector<uint64_t> argv(formals.size(), 0);
                size_t pos = 0;
                for (AstArg* ap = fp->argsp(); ap; ap = VN_AS(ap->nextp(), Arg)) {
                    size_t idx = pos++;
                    if (!ap->name().empty()) for (size_t i = 0; i < formals.size(); ++i) if (formals[i]->name() == ap->name()) idx = i;
                    if (idx < argv.size() && ap->exprp()) argv[idx] = eval(ap->exprp());
                }
                std::vector<std::pair<const AstVar*, std::pair<bool, uint64_t>>> saved;
                auto save = [&](const AstVar* v) {
                    const auto it = scalars.find(v);
                    saved.push_back({v, {it != scalars.end(), it != scalars.end() ? it->second : 0}});
                };
                for (AstVar* v : formals) save(v);
                for (AstVar* v : locals) save(v);
                if (retp) save(retp);
                for (size_t i = 0; i < formals.size(); ++i) scalars[formals[i]] = mask(argv[i], formals[i]->width());
                for (AstVar* v : locals) scalars[v] = 0;
                if (retp) scalars[retp] = 0;
                run(taskp->stmtsp());
                const uint64_t r = retp ? scalars[retp] : 0;
                for (const auto& sv : saved) {
                    if (sv.second.first) scalars[sv.first] = sv.second.second;
                    else scalars.erase(sv.first);
                }
                --depth;
                return failed ? 0 : mask(r, w);
            }
            if (AstConcat* const cp = VN_CAST(ep, Concat)) {
                const uint64_t l = eval(cp->lhsp());
                const uint64_t r = eval(cp->rhsp());
                return mask((l << cp->rhsp()->width()) | r, w);
            }
            if (AstReplicate* const rp = VN_CAST(ep, Replicate)) {
                const uint64_t v = eval(rp->srcp());
                const uint64_t n = eval(rp->countp());
                const int vw = rp->srcp()->width();
                uint64_t out = 0;
                for (uint64_t i = 0; i < n && i * vw < 64; ++i) out |= v << (i * vw);
                return mask(out, w);
            }
            if (AstNodeUniop* const up = VN_CAST(ep, NodeUniop)) {
                const uint64_t a = eval(up->lhsp());
                const int aw = up->lhsp()->width();
                if (VN_IS(up, Not)) return mask(~a, w);
                if (VN_IS(up, LogNot)) return a == 0;
                if (VN_IS(up, Negate)) return mask(~a + 1, w);
                if (VN_IS(up, RedOr)) return a != 0;
                if (VN_IS(up, RedAnd)) return mask(a, aw) == mask(~uint64_t{0}, aw);
                if (VN_IS(up, RedXor)) return __builtin_parityll(a);
                if (VN_IS(up, Extend) || VN_IS(up, CCast)) return mask(a, w);
                if (VN_IS(up, ExtendS)) return mask(static_cast<uint64_t>(sext(a, aw)), w);
                return fail();
            }
            if (AstNodeBiop* const bp = VN_CAST(ep, NodeBiop)) {
                const uint64_t a = eval(bp->lhsp());
                const uint64_t b = eval(bp->rhsp());
                const int aw = bp->lhsp()->width();
                const int bw = bp->rhsp()->width();
                if (VN_IS(bp, And)) return mask(a & b, w);
                if (VN_IS(bp, Or)) return mask(a | b, w);
                if (VN_IS(bp, Xor)) return mask(a ^ b, w);
                if (VN_IS(bp, Add)) return mask(a + b, w);
                if (VN_IS(bp, Sub)) return mask(a - b, w);
                if (VN_IS(bp, Mul) || VN_IS(bp, MulS)) return mask(a * b, w);
                if (VN_IS(bp, ShiftL)) return b >= 64 ? 0 : mask(a << b, w);
                if (VN_IS(bp, ShiftR)) return b >= 64 ? 0 : mask(a >> b, w);
                if (VN_IS(bp, ShiftRS)) return b >= 64 ? mask(static_cast<uint64_t>(sext(a, aw) < 0 ? -1 : 0), w) : mask(static_cast<uint64_t>(sext(a, aw) >> b), w);
                if (VN_IS(bp, Eq) || VN_IS(bp, EqCase)) return a == b;
                if (VN_IS(bp, Neq) || VN_IS(bp, NeqCase)) return a != b;
                if (VN_IS(bp, Lt)) return a < b;
                if (VN_IS(bp, Lte)) return a <= b;
                if (VN_IS(bp, Gt)) return a > b;
                if (VN_IS(bp, Gte)) return a >= b;
                if (VN_IS(bp, LtS)) return sext(a, aw) < sext(b, bw);
                if (VN_IS(bp, LteS)) return sext(a, aw) <= sext(b, bw);
                if (VN_IS(bp, GtS)) return sext(a, aw) > sext(b, bw);
                if (VN_IS(bp, GteS)) return sext(a, aw) >= sext(b, bw);
                if (VN_IS(bp, LogAnd)) return (a != 0) && (b != 0);
                if (VN_IS(bp, LogOr)) return (a != 0) || (b != 0);
                if (VN_IS(bp, Div)) return b ? mask(a / b, w) : 0;
                if (VN_IS(bp, ModDiv)) return b ? mask(a % b, w) : 0;
                return fail();
            }
            return fail();
        }
        void assign(AstNodeExpr* lhsp, uint64_t val) {
            if (AstVarRef* const vp = VN_CAST(lhsp, VarRef)) {
                scalars[vp->varp()] = mask(val, lhsp->width());
                written.insert(vp->varp());
                return;
            }
            if (AstArraySel* const ap = VN_CAST(lhsp, ArraySel)) {
                AstVarRef* const vp = VN_CAST(ap->fromp(), VarRef);
                if (!vp) { failed = true; return; }
                std::vector<uint64_t>& arr = arrayOf(vp->varp());
                const long long i = static_cast<long long>(eval(ap->bitp())) - arrayLo(vp->varp());
                if (i >= 0 && i < static_cast<long long>(arr.size())) arr[i] = mask(val, lhsp->width());
                written.insert(vp->varp());
                return;
            }
            if (AstSel* const sp = VN_CAST(lhsp, Sel)) {
                const uint64_t lsb = eval(sp->lsbp());
                const int sw = sp->widthConst();
                if (lsb >= 64) return;
                const uint64_t old = eval(sp->fromp());
                const uint64_t m = (sw >= 64 ? ~uint64_t{0} : ((uint64_t{1} << sw) - 1)) << lsb;
                assign(sp->fromp(), (old & ~m) | ((val << lsb) & m));
                return;
            }
            { failed = true; return; }
        }
        void run(AstNode* nodep) {
            for (; nodep; nodep = nodep->nextp()) {
                if (!failed) lastp = nodep;
                if (failed || ++steps > 20000000) { failed = true; return; }
                if (VN_IS(nodep, Comment)) continue;
                if (AstNodeAssign* const ap = VN_CAST(nodep, NodeAssign)) {
                    assign(ap->lhsp(), eval(ap->rhsp()));
                } else if (AstBegin* const bp = VN_CAST(nodep, Begin)) {
                    run(bp->stmtsp());
                } else if (AstInitialStaticStmt* const sp = VN_CAST(nodep, InitialStaticStmt)) {
                    run(sp->stmtsp());  // a local's declaration-time value
                } else if (AstInitialAutomaticStmt* const sp = VN_CAST(nodep, InitialAutomaticStmt)) {
                    run(sp->stmtsp());
                } else if (AstNodeIf* const ip = VN_CAST(nodep, NodeIf)) {
                    run(eval(ip->condp()) ? ip->thensp() : ip->elsesp());  // whole branch list
                } else if (AstLoop* const lp = VN_CAST(nodep, Loop)) {
                    for (long long iter = 0;; ++iter) {
                        if (failed || iter > 1000000) { failed = true; return; }
                        bool stop = false;
                        for (AstNode* sp = lp->stmtsp(); sp; sp = sp->nextp()) {
                            if (AstLoopTest* const tp = VN_CAST(sp, LoopTest)) {
                                if (!eval(tp->condp())) { stop = true; break; }
                            } else {
                                runOne(sp);
                            }
                        }
                        if (stop) break;
                    }
                } else if (VN_IS(nodep, Var)) {
                } else {
                    { failed = true; return; }
                }
            }
        }
        void runOne(AstNode* nodep) {  // one statement, not its siblings
            if (VN_IS(nodep, Comment) || VN_IS(nodep, Var)) return;
            if (AstNodeAssign* const ap = VN_CAST(nodep, NodeAssign)) {
                assign(ap->lhsp(), eval(ap->rhsp()));
            } else if (AstBegin* const bp = VN_CAST(nodep, Begin)) {
                run(bp->stmtsp());
            } else if (AstInitialStaticStmt* const sp = VN_CAST(nodep, InitialStaticStmt)) {
                run(sp->stmtsp());
            } else if (AstInitialAutomaticStmt* const sp = VN_CAST(nodep, InitialAutomaticStmt)) {
                run(sp->stmtsp());
            } else if (AstNodeIf* const ip = VN_CAST(nodep, NodeIf)) {
                run(eval(ip->condp()) ? ip->thensp() : ip->elsesp());
            } else if (VN_IS(nodep, Loop)) {
                AstNode* const nextp = nodep->nextp();
                if (!nextp) { run(nodep); return; }
                // run the loop alone: temporarily its own list
                struct Detach { AstNode* n; AstNode* next; };
                // simplest: interpret the loop node directly
                AstLoop* const lp = VN_AS(nodep, Loop);
                for (long long iter = 0;; ++iter) {
                    if (iter > 1000000) { failed = true; return; }
                    bool stop = false;
                    for (AstNode* sp = lp->stmtsp(); sp; sp = sp->nextp()) {
                        if (AstLoopTest* const tp = VN_CAST(sp, LoopTest)) {
                            if (!eval(tp->condp())) { stop = true; break; }
                        } else {
                            runOne(sp);
                        }
                    }
                    if (stop) break;
                }
            } else {
                { failed = true; return; }
            }
        }
    };
    bool evalMemInit(AstNode* stmtsp) {
        if (!stmtsp) return false;
        InitEval ev{*this};
        ev.run(stmtsp);
        if (ev.failed) {
            if (std::getenv("STRUCT_DEBUG_INIT") && ev.lastp)
                std::cerr << "struct: initial-block interpreter gave up at " << ev.lastp->typeName()
                          << " " << ev.lastp->fileline()->ascii() << "\n";
            return false;
        }
        bool any = false;
        for (const AstVar* varp : ev.written) {
            const auto mit = m_mems.find(varp);
            if (mit == m_mems.end()) continue;
            SMem& m = mit->second;
            const std::vector<uint64_t>& arr = ev.arrayOf(varp);
            m.initWords.assign(m.depth, 0);
            for (int i = 0; i < m.depth && i < static_cast<int>(arr.size()); ++i) m.initWords[i] = arr[i];
            m.hasInitWords = true;
            any = true;
        }
        return any;
    }

    // `reg r = CONST;` with no other driver (a configuration knob only a
    // testbench would poke) is the constant: `initial static` values are
    // remembered here and emitted as assigns for variables nothing drives.
    std::vector<std::pair<std::string, AstConst*>> m_staticInits;
    void noteStaticInit(AstNode* stmtsp) {
        for (AstNode* sp = stmtsp; sp; sp = sp->nextp()) {
            const AstAssign* const asp = VN_CAST(sp, Assign);
            if (!asp) continue;
            const AstVarRef* const refp = VN_CAST(asp->lhsp(), VarRef);
            AstConst* const cp = VN_CAST(asp->rhsp(), Const);
            if (!refp || !cp || refp->varp()->isNet()) continue;
            if (!VN_IS(refp->varp()->dtypep()->skipRefp(), BasicDType)) continue;
            m_staticInits.emplace_back(sanitizeName(m_genPrefix + refp->varp()->prettyName()), cp);
        }
    }
    void fillStaticInits() {
        std::unordered_set<std::string> written;
        for (const SItem& it : m_items) {
            for (const std::string& w : it.writes) written.insert(w);
        }
        // A register with a declaration value (`reg [3:0] n = 4'd12;`) powers
        // up there on an FPGA: the value goes onto its register cells as
        // INIT_VAL (the slice a cell holds, when the register was split)
        for (const auto& kv : m_staticInits) {
            if (!written.count(kv.first) || kv.second->num().width() > 64 || kv.second->num().isFourState()) continue;
            const uint64_t v = kv.second->num().toUQuad();
            if (!v) continue;
            for (SItem& it : m_items) {
                if (it.kind != SItem::CELL || (it.prim != "dff_en" && it.prim != "dffn_en")) continue;
                for (const SPin& pin : it.pins) {
                    if (pin.name != "q") continue;
                    const std::string& e = pin.expr;
                    int lo = -1;
                    int w = -1;
                    if (e == kv.first) {
                        lo = 0;
                    } else if (e.compare(0, kv.first.size() + 1, kv.first + "[") == 0) {
                        int a = 0, b = 0;
                        const char* rest = e.c_str() + kv.first.size() + 1;
                        if (std::sscanf(rest, "%d +: %d]", &a, &b) == 2) { lo = a; w = b; }
                        else if (std::sscanf(rest, "%d:%d]", &a, &b) == 2) { lo = std::min(a, b); w = std::abs(a - b) + 1; }
                        else if (std::sscanf(rest, "%d]", &a) == 1) { lo = a; w = 1; }
                    }
                    if (lo < 0) continue;
                    uint64_t part = lo >= 64 ? 0 : (v >> lo);
                    if (w > 0 && w < 64) part &= (uint64_t{1} << w) - 1;
                    if (part) it.params.emplace_back("INIT_VAL", std::to_string(part));
                }
            }
        }
        for (const auto& kv : m_staticInits) {
            if (written.count(kv.first)) continue;
            Env env;
            warn("variable " + kv.first + " is only assigned by its declaration; treated as the constant "
                 + kv.second->num().ascii(true, true));
            addAssign(kv.first, lowerExpr(kv.second, env));
            written.insert(kv.first);
        }
    }

    // `wire w = expr;` reaches us as `initial w = expr;` (an AstInitial whose
    // statements all assign nets): that is a continuous assignment.
    bool harvestNetInit(AstNode* stmtsp) {
        if (!stmtsp) return false;
        for (AstNode* sp = stmtsp; sp; sp = sp->nextp()) {
            const AstAssign* const asp = VN_CAST(sp, Assign);
            if (!asp) return false;
            const AstVarRef* const refp = VN_CAST(asp->lhsp(), VarRef);
            if (!refp || !refp->varp()->isNet()) return false;
        }
        for (AstNode* sp = stmtsp; sp; sp = sp->nextp()) {
            const AstAssign* const asp = VN_AS(sp, Assign);
            lowerContAssign(asp, asp->lhsp(), asp->rhsp());
        }
        return true;
    }

    // ---- continuous assign ----
    void lowerContAssign(AstAssignW* ap) { lowerContAssign(ap, ap->lhsp(), ap->rhsp()); }
    void lowerContAssign(const AstNode* ap, AstNodeExpr* lhsp, AstNodeExpr* rhsp) {
        Env env;
        const SLVal lv = lowerLValue(lhsp, env);
        if (!lv.ok) return;
        const SExpr rhs = lowerExpr(rhsp, env);
        if (lv.memVarp) {
            warnNode(ap, "continuous assign into memory array unsupported");
            return;
        }
        if (lv.memDynamic) {
            warnNode(ap, "continuous assign with dynamic array index unsupported");
            return;
        }
        if (rhs.text != lv.text) addAssign(lv.text, rhs, lv.refs);
    }

    // A parameter value as Verilog text: a string literal keeps its quotes
    // (Verilator packs "7SERIES" into a 56-bit number but remembers where it
    // came from), everything else as Verilator prints it (256'h.., 20.0, 32'sh1)
    static std::string paramText(const AstConst* kp) {
        const V3Number& num = kp->num();
        if (num.isString()) return num.ascii(true, true);
        if (num.isFromString() && num.width() % 8 == 0 && !num.isFourState()) {
            std::string str;
            for (int b = num.width() - 8; b >= 0; b -= 8) {
                int ch = 0;
                for (int k = 0; k < 8; ++k) if (num.bitIs1(b + k)) ch |= 1 << k;
                if (ch) str += static_cast<char>(ch);
            }
            return "\"" + str + "\"";
        }
        return num.ascii(true, true);
    }

    // ---- user module instance ----
    void lowerCell(AstCell* cp) {
        Env env;
        SItem it;
        it.kind = SItem::USERCELL;
        it.keep = true;
        it.prim = cp->modp() ? V3EmitStruct::cellTypeName(cp->modp()) : sanitizeName(cp->modName());
        it.inst = sanitizeName(m_genPrefix + cp->prettyName());
        // A black box keeps its parameters (RAMB INIT_*, MMCM settings): after
        // V3Param they live on the specialised module as parameter vars
        if (cp->modp() && V3EmitStruct::isBlackbox(cp->modp())) {
            for (AstNode* sp = cp->modp()->stmtsp(); sp; sp = sp->nextp()) {
                const AstVar* const vp = VN_CAST(sp, Var);
                if (!vp || !vp->isGParam()) continue;
                const AstConst* const kp = VN_CAST(vp->valuep(), Const);
                if (!kp) continue;
                it.params.emplace_back(vp->prettyName(), paramText(kp));
            }
        }
        for (AstPin* pinp = cp->pinsp(); pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            // positional connections are named __pinNumberN; the port is modVarp
            const std::string pinName = pinp->modVarp() ? pinp->modVarp()->prettyName() : pinp->name();
            if (!pinp->exprp()) {
                it.pins.push_back({pinName, ""});
                continue;
            }
            AstNodeExpr* const ep = VN_CAST(pinp->exprp(), NodeExpr);
            if (!ep) continue;
            const bool isOut = pinp->modVarp() && pinp->modVarp()->direction().isWritable();
            if (isOut) {
                SLVal lv;
                if (!VN_IS(ep, Concat)) lv = lowerLValue(ep, env);
                if (lv.ok && !lv.memVarp && !lv.memDynamic) {
                    pinOut(it, pinName, lv.text, lv.refs);
                } else if (VN_IS(ep, Concat)) {
                    // .PIN({a[9], b[3:0]}): the pin drives a wire, the parts take slices
                    std::vector<AstNodeExpr*> parts;
                    flattenConcat(ep, parts);
                    const SExpr w = newWire(ep->width());
                    pinOut(it, pinName, w.text, {});
                    int lo = ep->width();
                    for (AstNodeExpr* const pp : parts) {
                        lo -= pp->width();
                        const SLVal plv = lowerLValue(pp, env);
                        if (!plv.ok || plv.memVarp || plv.memDynamic) {
                            warnNode(pp, "unsupported output pin connection part");
                            continue;
                        }
                        addAssign(plv.text, sliceOf(w, lo, pp->width()), plv.refs);
                    }
                } else {
                    warnNode(pinp, "unsupported output pin connection");
                }
            } else {
                const SExpr e = lowerExpr(ep, env);
                pinIn(it, pinName, e);
            }
        }
        m_items.push_back(it);
    }

    //------------------------------------------------------------------
    // Always-block classification (sv_tran_struct classify_always_block)

    // predicate_signal: v | !v | v == K | v != K  -> v
    static const AstVar* predicateVar(AstNodeExpr* condp) {
        if (const AstVarRef* const vp = VN_CAST(condp, VarRef)) return vp->varp();
        if (const AstNodeUniop* const up = VN_CAST(condp, NodeUniop)) {
            if (VN_IS(up, Not) || VN_IS(up, LogNot)) {
                if (const AstVarRef* const vp = VN_CAST(up->lhsp(), VarRef)) return vp->varp();
            }
        }
        if (const AstNodeBiop* const bp = VN_CAST(condp, NodeBiop)) {
            if (VN_IS(bp, Eq) || VN_IS(bp, Neq)) {
                if (VN_IS(bp->rhsp(), Const)) {
                    if (const AstVarRef* const vp = VN_CAST(bp->lhsp(), VarRef)) return vp->varp();
                }
                if (VN_IS(bp->lhsp(), Const)) {
                    if (const AstVarRef* const vp = VN_CAST(bp->rhsp(), VarRef)) return vp->varp();
                }
            }
        }
        return nullptr;
    }
    static bool assignsOnlyConstants(AstNode* nodep) {
        if (!nodep) return false;
        bool any = false;
        for (; nodep; nodep = nodep->nextp()) {
            if (const AstNodeAssign* const ap = VN_CAST(nodep, NodeAssign)) {
                if (!VN_IS(ap->rhsp(), Const)) return false;
                any = true;
            } else if (const AstBegin* const bp = VN_CAST(nodep, Begin)) {
                if (!assignsOnlyConstants(bp->stmtsp())) return false;
                any = true;
            } else {
                return false;
            }
        }
        return any;
    }
    // Walk the top-level if/else-if chain (or the folded ternary form) and
    // collect (reset var, condition expr) pairs in source order.
    struct ResetLink final {
        const AstVar* varp;
        AstNodeExpr* condp;
        bool negated;  // reset branch is the ELSE of condp (V3Const swapped `if (!rst)`)
    };
    static void collectResetChain(AstNode* nodep, std::vector<ResetLink>& out) {
        if (!nodep) return;
        if (const AstBegin* const bp = VN_CAST(nodep, Begin)) {
            collectResetChain(bp->stmtsp(), out);
            return;
        }
        if (AstNodeIf* const ip = VN_CAST(nodep, NodeIf)) {
            const AstVar* const v = predicateVar(ip->condp());
            if (!v) return;
            if (assignsOnlyConstants(ip->thensp())) {
                out.push_back({v, ip->condp(), false});
                collectResetChain(ip->elsesp(), out);
            } else if (assignsOnlyConstants(ip->elsesp())) {
                out.push_back({v, ip->condp(), true});
                collectResetChain(ip->thensp(), out);
            }
            return;
        }
        if (const AstNodeAssign* const ap = VN_CAST(nodep, NodeAssign)) {
            AstNodeExpr* ep = ap->rhsp();
            while (AstCond* const cp = VN_CAST(ep, Cond)) {
                const AstVar* const v = predicateVar(cp->condp());
                if (!v) break;
                if (VN_IS(cp->thenp(), Const)) {
                    out.push_back({v, cp->condp(), false});
                    ep = cp->elsep();
                } else if (VN_IS(cp->elsep(), Const)) {
                    out.push_back({v, cp->condp(), true});
                    ep = cp->thenp();
                } else {
                    break;
                }
            }
        }
    }

    enum class BlockKind : uint8_t { COMB, SEQ, LATCH, CONT, UNSYNTH };

    struct Classification final {
        BlockKind kind = BlockKind::UNSYNTH;
        const AstVar* clockp = nullptr;
        bool negedge = false;
        bool hasRst = false;
        bool rstAsync = false;
        const AstVar* rstVarp = nullptr;
        AstNodeExpr* rstCondp = nullptr;
        bool rstNegated = false;
        std::string reason;
    };

    Classification classify(AstAlways* ap) {
        Classification c;
        switch (ap->keyword()) {
        case VAlwaysKwd::CONT_ASSIGN: c.kind = BlockKind::CONT; return c;
        case VAlwaysKwd::ALWAYS_COMB: c.kind = BlockKind::COMB; return c;
        case VAlwaysKwd::ALWAYS_LATCH: c.kind = BlockKind::LATCH; return c;
        default: break;
        }
        std::vector<std::pair<const AstVar*, bool>> edges;  // (var, negedge)
        int levels = 0;
        if (AstSenTree* const stp = ap->sentreep()) {
            for (AstSenItem* ip = stp->sensesp(); ip; ip = VN_AS(ip->nextp(), SenItem)) {
                const AstVarRef* const vrp = VN_CAST(ip->sensp(), VarRef);
                if (ip->edgeType() == VEdgeType::ET_POSEDGE
                    || ip->edgeType() == VEdgeType::ET_NEGEDGE) {
                    if (!vrp) {
                        c.reason = "edge-sensitive item that is not a plain signal";
                        return c;
                    }
                    edges.emplace_back(vrp->varp(), ip->edgeType() == VEdgeType::ET_NEGEDGE);
                } else {
                    ++levels;
                }
            }
        }
        const bool isFf = ap->keyword() == VAlwaysKwd::ALWAYS_FF;
        if (edges.empty()) {
            if (!isFf) {
                c.kind = BlockKind::COMB;  // always @(a or b), always @*
            } else {
                c.reason = "always_ff with no edge-triggered signal";
            }
            return c;
        }
        std::vector<ResetLink> bodyResets;
        collectResetChain(ap->stmtsp(), bodyResets);
        if (edges.size() == 1) {
            c.kind = BlockKind::SEQ;
            c.clockp = edges[0].first;
            c.negedge = edges[0].second;
            // One edge: reset (if any) is synchronous, taken from the body chain
            for (const ResetLink& r : bodyResets) {
                if (r.varp != c.clockp) {
                    c.hasRst = true;
                    c.rstAsync = false;
                    c.rstVarp = r.varp;
                    c.rstCondp = r.condp;
                    c.rstNegated = r.negated;
                    break;
                }
            }
            return c;
        }
        // Two or more edges: async controls are the body-chain signals that
        // are also edges; the clock is the single remaining edge.
        std::vector<ResetLink> asyncResets;
        for (const ResetLink& r : bodyResets) {
            for (const auto& e : edges) {
                if (e.first == r.varp) {
                    asyncResets.push_back(r);
                    break;
                }
            }
        }
        std::vector<std::pair<const AstVar*, bool>> clocks;
        for (const auto& e : edges) {
            bool isRst = false;
            for (const ResetLink& r : asyncResets) isRst |= (r.varp == e.first);
            if (!isRst) clocks.push_back(e);
        }
        if (clocks.size() == 1 && !asyncResets.empty()) {
            c.kind = BlockKind::SEQ;
            c.clockp = clocks[0].first;
            c.negedge = clocks[0].second;
            c.hasRst = true;
            c.rstAsync = true;
            c.rstVarp = asyncResets[0].varp;
            c.rstCondp = asyncResets[0].condp;
            c.rstNegated = asyncResets[0].negated;
            for (size_t i = 1; i < asyncResets.size(); ++i) {
                warn("set/reset FF: secondary async control '"
                     + varName(asyncResets[i].varp)
                     + "' recognised but not wired into the register cell");
            }
            return c;
        }
        c.reason = "multi-edge always block but body has no reset-style chain";
        return c;
    }

    //------------------------------------------------------------------
    // Always block lowering

    void lowerAlways(AstAlways* ap) {
        const Classification cls = classify(ap);
        if (cls.kind == BlockKind::CONT) {
            for (AstNode* sp = ap->stmtsp(); sp; sp = sp->nextp()) {
                if (AstAssignW* const wp = VN_CAST(sp, AssignW)) {
                    lowerContAssign(wp);
                } else {
                    warnNode(sp, "unexpected statement in continuous assign");
                }
            }
            return;
        }
        if (cls.kind == BlockKind::UNSYNTH) {
            warnNode(ap, "unsynthesizable always block: " + cls.reason);
            SItem it;
            it.kind = SItem::COMMENT;
            it.text = "/* unsynthesizable always block: " + cls.reason + " */";
            it.keep = true;
            m_items.push_back(it);
            return;
        }
        VL_RESTORER(m_seq);
        VL_RESTORER(m_latch);
        VL_RESTORER_COPY(m_clk);
        VL_RESTORER(m_negedge);
        VL_RESTORER(m_hasRst);
        VL_RESTORER(m_rstAsync);
        VL_RESTORER_COPY(m_rst);
        VL_RESTORER(m_rstVarp);
        VL_RESTORER(m_rstCondp);
        m_seq = cls.kind == BlockKind::SEQ;
        m_latch = cls.kind == BlockKind::LATCH;
        m_hasRst = false;
        m_rstAsync = false;
        m_rstVarp = nullptr;
        m_rstCondp = nullptr;
        m_pathCond.clear();
        m_regsInBlock.clear();
        ++m_alwaysSeq;
        Env env;
        if (m_seq) {
            m_clk = identExpr(varName(cls.clockp), 1);
            m_negedge = cls.negedge;
            if (cls.hasRst) {
                m_hasRst = true;
                m_rstAsync = cls.rstAsync;
                m_rstVarp = cls.rstVarp;
                m_rstCondp = cls.rstCondp;
                SExpr r = toBool(lowerExpr(cls.rstCondp, env));
                if (cls.rstNegated) r = notBit(r);
                m_rst = materialize(r);
            }
        }
        lowerStmts(ap->stmtsp(), env);
        finishBlock(env);
        if (m_seq && m_report) reportRegisters(cls);
    }

    // Emit the block's final values as registers / latches / assigns
    void finishBlock(Env& env) {
        foldPending(env, nullptr);
        // A variable written both whole and in slices gets one register
        std::unordered_set<std::string> absorbedSlices;
        for (const std::string& key : env.order) {
            if (key.find('[') != std::string::npos || !env.next.count(key)) continue;
            const std::string pfx = key + "[";
            bool any = false;
            for (auto it = env.next.lower_bound(pfx); it != env.next.end() && it->first.compare(0, pfx.size(), pfx) == 0; ++it) {
                absorbedSlices.insert(it->first);
                any = true;
            }
            if (any) env.next[key] = assembleFromMap(key, env.next[key], env.next);
        }
        for (const std::string& key : env.order) {
            if (!env.next.count(key) || absorbedSlices.count(key)) continue;
            const SExpr val = env.next[key];
            if (val.text == key) continue;  // hold
            const int width = widthOfKey(key);
            const std::vector<std::string> qRefs = keyRefs(key);
            if (m_seq) {
                SExpr d = val;
                SExpr en = constExpr(1, 1);
                // `q <= rst ? C : x`  -> the register's reset pin / RESET_VAL
                uint64_t resetVal = 0;
                bool useRst = false;
                if (m_hasRst) {
                    const auto rit = m_muxes.find(d.text);
                    if (rit != m_muxes.end() && rit->second.sel.text == m_rst.text
                        && rit->second.in1.hasVal) {
                        resetVal = rit->second.in1.val;
                        d = rit->second.in0;
                        useRst = true;
                    } else if (rit != m_muxes.end() && rit->second.sel.text == m_rst.text
                               && rit->second.in1.text == key) {
                        // reset branch holds: no reset on this register
                        d = rit->second.in0;
                    }
                }
                // `if (en) q <= d;` -> dff_en with EN; nested holds
                // (`if (en) if (we) ... else q <= d;`) fold into one enable
                for (int level = 0; level < 4; ++level) {
                    const auto mit = m_muxes.find(d.text);
                    if (mit == m_muxes.end()) break;
                    SExpr lvlEn;
                    if (mit->second.in0.text == key && (level > 0 || mit->second.sel.isIdent)) {
                        lvlEn = mit->second.sel;
                        d = mit->second.in1;
                    } else if (mit->second.in1.text == key) {
                        // hold in the taken branch: enable is the inverted select
                        lvlEn = materialize(notBit(mit->second.sel));
                        d = mit->second.in0;
                    } else {
                        break;
                    }
                    en = level == 0 ? lvlEn : materialize(andBits(en, lvlEn));
                }
                // `if (re) q <= mem[a];` with no reset -> a synchronous read
                // port whose output register is the BRAM's own
                const auto rp = d.isIdent ? m_readPorts.find(d.text) : m_readPorts.end();
                if (!useRst && rp != m_readPorts.end()) {
                    SMem& m = m_mems.at(rp->second.first);
                    if (m.sync.size() < m.readIdx.size()) m.sync.resize(m.readIdx.size());
                    SMem::SyncRead& sr = m.sync[rp->second.second];
                    if (!sr.used) {
                        sr.used = true;
                        sr.en = en;
                        sr.q = key;
                        sr.qRefs = qRefs;
                        sr.clk = m_clk;
                        m.clk = m_clk;
                        m_deferred.push_back({key, qRefs, d, en, m_clk, width, m_negedge});
                        continue;
                    }
                }
                genDff(key, qRefs, d, en, width, resetVal, useRst);
            } else if (m_latch) {
                const auto mit = m_muxes.find(val.text);
                if (mit != m_muxes.end() && mit->second.in0.text == key) {
                    genLatch(key, qRefs, mit->second.sel, mit->second.in1, width);
                } else {
                    warn("always_latch: no enable structure for " + key + ", using en=1");
                    genLatch(key, qRefs, constExpr(1, 1), val, width);
                }
            } else {
                addAssign(key, val, qRefs);
            }
        }
    }

    // "base[lo+:w]" with a constant lo -> true
    static bool splitSliceKey(const std::string& key, std::string& base, int& lo, int& w) {
        const size_t b = key.find('[');
        if (b == std::string::npos) return false;
        const size_t p = key.find("+:", b);
        if (p == std::string::npos || key.back() != ']') return false;
        base = key.substr(0, b);
        char* endp = nullptr;
        lo = static_cast<int>(std::strtol(key.c_str() + b + 1, &endp, 10));
        if (endp != key.c_str() + p) return false;
        w = std::atoi(key.c_str() + p + 2);
        return w > 0;
    }
    // bits [lo+:w] of a value (which may need materialising)
    SExpr sliceOf(const SExpr& v, int lo, int w) {
        if (v.hasVal) return constExpr(maskTo(v.val >> lo, w), w);
        const SExpr m = materialize(v);
        SExpr e;
        e.text = w == 1 ? m.text + "[" + std::to_string(lo) + "]"
                        : m.text + "[" + std::to_string(lo + w - 1) + ":" + std::to_string(lo) + "]";
        e.width = w;
        e.refs = m.refs;
        return e;
    }
    // Apply the slice entries of `map` for `name` on top of `whole`
    SExpr assembleFromMap(const std::string& name, const SExpr& whole, const std::map<std::string, SExpr>& map) {
        const std::string pfx = name + "[";
        std::vector<std::pair<int, std::pair<int, SExpr>>> slices;  // (lo, (w, value))
        for (auto it = map.lower_bound(pfx); it != map.end() && it->first.compare(0, pfx.size(), pfx) == 0; ++it) {
            std::string base;
            int lo, w;
            if (!splitSliceKey(it->first, base, lo, w)) continue;
            slices.emplace_back(lo, std::make_pair(w, it->second));
        }
        if (slices.empty()) return whole;
        std::sort(slices.begin(), slices.end(), [](const auto& a, const auto& b) { return a.first < b.first; });
        const SExpr base = materialize(whole);
        std::string text = "{";
        std::vector<std::string> refs;
        int pos = whole.width;
        bool first = true;
        auto piece = [&](const std::string& t, const std::vector<std::string>& r) {
            if (!first) text += ", ";
            first = false;
            text += t;
            addRefs(refs, r);
        };
        for (auto it = slices.rbegin(); it != slices.rend(); ++it) {
            const int lo = it->first;
            const int w = it->second.first;
            if (lo + w > pos) continue;
            if (lo + w < pos) {
                const SExpr gap = sliceOf(base, lo + w, pos - (lo + w));  // folds a constant base
                piece(gap.text, gap.refs);
            }
            const SExpr v = materialize(it->second.second);
            piece(v.text, v.refs);
            pos = lo;
        }
        if (pos > 0) {
            const SExpr tail = sliceOf(base, 0, pos);
            piece(tail.text, tail.refs);
        }
        text += "}";
        SExpr e;
        e.text = text;
        e.width = whole.width;
        e.refs = refs;
        const SExpr w = newWire(whole.width);
        addAssign(w.text, e);
        return w;
    }

    int widthOfKey(const std::string& key) const {
        // "x[lsb+:w]" -> w ; "x" -> width of x
        const size_t p = key.find("+:");
        if (p != std::string::npos) {
            return std::atoi(key.c_str() + p + 2);
        }
        return widthOf(rootIdent(key));
    }
    static std::vector<std::string> keyRefs(const std::string& key) {
        // identifiers inside the key's index expression (dynamic selects)
        std::vector<std::string> out;
        const size_t b = key.find('[');
        if (b == std::string::npos) return out;
        std::string cur;
        for (size_t i = b; i < key.size(); ++i) {
            const char c = key[i];
            if (std::isalnum(static_cast<unsigned char>(c)) || c == '_' || c == '$') {
                cur += c;
            } else {
                if (!cur.empty() && !std::isdigit(static_cast<unsigned char>(cur[0]))
                    && cur.find('\'') == std::string::npos)
                    out.push_back(cur);
                cur.clear();
            }
        }
        return out;
    }

    void reportRegisters(const Classification& cls) {
        if (m_regsInBlock.empty()) return;
        std::vector<std::pair<std::string, int>> regs = m_regsInBlock;
        std::sort(regs.begin(), regs.end());
        int total = 0;
        for (const auto& r : regs) total += r.second;
        std::cerr << "\nInferred memory devices in process\n"
                  << "    in routine always_seq_" << m_alwaysSeq << " in module '"
                  << m_modp->prettyName() << "'.\n"
                  << "===============================================================================\n"
                  << "| Register Name                | Type  | Width | Bus | MB | AR | AS | SR | SS | ST |\n"
                  << "===============================================================================\n";
        for (const auto& r : regs) {
            std::cerr << "| " << std::left << std::setw(28) << r.first << " | Flop  | "
                      << std::right << std::setw(5) << r.second << " | " << std::setw(3)
                      << (r.second > 1 ? "Y" : "N") << " | -  | "
                      << (cls.hasRst && cls.rstAsync ? "Y" : "N") << "  | N  | "
                      << (cls.hasRst && !cls.rstAsync ? "Y" : "N") << "  | N  | N  |\n";
        }
        std::cerr << "===============================================================================\n"
                  << "| Total inferred registers: " << std::setw(3) << regs.size()
                  << "                                 Bits: " << std::setw(6) << total << " |\n"
                  << "===============================================================================\n\n";
    }

    //------------------------------------------------------------------
    // Statements

    void lowerStmts(AstNode* nodep, Env& env) {
        for (; nodep; nodep = nodep->nextp()) {
            if (env.halted) return;
            lowerStmt(nodep, env);
        }
    }

    void lowerStmt(AstNode* nodep, Env& env) {
        if (AstNodeAssign* const ap = VN_CAST(nodep, NodeAssign)) {
            if (VN_IS(ap, AssignForce)) {
                warnNode(nodep, "force/release dropped");
                return;
            }
            const bool blocking = !VN_IS(ap, AssignDly);
            lowerAssign(ap->lhsp(), ap->rhsp(), blocking, env);
        } else if (AstNodeIf* const ip = VN_CAST(nodep, NodeIf)) {
            lowerIf(ip, env);
        } else if (AstCase* const cp = VN_CAST(nodep, Case)) {
            lowerCase(cp, env);
        } else if (AstBegin* const bp = VN_CAST(nodep, Begin)) {
            lowerStmts(bp->stmtsp(), env);
        } else if (AstLoop* const lp = VN_CAST(nodep, Loop)) {
            lowerLoop(lp, env);
        } else if (AstJumpBlock* const jp = VN_CAST(nodep, JumpBlock)) {
            m_jumpStack.push_back(jp);
            lowerStmts(jp->stmtsp(), env);
            m_jumpStack.pop_back();
            if (env.halted && env.haltTarget == jp) {
                env.halted = false;
                env.haltTarget = nullptr;
            }
            foldPending(env, jp);
        } else if (AstJumpGo* const gp = VN_CAST(nodep, JumpGo)) {
            env.halted = true;
            env.haltTarget = gp->blockp();
        } else if (AstStmtExpr* const sp = VN_CAST(nodep, StmtExpr)) {
            if (AstTaskRef* const tp = VN_CAST(sp->exprp(), TaskRef)) {
                inlineTask(tp, env);
            } else if (AstFuncRef* const fp = VN_CAST(sp->exprp(), FuncRef)) {
                inlineCall(fp, env, nullptr);
            } else if (VN_IS(sp->exprp(), CMethodHard) || VN_IS(sp->exprp(), MethodCall)) {
                warnNode(nodep, "method call dropped");
            } else {
                warnNode(nodep, "expression statement dropped");
            }
        } else if (VN_IS(nodep, Var) || VN_IS(nodep, Comment) || VN_IS(nodep, CReset)
                   || VN_IS(nodep, StmtPragma)) {
            // declarations / no-ops
        } else if (AstInitialAutomaticStmt* const iap = VN_CAST(nodep, InitialAutomaticStmt)) {
            lowerStmts(iap->stmtsp(), env);
        } else if (AstInitialStaticStmt* const isp = VN_CAST(nodep, InitialStaticStmt)) {
            lowerStmts(isp->stmtsp(), env);
        } else if (VN_IS(nodep, Display) || VN_IS(nodep, Stop) || VN_IS(nodep, Finish)
                   || VN_IS(nodep, Delay)
                   || VN_IS(nodep, NodeCoverOrAssert) || VN_IS(nodep, PrintTimeScale)
                   || VN_IS(nodep, TimeFormat) || VN_IS(nodep, NodeReadWriteMem)
                   || VN_IS(nodep, SFormat) || VN_IS(nodep, FClose)
                   || VN_IS(nodep, FFlush)) {
            warnNode(nodep, "non-synthesisable statement dropped");
        } else if (AstEventControl* const ep = VN_CAST(nodep, EventControl)) {
            warnNode(nodep, "event control dropped; body kept");
            lowerStmts(ep->stmtsp(), env);
        } else {
            warnNode(nodep, "unsupported statement dropped");
        }
    }

    // ---- assignment ----
    void lowerAssign(AstNodeExpr* lhsp, AstNodeExpr* rhsp, bool blocking, Env& env) {
        if (AstVarRef* const lvp = VN_CAST(lhsp, VarRef)) {
            const auto mit = m_mems.find(lvp->varp());
            if (mit != m_mems.end() && mit->second.asRegs) {
                lowerArrayCopy(mit->second, rhsp, blocking, env);
                return;
            }
        }
        if (AstConcat* const cp = VN_CAST(lhsp, Concat)) {
            // {a, b} = rhs  ->  a = rhs[hi:..]; b = rhs[..:0]
            SExpr rhs = materialize(lowerExpr(rhsp, env));
            std::vector<AstNodeExpr*> parts;
            flattenConcat(cp, parts);
            int lsb = 0;
            for (auto it = parts.rbegin(); it != parts.rend(); ++it) {
                const int w = (*it)->width();
                SExpr slice = rhs;
                slice.text = rhs.text + "[" + std::to_string(lsb) + " +: " + std::to_string(w) + "]";
                slice.width = w;
                slice.isIdent = false;
                slice.isConst = false;
                slice.hasVal = false;
                if (rhs.hasVal) {
                    slice = constExpr(maskTo(rhs.val >> lsb, w), w);
                }
                const SLVal lv = lowerLValue(*it, env);
                if (lv.ok) assignTo(lv, materialize(slice), blocking, env);
                lsb += w;
            }
            return;
        }
        const SLVal lv = lowerLValue(lhsp, env);
        if (!lv.ok) return;
        const SExpr rhs = lowerExpr(rhsp, env);
        assignTo(lv, rhs, blocking, env);
    }
    // `arr = other_arr` / `arr = '{default: v, i: v}` on a register-expanded array
    void lowerArrayCopy(const SMem& dst, AstNodeExpr* rhsp, bool blocking, Env& env) {
        auto elem = [&](int k) {
            SLVal e;
            e.ok = true;
            e.key = dst.regNames[k];
            e.text = e.key;
            e.width = dst.dataWidth;
            return e;
        };
        if (AstVarRef* const rvp = VN_CAST(rhsp, VarRef)) {
            const auto sit = m_mems.find(rvp->varp());
            if (sit != m_mems.end() && sit->second.asRegs && sit->second.depth == dst.depth) {
                for (int k = 0; k < dst.depth; ++k) {
                    setKey(elem(k), materialize(readKey(sit->second.regNames[k], env, true)), blocking, env);
                }
                return;
            }
        }
#if VERILATOR_VERSION_INTEGER >= 5053000  // AstInitArray became AstConsArray (verilator #8809)
        if (AstConsArray* const ip = VN_CAST(rhsp, ConsArray)) {
            for (int k = 0; k < dst.depth; ++k) {
                AstNodeExpr* vp = ip->valuep(static_cast<uint64_t>(k));
#else
        if (AstInitArray* const ip = VN_CAST(rhsp, InitArray)) {
            for (int k = 0; k < dst.depth; ++k) {
                AstNodeExpr* vp = ip->getIndexDefaultedValuep(static_cast<uint64_t>(k));
#endif
                if (!vp) {
                    warnNode(rhsp, "array pattern leaves element " + std::to_string(k) + " of " + dst.name + " unset");
                    continue;
                }
                setKey(elem(k), materialize(resize(lowerExpr(vp, env), dst.dataWidth, false)), blocking, env);
            }
            return;
        }
        if (VN_IS(rhsp, CReset)) {
            for (int k = 0; k < dst.depth; ++k) setKey(elem(k), constExpr(0, dst.dataWidth), blocking, env);
            return;
        }
        warnNode(rhsp, "whole-array assignment to " + dst.name + " from this expression unsupported");
    }
    static void flattenConcat(AstNodeExpr* ep, std::vector<AstNodeExpr*>& out) {
        if (AstConcat* const cp = VN_CAST(ep, Concat)) {
            flattenConcat(cp->lhsp(), out);
            flattenConcat(cp->rhsp(), out);
        } else {
            out.push_back(ep);
        }
    }

    void assignTo(const SLVal& lv, const SExpr& rhsIn, bool blocking, Env& env) {
        SExpr rhs = materialize(rhsIn);
        if (lv.memVarp) {
            // Big memory element write: becomes a write port
            SMem& m = m_mems[lv.memVarp];
            if (!m_seq) warn("memory " + m.name + " written outside a clocked block");
            SMem::Write w;
            w.idx = materialize(lv.idx);
            w.data = rhs;
            w.en = materialize(pathCondition());
            w.clk = m_clk;
            m.writes.push_back(w);
            m.anyWrite = true;
            if (m_seq) m.clk = m_clk;
            return;
        }
        if (lv.sliceDynamic) {
            const int w = lv.width;
            const SExpr idx = materialize(lv.idx);
            for (int lo = 0; lo + w <= lv.baseWidth; lo += w) {
                const SExpr hit = eqConst(idx, static_cast<uint64_t>(lo));
                SLVal e;
                e.ok = true;
                e.key = lv.baseKey + "[" + std::to_string(lo) + "+:" + std::to_string(w) + "]";
                e.text = lv.baseKey + "[" + std::to_string(lo) + " +: " + std::to_string(w) + "]";
                e.width = w;
                const SExpr prior = readKey(e.key, env, true);
                setKey(e, genMux(hit, materialize(prior), rhs, w), blocking, env);
            }
            return;
        }
        if (lv.memDynamic) {
            // Small array with a dynamic index: conditional write to every element
            const SMem& m = m_mems.at(lv.memSmallVarp);
            const SExpr idx = materialize(lv.idx);
            for (int k = 0; k < m.depth; ++k) {
                const std::string& reg = m.regNames[k];
                const SExpr hit = eqConst(idx, static_cast<uint64_t>(k + m.lo));
                const SExpr prior = readKey(reg, env, blocking ? true : false);
                const SExpr v = genMux(hit, prior, rhs, m.dataWidth);
                SLVal e;
                e.ok = true;
                e.key = reg;
                e.text = reg;
                e.width = m.dataWidth;
                setKey(e, v, blocking, env);
            }
            return;
        }
        setKey(lv, rhs, blocking, env);
    }
    void setKey(const SLVal& lv, const SExpr& rhs, bool blocking, Env& env) {
        if (lv.key.find('[') == std::string::npos) {
            const std::string pfx = lv.key + "[";
            auto erasePfx = [&](std::map<std::string, SExpr>& mp) {
                for (auto it = mp.lower_bound(pfx); it != mp.end() && it->first.compare(0, pfx.size(), pfx) == 0;) it = mp.erase(it);
            };
            erasePfx(env.next);
            if (blocking || !m_seq) erasePfx(env.cur);
        }
        env.setNext(lv.key, rhs);
        if (blocking || !m_seq) env.cur[lv.key] = rhs;
    }
    // Value a read of `key` sees now: blocking value if any, else the
    // net / register output itself.
    SExpr readKey(const std::string& key, const Env& env, bool viaCur) {
        const std::map<std::string, SExpr>& mp = viaCur ? env.cur : env.next;
        // Slice entries are erased by a later whole write (setKey), so any
        // present are newer than the whole value and go on top of it.
        auto withSlices = [&](const SExpr& whole) -> SExpr {
            if (key.find('[') != std::string::npos) return whole;
            const std::string pfx = key + "[";
            const auto sit = mp.lower_bound(pfx);
            if (sit != mp.end() && sit->first.compare(0, pfx.size(), pfx) == 0) return assembleFromMap(key, whole, mp);
            return whole;
        };
        {
            const auto it = mp.find(key);
            if (it != mp.end()) return withSlices(it->second);
        }
        {
            std::string base;
            int lo, w;
            if (splitSliceKey(key, base, lo, w)) {
                const auto wit = mp.find(base);
                if (wit != mp.end()) return sliceOf(wit->second, lo, w);
            }
        }
        SExpr e = identExpr(key, widthOfKey(key));
        e.isIdent = key.find('[') == std::string::npos;
        e.refs = {rootIdent(key)};
        for (const std::string& r : keyRefs(key)) e.refs.push_back(r);
        return withSlices(e);
    }

    // ---- lvalues ----
    SLVal lowerLValue(AstNodeExpr* lhsp, Env& env) {
        SLVal lv;
        if (AstVarRef* const vp = VN_CAST(lhsp, VarRef)) {
            const AstVar* const varp = vp->varp();
            const auto ait = m_alias.find(varp);
            if (ait != m_alias.end()) return ait->second;
            const auto mit = m_mems.find(varp);
            if (mit != m_mems.end()) {
                warnNode(lhsp, "whole-array assignment to " + mit->second.name + " unsupported");
                return lv;
            }
            lv.ok = true;
            lv.key = varName(varp);
            lv.text = lv.key;
            lv.width = varp->width();
            return lv;
        }
        if (AstSel* const sp = VN_CAST(lhsp, Sel)) {
            SLVal base = lowerLValue(sp->fromp(), env);
            if (!base.ok) return lv;
            if (base.memVarp || base.memDynamic) {
                warnNode(lhsp, "part-select write into array element with dynamic index unsupported");
                return lv;
            }
            const int w = sp->widthConst();
            const SExpr lsbE = lowerExpr(sp->lsbp(), env);
            if (lsbE.hasVal) {
                const int lsb = static_cast<int>(lsbE.val);
                if (lsb == 0 && w == base.width) return base;  // whole-width select
                lv.ok = true;
                lv.key = base.key + "[" + std::to_string(lsb) + "+:" + std::to_string(w) + "]";
                lv.text = base.text + "[" + std::to_string(lsb) + " +: " + std::to_string(w) + "]";
                lv.width = w;
                lv.refs = base.refs;
                return lv;
            }
            const SExpr idx = materialize(lsbE);
            if (base.key.find('[') == std::string::npos && base.width > 0 && w > 0
                && base.width / w <= MAX_SLICE_SLOTS) {
                // vector[idx +: w] = v  ->  one conditional write per aligned slot
                // (Verilator emits idx as element*w for packed arrays)
                lv.ok = true;
                lv.sliceDynamic = true;
                lv.baseKey = base.key;
                lv.baseWidth = base.width;
                lv.idx = idx;
                lv.width = w;
                lv.key = base.key + "[" + idx.text + "+:" + std::to_string(w) + "]";
                lv.text = base.text + "[" + idx.text + " +: " + std::to_string(w) + "]";
                return lv;
            }
            lv.ok = true;
            lv.key = base.key + "[" + idx.text + "+:" + std::to_string(w) + "]";
            lv.text = base.text + "[" + idx.text + " +: " + std::to_string(w) + "]";
            lv.width = w;
            lv.refs = base.refs;
            addRefs(lv.refs, idx.refs);
            warnNode(lhsp, "dynamic part-select write; later reads in this block see the register value");
            return lv;
        }
        if (AstArraySel* const ap = VN_CAST(lhsp, ArraySel)) {
            const AstVarRef* const vp = VN_CAST(ap->fromp(), VarRef);
            if (!vp) {
                warnNode(lhsp, "multi-dimensional array write unsupported");
                return lv;
            }
            const auto mit = m_mems.find(vp->varp());
            const SExpr idx = lowerExpr(ap->bitp(), env);
            if (mit == m_mems.end()) {
                // Array-typed port: textual element lvalue
                lv.ok = true;
                lv.key = varName(vp->varp()) + "[" + idx.text + "]";
                lv.text = lv.key;
                lv.width = ap->width();
                lv.refs = idx.refs;
                return lv;
            }
            SMem& m = mit->second;
            if (!m.asRegs) {
                lv.ok = true;
                lv.memVarp = vp->varp();
                lv.idx = idx;
                lv.width = m.dataWidth;
                lv.key = m.name + "[" + idx.text + "]";
                lv.text = lv.key;
                return lv;
            }
            if (idx.hasVal) {
                const int64_t k = static_cast<int64_t>(idx.val) - m.lo;
                if (k < 0 || k >= m.depth) {
                    warnNode(lhsp, "constant index out of range for " + m.name);
                    return lv;
                }
                lv.ok = true;
                lv.key = m.regNames[k];
                lv.text = lv.key;
                lv.width = m.dataWidth;
                return lv;
            }
            lv.ok = true;
            lv.memDynamic = true;
            lv.memSmallVarp = vp->varp();
            lv.idx = idx;
            lv.width = m.dataWidth;
            lv.key = m.name + "[" + idx.text + "]";
            lv.text = lv.key;
            return lv;
        }
        warnNode(lhsp, "unsupported assignment target");
        return lv;
    }

    // ---- if / case ----
    void lowerIf(AstNodeIf* ip, Env& env) {
        const SExpr cond = materialize(toBool(lowerExpr(ip->condp(), env)));
        if (cond.hasVal) {
            lowerStmts(cond.val ? ip->thensp() : ip->elsesp(), env);
            return;
        }
        Env thenEnv = env;
        Env elseEnv = env;
        thenEnv.pending.clear();
        elseEnv.pending.clear();
        m_pathCond.emplace_back(cond, false);
        lowerStmts(ip->thensp(), thenEnv);
        m_pathCond.pop_back();
        m_pathCond.emplace_back(cond, true);
        lowerStmts(ip->elsesp(), elseEnv);
        m_pathCond.pop_back();
        mergeBranches(cond, thenEnv, elseEnv, env);
    }

    // Merge two branch environments into env (sv_tran_struct structural_if_as_mux)
    void mergeBranches(const SExpr& cond, Env& thenEnv, Env& elseEnv, Env& env) {
        const SExpr ncond = notBit(cond);
        // Pending halts inside the branches apply only under their branch condition
        for (Env::Pending& p : thenEnv.pending) {
            p.cond = andBits(cond, p.cond);
            env.pending.push_back(p);
        }
        for (Env::Pending& p : elseEnv.pending) {
            p.cond = andBits(ncond, p.cond);
            env.pending.push_back(p);
        }
        thenEnv.pending.clear();
        elseEnv.pending.clear();
        if (thenEnv.halted && !elseEnv.halted) {
            env.pending.push_back({cond, thenEnv.haltTarget, std::make_shared<Env>(thenEnv)});
            env.cur = elseEnv.cur;
            env.next = elseEnv.next;
            env.order = elseEnv.order;
            return;
        }
        if (elseEnv.halted && !thenEnv.halted) {
            env.pending.push_back({ncond, elseEnv.haltTarget, std::make_shared<Env>(elseEnv)});
            env.cur = thenEnv.cur;
            env.next = thenEnv.next;
            env.order = thenEnv.order;
            return;
        }
        if (thenEnv.halted && elseEnv.halted) {
            if (thenEnv.haltTarget != elseEnv.haltTarget) {
                // Different targets: keep the inner one live, record the outer
                env.pending.push_back({cond, thenEnv.haltTarget, std::make_shared<Env>(thenEnv)});
                env.cur = elseEnv.cur;
                env.next = elseEnv.next;
                env.order = elseEnv.order;
                env.halted = true;
                env.haltTarget = elseEnv.haltTarget;
                return;
            }
            env.halted = true;
            env.haltTarget = thenEnv.haltTarget;
        }
        // next: keys driven by either branch
        std::vector<std::string> keys;
        for (const std::string& k : thenEnv.order) keys.push_back(k);
        for (const std::string& k : elseEnv.order) {
            if (!thenEnv.next.count(k)) keys.push_back(k);
        }
        for (const std::string& key : keys) {
            const bool inThen = thenEnv.next.count(key);
            const bool inElse = elseEnv.next.count(key);
            SExpr tv;
            SExpr ev;
            if (inThen) tv = thenEnv.next.at(key);
            if (inElse) ev = elseEnv.next.at(key);
            // A branch that does not write `key` itself may still write it
            // through the other granularity: the whole register when `key`
            // is a slice (reset: x <= CONST; else: x[7:0] <= ...), or slices
            // when `key` is the whole register.  Only then is the value the
            // one from before the branch.
            auto missing = [&](const std::string& k, const Env& b) -> SExpr {
                std::string base;
                int lo, w;
                if (splitSliceKey(k, base, lo, w)) {
                    const auto wit = b.next.find(base);
                    if (wit != b.next.end()) return sliceOf(wit->second, lo, w);
                    return priorNext(k, env);
                }
                const std::string pfx = k + "[";
                const auto sit = b.next.lower_bound(pfx);
                if (sit != b.next.end() && sit->first.compare(0, pfx.size(), pfx) == 0) {
                    return assembleFromMap(k, materialize(priorNext(k, env)), b.next);
                }
                return priorNext(k, env);
            };
            if (!inThen) tv = missing(key, thenEnv);
            if (!inElse) ev = missing(key, elseEnv);
            if (tv.text == ev.text) {
                env.setNext(key, tv);
                continue;
            }
            const SExpr v = genMux(cond, materialize(ev), materialize(tv), widthOfKey(key));
            env.setNext(key, v);
        }
        // cur: what later reads see
        std::set<std::string> ckeys;
        for (const auto& kv : thenEnv.cur) ckeys.insert(kv.first);
        for (const auto& kv : elseEnv.cur) ckeys.insert(kv.first);
        for (const std::string& key : ckeys) {
            const SExpr tv = readKey(key, thenEnv, true);
            const SExpr ev = readKey(key, elseEnv, true);
            if (tv.text == ev.text) {
                env.cur[key] = tv;
                continue;
            }
            env.cur[key] = genMux(cond, materialize(ev), materialize(tv), widthOfKey(key));
        }
    }
    // Value `key` had before a branch that did not assign it
    SExpr priorNext(const std::string& key, const Env& env) {
        const auto it = env.next.find(key);
        if (it != env.next.end()) return it->second;
        {
            std::string base;
            int lo, w;
            if (splitSliceKey(key, base, lo, w)) {
                const auto wit = env.next.find(base);
                if (wit != env.next.end()) return sliceOf(wit->second, lo, w);
            }
        }
        if (m_seq || m_latch) return readKey(key, env, false);  // hold
        warn("Incomplete if for " + key + " - using default 0");
        return constExpr(0, widthOfKey(key));
    }

    // Fold halted alternative paths (returns) back into the live environment
    void foldPending(Env& env, const AstJumpBlock* target) {
        std::vector<Env::Pending> keep;
        std::vector<Env::Pending> fold;
        for (Env::Pending& p : env.pending) {
            if (target == nullptr || p.target == target) {
                fold.push_back(p);
            } else {
                keep.push_back(p);
            }
        }
        env.pending = keep;
        for (auto it = fold.rbegin(); it != fold.rend(); ++it) {
            const Env& h = *it->env;
            std::vector<std::string> keys = env.order;
            for (const std::string& k : h.order) {
                if (!env.next.count(k)) keys.push_back(k);
            }
            for (const std::string& key : keys) {
                const SExpr live = env.next.count(key) ? env.next.at(key) : priorNext(key, env);
                const SExpr hv = h.next.count(key) ? h.next.at(key) : priorNext(key, env);
                if (live.text == hv.text) continue;
                env.setNext(key, genMux(it->cond, materialize(live), materialize(hv),
                                        widthOfKey(key)));
            }
            std::set<std::string> ckeys;
            for (const auto& kv : env.cur) ckeys.insert(kv.first);
            for (const auto& kv : h.cur) ckeys.insert(kv.first);
            for (const std::string& key : ckeys) {
                const SExpr live = readKey(key, env, true);
                const SExpr hv = readKey(key, h, true);
                if (live.text == hv.text) continue;
                env.cur[key] = genMux(it->cond, materialize(live), materialize(hv),
                                      widthOfKey(key));
            }
        }
    }

    // case: each item becomes (expr == c1) | (expr == c2) ... ; items are
    // folded from the last to the first into a mux chain
    // (sv_tran_struct structural_case build_mux_chain), via the generic
    // if-merge so blocking semantics stay right.
    void lowerCase(AstCase* cp, Env& env) {
        const SExpr sel = materialize(lowerExpr(cp->exprp(), env));
        std::vector<std::pair<SExpr, AstCaseItem*>> arms;
        AstCaseItem* defaultp = nullptr;
        for (AstCaseItem* ip = cp->itemsp(); ip; ip = VN_AS(ip->nextp(), CaseItem)) {
            if (ip->isDefault()) {
                defaultp = ip;
                continue;
            }
            SExpr hit = constExpr(0, 1);
            bool first = true;
            for (AstNodeExpr* condp = ip->condsp(); condp;
                 condp = VN_AS(condp->nextp(), NodeExpr)) {
                SExpr one;
                if (VN_IS(condp, InsideRange)) {
                    AstInsideRange* const rp = VN_AS(condp, InsideRange);
                    const SExpr lo = lowerExpr(rp->lhsp(), env);
                    const SExpr hi = lowerExpr(rp->rhsp(), env);
                    one = andBits(genBinary("comparator_gte", sel, lo, sel.width, 1),
                                  genBinary("comparator_lte", sel, hi, sel.width, 1));
                } else {
                    one = caseMatch(cp, sel, condp, env);
                }
                hit = first ? one : orBits(hit, one);
                first = false;
            }
            arms.emplace_back(materialize(hit), ip);
        }
        lowerCaseArms(arms, 0, defaultp, env);
    }
    SExpr orBits(const SExpr& a, const SExpr& b) {
        if (a.hasVal) return a.val ? a : b;
        if (b.hasVal) return b.val ? b : a;
        return genBinary("bitwise_or", a, b, 1, 1);
    }
    // One case label: plain equality, or a masked compare for casez/casex
    // wildcard bits.
    SExpr caseMatch(AstCase* cp, const SExpr& sel, AstNodeExpr* condp, Env& env) {
        if (const AstConst* const kp = VN_CAST(condp, Const)) {
            const V3Number& num = kp->num();
            if ((cp->casez() || cp->casex()) && num.isFourState() && num.width() <= 64) {
                uint64_t mask = 0;
                uint64_t value = 0;
                for (int b = 0; b < num.width(); ++b) {
                    const bool wild = cp->casex() ? num.bitIsXZ(b) : num.bitIsZ(b);
                    if (!wild) {
                        mask |= 1ULL << b;
                        if (num.bitIs1(b)) value |= 1ULL << b;
                    }
                }
                const SExpr masked = genBinary("bitwise_and", sel, constExpr(mask, sel.width),
                                               sel.width, sel.width);
                return genBinary("comparator_eq", masked, constExpr(value, sel.width),
                                 sel.width, 1);
            }
        }
        const SExpr c = lowerExpr(condp, env);
        if (sel.hasVal && c.hasVal) return constExpr(sel.val == maskTo(c.val, sel.width), 1);
        return genBinary("comparator_eq", sel, c, sel.width, 1);
    }
    void lowerCaseArms(std::vector<std::pair<SExpr, AstCaseItem*>>& arms, size_t i,
                       AstCaseItem* defaultp, Env& env) {
        if (i == arms.size()) {
            if (defaultp) lowerStmts(defaultp->stmtsp(), env);
            return;
        }
        const SExpr& hit = arms[i].first;
        if (hit.hasVal) {
            if (hit.val) {
                lowerStmts(arms[i].second->stmtsp(), env);
            } else {
                lowerCaseArms(arms, i + 1, defaultp, env);
            }
            return;
        }
        Env thenEnv = env;
        Env elseEnv = env;
        thenEnv.pending.clear();
        elseEnv.pending.clear();
        m_pathCond.emplace_back(hit, false);
        lowerStmts(arms[i].second->stmtsp(), thenEnv);
        m_pathCond.pop_back();
        m_pathCond.emplace_back(hit, true);
        lowerCaseArms(arms, i + 1, defaultp, elseEnv);
        m_pathCond.pop_back();
        mergeBranches(hit, thenEnv, elseEnv, env);
    }

    // ---- loops (sv_transform unroll_for_loop, generalised) ----
    void lowerLoop(AstLoop* lp, Env& env) {
        AstLoopTest* const firstTestp = VN_CAST(lp->stmtsp(), LoopTest);
        AstLoopTest* lastTestp = nullptr;
        if (!firstTestp && lp->stmtsp()) {
            AstNode* lastp = lp->stmtsp();
            while (lastp->nextp()) lastp = lastp->nextp();
            lastTestp = VN_CAST(lastp, LoopTest);
        }
        for (int iter = 0;; ++iter) {
            if (iter >= MAX_UNROLL) {
                warnNode(lp, "loop exceeds " + std::to_string(MAX_UNROLL)
                                 + " iterations; remaining iterations dropped");
                return;
            }
            if (firstTestp) {
                const SExpr c = lowerExpr(firstTestp->condp(), env);
                if (!c.hasVal) {
                    warnNode(lp, "loop with non-constant bound cannot be unrolled; dropped");
                    return;
                }
                if (!c.val) return;
            }
            for (AstNode* sp = lp->stmtsp(); sp; sp = sp->nextp()) {
                if (VN_IS(sp, LoopTest)) {
                    if (sp == lastTestp) {
                        const SExpr c = lowerExpr(lastTestp->condp(), env);
                        if (!c.hasVal) {
                            warnNode(lp, "do-while loop with non-constant test; dropped");
                            return;
                        }
                        if (!c.val) return;
                    }
                    continue;
                }
                lowerStmt(sp, env);
                if (env.halted) break;
            }
            if (env.halted) {
                // `break` targets a JumpBlock enclosing the loop; a `continue`
                // targets a block inside the body (already resolved).
                return;
            }
            lowerStmts(lp->contsp(), env);
        }
    }

    // ---- function / task inlining (sv_transform inline_function / inline_task) ----
    SExpr inlineCall(AstNodeFTaskRef* refp, Env& env, const AstVar** retVarOut) {
        AstNodeFTask* const taskp = refp->taskp();
        SExpr zero = constExpr(0, refp->width() > 0 ? refp->width() : 1);
        if (!taskp) {
            warnNode(refp, "unresolved call to " + refp->prettyName());
            return zero;
        }
        if (taskp->dpiImport() || taskp->prototype()) {
            warnNode(refp, "DPI / prototype call to " + refp->prettyName() + " replaced by 0");
            return zero;
        }
        if (m_inlineDepth >= MAX_INLINE_DEPTH) {
            warnNode(refp, "inlining depth exceeded at " + refp->prettyName());
            return zero;
        }
        ++m_inlineDepth;
        const int callId = ++m_callSeq;
        const std::string prefix = "fn" + std::to_string(callId) + "__" + sanitizeName(taskp->prettyName()) + "__";
        // Formals in declaration order
        std::vector<AstVar*> formals;
        std::vector<AstVar*> locals;
        collectFtaskVars(taskp->stmtsp(), formals, locals);
        AstVar* const retp = VN_CAST(taskp->fvarp(), Var);
        // Arguments (positional, or by name)
        std::vector<AstNodeExpr*> args(formals.size(), nullptr);
        {
            size_t pos = 0;
            for (AstArg* ap = refp->argsp(); ap; ap = VN_AS(ap->nextp(), Arg)) {
                size_t idx = pos;
                if (!ap->name().empty()) {
                    for (size_t i = 0; i < formals.size(); ++i) {
                        if (formals[i]->name() == ap->name()) idx = i;
                    }
                }
                if (idx < args.size()) args[idx] = ap->exprp();
                ++pos;
            }
        }
        // Bind formals
        std::vector<std::pair<const AstVar*, bool>> bound;  // (var, wasBind)
        std::vector<std::pair<const AstVar*, SExpr>> savedBind;
        std::vector<std::pair<const AstVar*, SLVal>> savedAlias;
        std::vector<std::pair<const AstVar*, std::string>> savedLocal;
        for (size_t i = 0; i < formals.size(); ++i) {
            AstVar* const fp = formals[i];
            if (fp->direction().isWritable()) {
                SLVal lv;
                if (args[i]) lv = lowerLValue(args[i], env);
                if (!lv.ok) {
                    warnNode(refp, "unconnected output argument " + fp->prettyName());
                    lv.ok = true;
                    lv.key = prefix + sanitizeName(fp->prettyName());
                    lv.text = lv.key;
                    lv.width = fp->width();
                    m_widths[lv.key] = fp->width();
                }
                if (m_alias.count(fp)) savedAlias.emplace_back(fp, m_alias[fp]);
                m_alias[fp] = lv;
                if (fp->direction().isInout() && args[i]) {
                    // inout: initial value is the argument's current value
                    const SExpr v = materialize(lowerExpr(args[i], env));
                    env.cur[lv.key] = v;
                }
            } else {
                SExpr v = args[i] ? materialize(lowerExpr(args[i], env)) : constExpr(0, fp->width());
                if (m_bind.count(fp)) savedBind.emplace_back(fp, m_bind[fp]);
                m_bind[fp] = v;
            }
        }
        for (AstVar* const lp : locals) {
            if (m_localKey.count(lp)) savedLocal.emplace_back(lp, m_localKey[lp]);
            const std::string key = prefix + sanitizeName(lp->prettyName());
            m_localKey[lp] = key;
            m_widths[key] = lp->width();
        }
        std::string retKey;
        if (retp) {
            if (m_localKey.count(retp)) savedLocal.emplace_back(retp, m_localKey[retp]);
            retKey = prefix + sanitizeName(retp->prettyName());
            m_localKey[retp] = retKey;
            m_widths[retKey] = retp->width();
        }
        // Execute the body on a copy of the environment so returns fold locally
        Env fenv;
        fenv.cur = env.cur;
        fenv.next = env.next;
        fenv.order = env.order;
        VL_RESTORER(m_seq);
        VL_RESTORER(m_latch);
        const bool wasSeq = m_seq;
        m_seq = false;  // function body: all assignments are blocking temporaries
        m_latch = false;
        {
            // Body statements (skipping the formal/local declarations)
            lowerStmts(taskp->stmtsp(), fenv);
            foldPending(fenv, nullptr);
            fenv.halted = false;
        }
        m_seq = wasSeq;
        SExpr result = zero;
        if (retp) {
            const auto it = fenv.cur.find(retKey);
            if (it != fenv.cur.end()) {
                result = it->second;
            } else {
                const SExpr r = assembleSlices(retKey, constExpr(0, retp->width()), fenv);
                if (r.isConst) warnNode(refp, "function " + refp->prettyName() + " never assigns its return value");
                result = r;
            }
        }
        // Propagate side effects on module-level keys (tasks writing outputs)
        for (const auto& kv : fenv.cur) {
            if (kv.first.compare(0, prefix.size(), prefix) == 0) continue;
            env.cur[kv.first] = kv.second;
        }
        for (const std::string& k : fenv.order) {
            if (k.compare(0, prefix.size(), prefix) == 0) continue;
            env.setNext(k, fenv.next.at(k));
        }
        // Unbind
        for (AstVar* const fp : formals) {
            m_bind.erase(fp);
            m_alias.erase(fp);
        }
        for (const auto& kv : savedBind) m_bind[kv.first] = kv.second;
        for (const auto& kv : savedAlias) m_alias[kv.first] = kv.second;
        for (AstVar* const lp : locals) m_localKey.erase(lp);
        if (retp) m_localKey.erase(retp);
        for (const auto& kv : savedLocal) m_localKey[kv.first] = kv.second;
        --m_inlineDepth;
        if (retVarOut) *retVarOut = retp;
        return result;
    }
    static void collectFtaskVars(AstNode* nodep, std::vector<AstVar*>& formals,
                                 std::vector<AstVar*>& locals) {
        for (; nodep; nodep = nodep->nextp()) {
            if (AstVar* const vp = VN_CAST(nodep, Var)) {
                if (vp->isIO()) {
                    formals.push_back(vp);
                } else {
                    locals.push_back(vp);
                }
            } else if (AstBegin* const bp = VN_CAST(nodep, Begin)) {
                collectFtaskVars(bp->declsp(), formals, locals);
                collectFtaskVars(bp->stmtsp(), formals, locals);
            } else if (AstNodeIf* const ip = VN_CAST(nodep, NodeIf)) {
                collectFtaskVars(ip->thensp(), formals, locals);
                collectFtaskVars(ip->elsesp(), formals, locals);
            } else if (AstJumpBlock* const jp = VN_CAST(nodep, JumpBlock)) {
                collectFtaskVars(jp->stmtsp(), formals, locals);
            } else if (AstLoop* const lp = VN_CAST(nodep, Loop)) {
                collectFtaskVars(lp->stmtsp(), formals, locals);
            } else if (AstCase* const cp = VN_CAST(nodep, Case)) {
                for (AstCaseItem* ip = cp->itemsp(); ip; ip = VN_AS(ip->nextp(), CaseItem)) {
                    collectFtaskVars(ip->stmtsp(), formals, locals);
                }
            }
        }
    }
    void inlineTask(AstTaskRef* refp, Env& env) { inlineCall(refp, env, nullptr); }

    //------------------------------------------------------------------
    // Expressions (sv_tran_struct structural_expr with widths from the AST)

    SExpr lowerExpr(AstNodeExpr* nodep, Env& env) {
        if (!nodep) return constExpr(0, 1);
        const int width = nodep->width() > 0 ? nodep->width() : 1;
        if (AstConst* const cp = VN_CAST(nodep, Const)) return lowerConst(cp);
        if (AstVarRef* const vp = VN_CAST(nodep, VarRef)) return lowerVarRef(vp, env);
        if (AstEnumItemRef* const ep = VN_CAST(nodep, EnumItemRef)) {
            if (ep->itemp()) {
                if (AstConst* const cp = VN_CAST(ep->itemp()->valuep(), Const)) {
                    SExpr e = lowerConst(cp);
                    e.width = width;
                    return e;
                }
            }
            warnNode(nodep, "enum item without constant value");
            return constExpr(0, width);
        }
        if (AstCond* const cp = VN_CAST(nodep, Cond)) {
            const SExpr sel = materialize(toBool(lowerExpr(cp->condp(), env)));
            if (sel.hasVal) return lowerExpr(sel.val ? cp->thenp() : cp->elsep(), env);
            const SExpr in1 = materialize(lowerExpr(cp->thenp(), env));
            const SExpr in0 = materialize(lowerExpr(cp->elsep(), env));
            return genMux(sel, in0, in1, width);
        }
        if (AstSel* const sp = VN_CAST(nodep, Sel)) return lowerSel(sp, env);
        if (AstArraySel* const ap = VN_CAST(nodep, ArraySel)) return lowerArraySel(ap, env);
        if (AstConcat* const cp = VN_CAST(nodep, Concat)) {
            std::vector<AstNodeExpr*> parts;
            flattenConcat(cp, parts);
            std::string text = "{";
            std::vector<std::string> refs;
            bool allConst = true;
            uint64_t val = 0;
            int total = 0;
            for (size_t i = 0; i < parts.size(); ++i) {
                const SExpr p = materialize(lowerExpr(parts[i], env));
                if (i) text += ", ";
                text += p.text;
                addRefs(refs, p.refs);
                if (p.hasVal && total + p.width <= 64) {
                    val = (val << p.width) | maskTo(p.val, p.width);
                } else {
                    allConst = false;
                }
                total += p.width;
            }
            text += "}";
            if (allConst && total <= 64) return constExpr(val, width);
            SExpr e;
            e.text = text;
            e.width = width;
            e.refs = refs;
            const SExpr w = newWire(width);
            addAssign(w.text, e);
            return w;
        }
        if (AstReplicate* const rp = VN_CAST(nodep, Replicate)) {
            const SExpr src = materialize(lowerExpr(rp->srcp(), env));
            const SExpr cnt = lowerExpr(rp->countp(), env);
            if (!cnt.hasVal) {
                warnNode(nodep, "replicate with non-constant count");
                return constExpr(0, width);
            }
            if (src.hasVal && width <= 64) {
                uint64_t v = 0;
                for (uint64_t i = 0; i < cnt.val; ++i) v = (v << src.width) | src.val;
                return constExpr(v, width);
            }
            SExpr e;
            e.text = "{" + std::to_string(cnt.val) + "{" + src.text + "}}";
            e.width = width;
            e.refs = src.refs;
            const SExpr w = newWire(width);
            addAssign(w.text, e);
            return w;
        }
        if (AstFuncRef* const fp = VN_CAST(nodep, FuncRef)) {
            SExpr r = inlineCall(fp, env, nullptr);
            if (r.width != width) r = resize(r, width, r.isSigned);
            return r;
        }
        if (AstNodeUniop* const up = VN_CAST(nodep, NodeUniop)) return lowerUniop(up, env);
        if (AstNodeBiop* const bp = VN_CAST(nodep, NodeBiop)) return lowerBiop(bp, env);
        if (VN_IS(nodep, CastSize) || VN_IS(nodep, CastWrap)) {
            AstNodeExpr* const inner = VN_IS(nodep, CastSize)
                                           ? VN_AS(nodep, CastSize)->lhsp()
                                           : VN_AS(nodep, CastWrap)->lhsp();
            return resize(lowerExpr(inner, env), width, nodep->isSigned());
        }
        if (VN_IS(nodep, ExprStmt)) {
            AstExprStmt* const ep = VN_AS(nodep, ExprStmt);
            lowerStmts(ep->stmtsp(), env);
            return lowerExpr(ep->resultp(), env);
        }
        if (VN_IS(nodep, CReset)) return constExpr(0, width);
        if (AstNodeStream* const stp = VN_CAST(nodep, NodeStream)) {
            // {<< S {x}} reverses the order of S-bit slices; {>> S {x}} is the identity
            const SExpr src = materialize(lowerExpr(stp->lhsp(), env));
            const SExpr slice = lowerExpr(stp->rhsp(), env);
            if (VN_IS(stp, StreamR) || !slice.hasVal || slice.val == 0) {
                return resize(src, width, false);
            }
            const int sw = static_cast<int>(slice.val);
            if (src.hasVal && src.width <= 64) {
                uint64_t v = 0;
                int outPos = 0;
                for (int lo = src.width - sw; lo > -sw; lo -= sw) {
                    const int l = std::max(lo, 0);
                    const int n = std::min(sw, src.width - l);
                    v |= maskTo(src.val >> l, n) << outPos;
                    outPos += n;
                }
                return constExpr(v, width);
            }
            std::string text = "{";
            bool first = true;
            for (int lo = 0; lo < src.width; lo += sw) {
                const int n = std::min(sw, src.width - lo);
                if (!first) text += ", ";
                first = false;
                text += src.text + "[" + std::to_string(lo + n - 1) + ":" + std::to_string(lo) + "]";
            }
            text += "}";
            SExpr e;
            e.text = text;
            e.width = src.width;
            e.refs = src.refs;
            const SExpr w = newWire(src.width);
            addAssign(w.text, e);
            return resize(w, width, false);
        }
        if (VN_IS(nodep, VarXRef)) {
            warnNode(nodep, "hierarchical reference replaced by 0");
            return constExpr(0, width);
        }
        if (VN_IS(nodep, StructSel) || VN_IS(nodep, MemberSel)) {
            warnNode(nodep, "unpacked struct member select replaced by 0");
            return constExpr(0, width);
        }
        warnNode(nodep, "unsupported expression replaced by 0");
        return constExpr(0, width);
    }

    SExpr lowerConst(AstConst* cp) {
        const V3Number& num = cp->num();
        SExpr e;
        e.isConst = true;
        e.width = num.width();
        e.isSigned = num.isSigned();
        if (num.isString() || num.isDouble()) {
            e.text = num.ascii(true, true);
            e.width = cp->width() > 0 ? cp->width() : 1;
            return e;
        }
        if (num.isFourState()) {
            // X/Z bits are not hardware: clean them to 0 like the OCaml
            // flow's parse_const_value does
            if (num.width() <= 64) {
                uint64_t v = 0;
                for (int b = 0; b < num.width(); ++b) if (num.bitIs1(b)) v |= 1ULL << b;
                return constExpr(v, num.width(), num.isSigned());
            }
            std::string t = num.ascii(true, true);
            for (char& c : t) if (c == 'x' || c == 'X' || c == 'z' || c == 'Z' || c == '?') c = '0';
            e.text = t;
            return e;
        }
        e.text = num.ascii(true, true);
        if (num.width() <= 64) {
            e.hasVal = true;
            e.val = maskTo(num.toUQuad(), num.width());
        }
        return e;
    }

    SExpr lowerVarRef(AstVarRef* vp, Env& env) {
        const AstVar* const varp = vp->varp();
        const auto bit = m_bind.find(varp);
        if (bit != m_bind.end()) return bit->second;
        const auto ait = m_alias.find(varp);
        if (ait != m_alias.end()) return readKey(ait->second.key, env, true);
        const auto mit = m_mems.find(varp);
        if (mit != m_mems.end()) {
            warnNode(vp, "whole-array read of " + mit->second.name + " replaced by 0");
            return constExpr(0, vp->width() > 0 ? vp->width() : 1);
        }
        const std::string name = varName(varp);
        const auto cit = env.cur.find(name);
        // a whole value with slice writes after it (word = x; word[8*k +: 8] = b;):
        // the slices go on top -- setKey erases older slices on a whole write
        if (cit != env.cur.end()) return assembleFromMap(name, cit->second, env.cur);
        SExpr e = identExpr(name, varp->width());
        e.isSigned = varp->isSigned();
        return assembleSlices(name, e, env);
    }
    // `x[lo+:w] = v` entries in the environment override those bits of x
    SExpr assembleSlices(const std::string& name, const SExpr& whole, const Env& env) {
        return assembleFromMap(name, whole, env.cur);
    }
    SExpr assembleSlicesOld(const std::string& name, const SExpr& whole, const Env& env) {
        const std::string pfx = name + "[";
        std::vector<std::pair<int, std::pair<int, SExpr>>> slices;  // (lo, (w, value))
        for (auto it = env.cur.lower_bound(pfx); it != env.cur.end() && it->first.compare(0, pfx.size(), pfx) == 0; ++it) {
            const std::string rest = it->first.substr(pfx.size());
            const size_t p = rest.find("+:");
            if (p == std::string::npos) continue;
            char* endp = nullptr;
            const long lo = std::strtol(rest.c_str(), &endp, 10);
            if (endp == rest.c_str() || *endp != '+') continue;  // dynamic index
            const int w = std::atoi(rest.c_str() + p + 2);
            slices.emplace_back(static_cast<int>(lo), std::make_pair(w, it->second));
        }
        if (slices.empty()) return whole;
        std::sort(slices.begin(), slices.end(), [](const auto& a, const auto& b) { return a.first < b.first; });
        const SExpr base = materialize(whole);
        std::string text = "{";
        std::vector<std::string> refs;
        int pos = whole.width;
        bool first = true;
        auto piece = [&](const std::string& t, const std::vector<std::string>& r) {
            if (!first) text += ", ";
            first = false;
            text += t;
            addRefs(refs, r);
        };
        for (auto it = slices.rbegin(); it != slices.rend(); ++it) {
            const int lo = it->first;
            const int w = it->second.first;
            if (lo + w > pos) continue;  // overlapping: keep the later-sorted one
            if (lo + w < pos) {
                piece(base.text + "[" + std::to_string(pos - 1) + ":" + std::to_string(lo + w) + "]", base.refs);
            }
            const SExpr v = materialize(it->second.second);
            piece(v.text, v.refs);
            pos = lo;
        }
        if (pos > 0) piece(base.text + "[" + std::to_string(pos - 1) + ":0]", base.refs);
        text += "}";
        SExpr e;
        e.text = text;
        e.width = whole.width;
        e.refs = refs;
        const SExpr w = newWire(whole.width);
        addAssign(w.text, e);
        return w;
    }

    SExpr lowerSel(AstSel* sp, Env& env) {
        const int w = sp->widthConst();
        SExpr base = materialize(lowerExpr(sp->fromp(), env));
        const SExpr lsbE = lowerExpr(sp->lsbp(), env);
        if (lsbE.hasVal) {
            const int lsb = static_cast<int>(lsbE.val);
            if (base.hasVal) return constExpr(maskTo(base.val >> lsb, w), w);
            if (lsb == 0 && w == base.width) return base;  // whole-width select (e.g. x[0] of a 1-bit x)
            if (base.isConst) {
                const SExpr wb = newWire(base.width);
                addAssign(wb.text, base);
                base = wb;
            }
            // Partial key hit: a blocking write to exactly this slice
            const std::string key = base.text + "[" + std::to_string(lsb) + "+:" + std::to_string(w) + "]";
            const auto it = env.cur.find(key);
            if (it != env.cur.end()) return it->second;
            SExpr e;
            if (w == 1) {
                e.text = base.text + "[" + std::to_string(lsb) + "]";
            } else {
                e.text = base.text + "[" + std::to_string(lsb + w - 1) + ":" + std::to_string(lsb) + "]";
            }
            e.width = w;
            e.refs = base.refs;
            return e;
        }
        const SExpr idx = materialize(lsbE);
        if (base.isConst) {
            const SExpr wb = newWire(base.width);
            addAssign(wb.text, base);
            base = wb;
        }
        SExpr e;
        e.text = base.text + "[" + idx.text + " +: " + std::to_string(w) + "]";
        e.width = w;
        e.refs = base.refs;
        addRefs(e.refs, idx.refs);
        return e;
    }

    SExpr lowerArraySel(AstArraySel* ap, Env& env) {
        const int width = ap->width() > 0 ? ap->width() : 1;
        const AstVarRef* const vp = VN_CAST(ap->fromp(), VarRef);
        if (!vp) {
            warnNode(ap, "multi-dimensional array read replaced by 0");
            return constExpr(0, width);
        }
        const SExpr idx = materialize(lowerExpr(ap->bitp(), env));
        const auto mit = m_mems.find(vp->varp());
        if (mit == m_mems.end()) {
            // array-typed port
            SExpr e;
            e.text = varName(vp->varp()) + "[" + idx.text + "]";
            e.width = width;
            e.refs = {varName(vp->varp())};
            addRefs(e.refs, idx.refs);
            return e;
        }
        SMem& m = mit->second;
        if (m.asRegs) {
            if (idx.hasVal) {
                const int64_t k = static_cast<int64_t>(idx.val) - m.lo;
                if (k < 0 || k >= m.depth) {
                    warnNode(ap, "constant index out of range for " + m.name);
                    return constExpr(0, width);
                }
                return readKey(m.regNames[k], env, true);
            }
            // mux chain over the elements
            SExpr acc = readKey(m.regNames[0], env, true);
            for (int k = 1; k < m.depth; ++k) {
                const SExpr hit = eqConst(idx, static_cast<uint64_t>(k + m.lo));
                acc = genMux(hit, materialize(acc), materialize(readKey(m.regNames[k], env, true)),
                             m.dataWidth);
            }
            return acc;
        }
        // Big memory: one read port per distinct index expression
        size_t port = m.readIdx.size();
        for (size_t i = 0; i < m.readIdx.size(); ++i) {
            if (m.readIdx[i].text == idx.text) {
                port = i;
                break;
            }
        }
        if (port == m.readIdx.size()) m.readIdx.push_back(idx);
        const std::string rd = m.name + "_rdata" + std::to_string(port + 1);
        m_widths[rd] = m.dataWidth;
        m_readPorts[rd] = {vp->varp(), port};
        return identExpr(rd, m.dataWidth);
    }

    // Zero/sign extend or truncate to `width`
    SExpr resize(const SExpr& in, int width, bool signExtend) {
        if (in.width == width) return in;
        if (in.hasVal) {
            uint64_t v = in.val;
            if (signExtend && in.width < width) v = static_cast<uint64_t>(signExt(v, in.width));
            return constExpr(maskTo(v, width), width, signExtend);
        }
        const SExpr src = materialize(in);
        SExpr e;
        if (width < in.width) {
            e.text = src.text + "[" + std::to_string(width - 1) + ":0]";
        } else if (signExtend) {
            e.text = "{{" + std::to_string(width - in.width) + "{" + src.text + "["
                     + std::to_string(in.width - 1) + "]}}, " + src.text + "}";
        } else {
            e.text = "{{" + std::to_string(width - in.width) + "{1'b0}}, " + src.text + "}";
        }
        e.width = width;
        e.refs = src.refs;
        e.isSigned = signExtend;
        const SExpr w = newWire(width);
        addAssign(w.text, e);
        return w;
    }

    SExpr lowerUniop(AstNodeUniop* up, Env& env) {
        const int width = up->width() > 0 ? up->width() : 1;
        SExpr a = lowerExpr(up->lhsp(), env);
        if (VN_IS(up, Extend)) return resize(a, width, false);
        if (VN_IS(up, ExtendS)) return resize(a, width, true);
        if (VN_IS(up, Signed) || VN_IS(up, Unsigned)) {
            a.isSigned = VN_IS(up, Signed);
            return a;
        }
        if (VN_IS(up, Not)) {
            if (a.hasVal) return constExpr(~a.val, width);
            return genUnary("bitwise_not", materialize(a), width, width);
        }
        if (VN_IS(up, LogNot)) {
            if (a.hasVal) return constExpr(a.val ? 0 : 1, 1);
            return genUnary("logical_not", materialize(toBool(a)), 1, 1);
        }
        if (VN_IS(up, Negate)) {
            if (a.hasVal) return constExpr(0 - a.val, width);
            return genUnary("negator", materialize(a), width, width);
        }
        if (VN_IS(up, RedAnd)) {
            if (a.hasVal) return constExpr(maskTo(a.val, a.width) == maskTo(~0ULL, a.width), 1);
            return genUnary("reduction_and", materialize(a), a.width, 1);
        }
        if (VN_IS(up, RedOr)) {
            if (a.hasVal) return constExpr(a.val != 0, 1);
            return genUnary("reduction_or", materialize(a), a.width, 1);
        }
        if (VN_IS(up, RedXor)) {
            if (a.hasVal) return constExpr(__builtin_popcountll(a.val) & 1, 1);
            return genUnary("reduction_xor", materialize(a), a.width, 1);
        }
        if (VN_IS(up, CLog2)) {
            if (a.hasVal) {
                int r = 0;
                while ((1ULL << r) < a.val && r < 64) ++r;
                return constExpr(r, width);
            }
            warnNode(up, "$clog2 of non-constant replaced by 0");
            return constExpr(0, width);
        }
        if (VN_IS(up, CountOnes)) {
            if (a.hasVal) return constExpr(__builtin_popcountll(a.val), width);
        }
        if (VN_IS(up, IsUnknown)) return constExpr(0, 1);  // no X in hardware
        warnNode(up, "unsupported unary operator replaced by operand");
        return resize(a, width, false);
    }

    struct BiopInfo final {
        const char* prim;
        bool cmp;  // 1-bit result, WIDTH = operand width
        bool shift;  // WIDTH = lhs width
        bool logical;  // operands reduced to 1 bit first
        bool isSigned;
    };
    static bool biopInfo(AstNodeBiop* bp, BiopInfo& info) {
        info = {"", false, false, false, false};
        if (VN_IS(bp, Add)) info.prim = "adder";
        else if (VN_IS(bp, Sub)) info.prim = "subtractor";
        else if (VN_IS(bp, Mul)) info.prim = "multiplier";
        else if (VN_IS(bp, MulS)) { info.prim = "multiplier_signed"; info.isSigned = true; }
        else if (VN_IS(bp, Div)) info.prim = "divider";
        else if (VN_IS(bp, DivS)) { info.prim = "divider_signed"; info.isSigned = true; }
        else if (VN_IS(bp, ModDiv)) info.prim = "modulo";
        else if (VN_IS(bp, ModDivS)) { info.prim = "modulo_signed"; info.isSigned = true; }
        else if (VN_IS(bp, And)) info.prim = "bitwise_and";
        else if (VN_IS(bp, Or)) info.prim = "bitwise_or";
        else if (VN_IS(bp, Xor)) info.prim = "bitwise_xor";
        else if (VN_IS(bp, LogAnd)) { info.prim = "bitwise_and"; info.logical = true; }
        else if (VN_IS(bp, LogOr)) { info.prim = "bitwise_or"; info.logical = true; }
        else if (VN_IS(bp, Eq) || VN_IS(bp, EqCase) || VN_IS(bp, EqWild)) { info.prim = "comparator_eq"; info.cmp = true; }
        else if (VN_IS(bp, Neq) || VN_IS(bp, NeqCase) || VN_IS(bp, NeqWild)) { info.prim = "comparator_neq"; info.cmp = true; }
        else if (VN_IS(bp, Lt)) { info.prim = "comparator_lt"; info.cmp = true; }
        else if (VN_IS(bp, LtS)) { info.prim = "comparator_lt_signed"; info.cmp = true; info.isSigned = true; }
        else if (VN_IS(bp, Lte)) { info.prim = "comparator_lte"; info.cmp = true; }
        else if (VN_IS(bp, LteS)) { info.prim = "comparator_lte_signed"; info.cmp = true; info.isSigned = true; }
        else if (VN_IS(bp, Gt)) { info.prim = "comparator_gt"; info.cmp = true; }
        else if (VN_IS(bp, GtS)) { info.prim = "comparator_gt_signed"; info.cmp = true; info.isSigned = true; }
        else if (VN_IS(bp, Gte)) { info.prim = "comparator_gte"; info.cmp = true; }
        else if (VN_IS(bp, GteS)) { info.prim = "comparator_gte_signed"; info.cmp = true; info.isSigned = true; }
        else if (VN_IS(bp, ShiftL)) { info.prim = "shifter_left"; info.shift = true; }
        else if (VN_IS(bp, ShiftR)) { info.prim = "shifter_right"; info.shift = true; }
        else if (VN_IS(bp, ShiftRS)) { info.prim = "shifter_right_arith"; info.shift = true; info.isSigned = true; }
        else return false;
        return true;
    }

    // Constant folding (sv_transform try_eval_const, extended)
    static bool foldBiop(AstNodeBiop* bp, const SExpr& a, const SExpr& b, int width, uint64_t& out) {
        if (!a.hasVal || !b.hasVal || width > 64) return false;
        const uint64_t x = a.val;
        const uint64_t y = b.val;
        const int64_t sx = signExt(x, a.width);
        const int64_t sy = signExt(y, b.width);
        if (VN_IS(bp, Add)) out = x + y;
        else if (VN_IS(bp, Sub)) out = x - y;
        else if (VN_IS(bp, Mul)) out = x * y;
        else if (VN_IS(bp, MulS)) out = static_cast<uint64_t>(sx * sy);
        else if (VN_IS(bp, Div)) { if (!y) return false; out = x / y; }
        else if (VN_IS(bp, DivS)) { if (!sy) return false; out = static_cast<uint64_t>(sx / sy); }
        else if (VN_IS(bp, ModDiv)) { if (!y) return false; out = x % y; }
        else if (VN_IS(bp, ModDivS)) { if (!sy) return false; out = static_cast<uint64_t>(sx % sy); }
        else if (VN_IS(bp, And)) out = x & y;
        else if (VN_IS(bp, Or)) out = x | y;
        else if (VN_IS(bp, Xor)) out = x ^ y;
        else if (VN_IS(bp, LogAnd)) out = (x != 0) && (y != 0);
        else if (VN_IS(bp, LogOr)) out = (x != 0) || (y != 0);
        else if (VN_IS(bp, Eq) || VN_IS(bp, EqCase) || VN_IS(bp, EqWild)) out = x == y;
        else if (VN_IS(bp, Neq) || VN_IS(bp, NeqCase) || VN_IS(bp, NeqWild)) out = x != y;
        else if (VN_IS(bp, Lt)) out = x < y;
        else if (VN_IS(bp, LtS)) out = sx < sy;
        else if (VN_IS(bp, Lte)) out = x <= y;
        else if (VN_IS(bp, LteS)) out = sx <= sy;
        else if (VN_IS(bp, Gt)) out = x > y;
        else if (VN_IS(bp, GtS)) out = sx > sy;
        else if (VN_IS(bp, Gte)) out = x >= y;
        else if (VN_IS(bp, GteS)) out = sx >= sy;
        else if (VN_IS(bp, ShiftL)) out = y >= 64 ? 0 : x << y;
        else if (VN_IS(bp, ShiftR)) out = y >= 64 ? 0 : x >> y;
        else if (VN_IS(bp, ShiftRS)) out = static_cast<uint64_t>(y >= 64 ? (sx < 0 ? -1 : 0) : sx >> y);
        else if (VN_IS(bp, Pow)) {
            uint64_t r = 1;
            for (uint64_t i = 0; i < y && i < 64; ++i) r *= x;
            out = r;
        } else return false;
        out = maskTo(out, width);
        return true;
    }

    SExpr lowerBiop(AstNodeBiop* bp, Env& env) {
        const int width = bp->width() > 0 ? bp->width() : 1;
        SExpr a = lowerExpr(bp->lhsp(), env);
        SExpr b = lowerExpr(bp->rhsp(), env);
        uint64_t folded = 0;
        if (foldBiop(bp, a, b, width, folded)) return constExpr(folded, width, bp->isSigned());
        BiopInfo info;
        if (!biopInfo(bp, info)) {
            if (VN_IS(bp, Pow) || VN_IS(bp, PowSS) || VN_IS(bp, PowSU) || VN_IS(bp, PowUS)) {
                warnNode(bp, "non-constant power operator replaced by 0");
            } else {
                warnNode(bp, "unsupported binary operator replaced by 0");
            }
            return constExpr(0, width);
        }
        if (info.logical) {
            a = toBool(a);
            b = toBool(b);
        }
        a = materialize(a);
        b = materialize(b);
        int opWidth = width;
        int outWidth = width;
        if (info.cmp) {
            opWidth = std::max(a.width, b.width);
            outWidth = 1;
        } else if (info.shift) {
            opWidth = width;
        } else if (info.logical) {
            opWidth = 1;
        }
        SExpr r = genBinary(info.prim, a, b, opWidth, outWidth);
        r.isSigned = bp->isSigned();
        return r;
    }

    //==================================================================
    // 3. Memory primitives (sv_tran_struct gen_memory_primitive)

    // Read a $readmemh image (words as hex, optional @addr markers, // comments)
    static bool readHexWords(const std::string& path, std::vector<uint64_t>& words) {
        std::vector<std::string> cands = {path};
        if (const char* d = getenv("MEM_INIT_DIR")) cands.push_back(std::string(d) + "/" + path);
        std::ifstream in;
        for (const std::string& c : cands) {
            in.open(c);
            if (in) break;
            in.clear();
        }
        if (!in) return false;
        std::string tok;
        size_t addr = 0;
        std::string line;
        while (std::getline(in, line)) {
            const size_t cpos = line.find("//");
            if (cpos != std::string::npos) line = line.substr(0, cpos);
            std::istringstream ls{line};
            while (ls >> tok) {
                if (tok[0] == '@') {
                    addr = std::stoul(tok.substr(1), nullptr, 16);
                    continue;
                }
                uint64_t v = 0;
                for (const char c : tok) {
                    if (c == '_') continue;
                    const int d = std::isdigit(static_cast<unsigned char>(c)) ? c - '0'
                                  : (std::tolower(c) >= 'a' && std::tolower(c) <= 'f') ? std::tolower(c) - 'a' + 10 : 0;
                    v = (v << 4) | static_cast<uint64_t>(d);
                }
                if (words.size() <= addr) words.resize(addr + 1, 0);
                words[addr++] = v;
            }
        }
        return true;
    }

    // Asynchronous ROM: a balanced mux2 tree over the address bits with the
    // image words as leaves (what a synthesiser's LUT-ROM is)
    // Two expressions denote the same signal: same text, or wires assigned
    // the same text (`mem_b_addr[9:0]` materialised twice)
    std::string defText(const SExpr& e) {
        if (!e.isIdent) return e.text;
        for (const SItem& it : m_items) {
            if (it.kind == SItem::ASSIGN && it.lhs == e.text) return it.rhs;
        }
        return e.text;
    }
    bool sameSignal(const SExpr& a, const SExpr& b) {
        if (a.text == b.text) return true;
        return defText(a) == defText(b);
    }

    SExpr romTree(const SMem& m, const std::vector<uint64_t>& words, const SExpr& addr) {
        if (addr.hasVal) {  // constant index (a generate loop reading a table)
            const uint64_t k = addr.val;
            return constExpr(k < words.size() ? words[k] : 0, m.dataWidth);
        }
        const SExpr a = materialize(resize(addr, m.addrWidth, false));
        std::vector<SExpr> level;
        const size_t n = size_t{1} << m.addrWidth;
        for (size_t i = 0; i < n; ++i) {
            const size_t k = i + static_cast<size_t>(m.lo < 0 ? 0 : 0);
            level.push_back(constExpr(k < words.size() ? words[k] : 0, m.dataWidth));
        }
        for (int bit = 0; bit < m.addrWidth; ++bit) {
            SExpr sel;
            sel.text = a.text + "[" + std::to_string(bit) + "]";
            sel.width = 1;
            sel.refs = a.refs;
            const SExpr selw = materialize(sel);
            std::vector<SExpr> next;
            for (size_t i = 0; i + 1 < level.size(); i += 2) {
                next.push_back(genMux(selw, level[i], level[i + 1], m.dataWidth));
            }
            level.swap(next);
        }
        return level.empty() ? constExpr(0, m.dataWidth) : level[0];
    }

    void emitMemories() {
        // Deterministic order: by name
        std::vector<SMem*> mems;
        for (auto& kv : m_mems) {
            if (!kv.second.asRegs) mems.push_back(&kv.second);
        }
        std::sort(mems.begin(), mems.end(), [](const SMem* a, const SMem* b) { return a->name < b->name; });
        // Which read-port idents are consumed by ordinary logic (not just by
        // the absorbed register)?
        std::unordered_map<std::string, int> rdUses;
        {
            // Only logic that is still live counts (the enable mux a register
            // was folded out of is dead but still sits in m_items)
            std::unordered_set<std::string> roots;
            for (SMem* const mp : mems) {
                for (const SMem::Write& w : mp->writes) {
                    roots.insert(w.idx.refs.begin(), w.idx.refs.end());
                    roots.insert(w.data.refs.begin(), w.data.refs.end());
                    roots.insert(w.en.refs.begin(), w.en.refs.end());
                }
                for (const SExpr& r : mp->readIdx) roots.insert(r.refs.begin(), r.refs.end());
                for (const SMem::SyncRead& sr : mp->sync) {
                    if (sr.used) roots.insert(sr.en.refs.begin(), sr.en.refs.end());
                }
                if (!mp->clk.text.empty()) roots.insert(mp->clk.refs.begin(), mp->clk.refs.end());
            }
            for (const SDeferredDff& dd : m_deferred) roots.insert(dd.en.refs.begin(), dd.en.refs.end());
            const std::vector<bool> alive = markLive(roots);
            for (size_t i = 0; i < m_items.size(); ++i) {
                if (!alive[i]) continue;
                for (const std::string& r : m_items[i].reads) {
                    if (m_readPorts.count(r)) ++rdUses[r];
                }
            }
        }
        for (SMem* const mp : mems) {
            SMem& m = *mp;
            const size_t nr = m.readIdx.size();
            const size_t nw = m.writes.size();
            if (nr == 0 && nw == 0) {
                warn("memory " + m.name + " is never accessed; dropped");
                continue;
            }
            if (nw > 2) warn("memory " + m.name + ": " + std::to_string(nw) + " write ports, only 2 supported");
            auto rdName = [&](size_t i) { return m.name + "_rdata" + std::to_string(i + 1); };
            auto declRd = [&](size_t i) {
                SDecl d;
                d.name = rdName(i);
                d.width = m.dataWidth;
                d.dir = VDirection::NONE;
                m_wires.push_back(d);
                m_widths[d.name] = m.dataWidth;
            };
            const SExpr clk = m.clk.text.empty() ? memClock() : m.clk;
            const SExpr zeroA = constExpr(0, m.addrWidth);
            const SExpr zeroD = constExpr(0, m.dataWidth);
            auto addr = [&](const SExpr& e) { return resize(e, m.addrWidth, false); };
            std::vector<std::pair<std::string, std::string>> params
                = {{"ADDR_WIDTH", std::to_string(m.addrWidth)}, {"DATA_WIDTH", std::to_string(m.dataWidth)}};
            if (!m.initFile.empty()) {
                params.emplace_back("INIT_FILE", "\"" + m.initFile + "\"");
            } else if (m.hasInitWords) {
                // an image computed from an initial block: written out as a
                // $readmemh file in the build directory, so the primitive (and
                // the mapper's INIT strings) see the same contents
                std::string dir = v3Global.opt.makeDir();
                V3Os::createDir(dir);
                if (!dir.empty() && dir[0] != '/') {
                    char cwd[4096];
                    if (::getcwd(cwd, sizeof cwd)) dir = std::string(cwd) + "/" + dir;
                }
                const std::string f = dir + "/" + sanitizeName(m_modp->prettyName()) + "__" + m.name + ".hex";
                std::ofstream hf{f};
                for (const uint64_t w : m.initWords) hf << std::hex << w << "\n";
                params.emplace_back("INIT_FILE", "\"" + f + "\"");
            }
            // True dual port: two clocked blocks (possibly on different clocks),
            // each writing and synchronously reading one address
            // (`if (en) if (we) mem[a] <= d; else q <= mem[a];`) -> memory_tdp_sync
            if (nw == 2 && nr == 2 && m.sync.size() >= 2 && m.sync[0].used && m.sync[1].used
                && rdUses[rdName(0)] == 0 && rdUses[rdName(1)] == 0) {
                int pair[2] = {-1, -1};
                bool taken[2] = {false, false};
                for (int k = 0; k < 2; ++k) {
                    for (int j = 0; j < 2; ++j) {
                        if (taken[j]) continue;
                        if (sameSignal(m.writes[k].idx, m.readIdx[j])
                            && m.writes[k].clk.text == m.sync[j].clk.text) {
                            pair[k] = j;
                            taken[j] = true;
                            break;
                        }
                    }
                }
                if (pair[0] >= 0 && pair[1] >= 0) {
                    SItem& it = addCell("memory_tdp_sync", m.name + "_inst");
                    it.keep = true;
                    it.params = params;
                    for (int k = 0; k < 2; ++k) {
                        const std::string sfx = std::to_string(k + 1);
                        const SMem::SyncRead& sr = m.sync[pair[k]];
                        pinIn(it, "clk" + sfx, m.writes[k].clk.text.empty() ? clk : m.writes[k].clk);
                        pinIn(it, "en" + sfx, materialize(orBits(m.writes[k].en, sr.en)));
                        pinIn(it, "we" + sfx, m.writes[k].en);
                        pinIn(it, "addr" + sfx, addr(m.writes[k].idx));
                        pinIn(it, "wdata" + sfx, m.writes[k].data);
                        pinOut(it, "rdata" + sfx, sr.q, sr.qRefs);
                        m_regsInBlock.emplace_back(sr.q, m.dataWidth);
                    }
                    continue;
                }
            }
            if (nw == 2 && m.writes[0].clk.text != m.writes[1].clk.text) {
                warn("memory " + m.name + ": written from two clock domains ("
                     + m.writes[0].clk.text + ", " + m.writes[1].clk.text
                     + ") but not as a true dual port; the primitive gets one clock");
            }
            // Every read port absorbed into a register and consumed nowhere else?
            bool allSync = nr > 0 && nw <= 1;
            for (size_t i = 0; i < nr && allSync; ++i) {
                allSync = i < m.sync.size() && m.sync[i].used && rdUses[rdName(i)] == 0;
            }
            if (!allSync) {
                // Re-emit the registers that were held back for absorption
                for (size_t i = 0; i < nr && i < m.sync.size(); ++i) {
                    if (!m.sync[i].used) continue;
                    for (const SDeferredDff& dd : m_deferred) {
                        if (dd.q != m.sync[i].q) continue;
                        SItem& it = addCell(dd.negedge ? "dffn_en" : "dff_en", newName("dff"));
                        it.params = {{"WIDTH", std::to_string(dd.width)}, {"RESET_VAL", "0"}, {"IS_ASYNC", "0"}};
                        pinIn(it, "clk", dd.clk);
                        it.pins.push_back({"rst", "1'b0"});
                        pinIn(it, "en", dd.en);
                        pinIn(it, "d", dd.d);
                        pinOut(it, "q", dd.q, dd.qRefs);
                    }
                }
            }
            if (nw == 0 && !allSync) {
                // Asynchronous ROM: lower the image to logic
                std::vector<uint64_t> words;
                bool have = false;
                if (m.hasInitWords) {
                    words = m.initWords;
                    have = true;
                } else if (!m.initFile.empty()) {
                    have = readHexWords(m.initFile, words);
                }
                if (!have || m.dataWidth > 64 || m.addrWidth > 16) {
                    warn("memory " + m.name + ": asynchronous read-only array without a loadable "
                         "$readmemh image (" + m.initFile + "); reads are 0");
                    for (size_t i = 0; i < nr; ++i) {
                        declRd(i);
                        addAssign(rdName(i), zeroD);
                    }
                    continue;
                }
                warn("memory " + m.name + ": " + std::to_string(words.size()) + "-word ROM "
                     + (m.hasInitWords ? std::string("(initial block image)") : m.initFile)
                     + " lowered to a mux tree (asynchronous read)");
                for (size_t i = 0; i < nr; ++i) {
                    declRd(i);
                    addAssign(rdName(i), romTree(m, words, m.readIdx[i]));
                }
                continue;
            }
            // One write port and one synchronous read port on different clocks (an
            // asynchronous FIFO or packet buffer: eth_pkt_buf256 writes on clk and
            // reads on rd_clk): the single-clock primitives would move one side into
            // the other's domain, so it becomes a true dual port, port 1 writing on
            // the write clock, port 2 reading on the read clock
            if (allSync && nw == 1 && nr == 1 && !m.writes[0].clk.text.empty() && !m.sync[0].clk.text.empty()
                && m.writes[0].clk.text != m.sync[0].clk.text) {
                SItem& it = addCell("memory_tdp_sync", m.name + "_inst");
                it.keep = true;
                it.params = params;
                const SMem::SyncRead& sr = m.sync[0];
                pinIn(it, "clk1", m.writes[0].clk);
                pinIn(it, "en1", m.writes[0].en);
                pinIn(it, "we1", m.writes[0].en);
                pinIn(it, "addr1", addr(m.writes[0].idx));
                pinIn(it, "wdata1", m.writes[0].data);
                it.pins.push_back({"rdata1", ""});
                pinIn(it, "clk2", sr.clk);
                pinIn(it, "en2", sr.en);
                pinIn(it, "we2", constExpr(0, 1));
                pinIn(it, "addr2", addr(m.readIdx[0]));
                pinIn(it, "wdata2", zeroD);
                pinOut(it, "rdata2", sr.q, sr.qRefs);
                m_regsInBlock.emplace_back(sr.q, m.dataWidth);
                continue;
            }
            if (allSync && nw >= 1) {
                for (size_t i = 0; i < nr && i < m.sync.size(); ++i) {
                    if (!m.sync[i].clk.text.empty() && !m.writes[0].clk.text.empty()
                        && m.sync[i].clk.text != m.writes[0].clk.text)
                        warn("memory " + m.name + ": read port " + std::to_string(i + 1) + " clocked by "
                             + m.sync[i].clk.text + ", writes by " + m.writes[0].clk.text
                             + "; the primitive has one clock");
                }
            }
            if (allSync) {
                // Synchronous-read primitives, up to two read ports per bank
                for (size_t bank = 0; bank * 2 < nr; ++bank) {
                    const size_t r0 = bank * 2;
                    const bool two = r0 + 1 < nr;
                    SItem& it = addCell(two ? "memory_1w2r_sync" : "memory_1w1r_sync",
                                        m.name + "_inst" + (bank ? "_" + std::to_string(bank + 1) : ""));
                    it.keep = true;
                    it.params = params;
                    pinIn(it, "clk", clk);
                    pinIn(it, "we", nw ? m.writes[0].en : constExpr(0, 1));
                    pinIn(it, "waddr", nw ? addr(m.writes[0].idx) : zeroA);
                    pinIn(it, "wdata", nw ? m.writes[0].data : zeroD);
                    const char* reN[2] = {"re1", "re2"};
                    const char* raN[2] = {"raddr1", "raddr2"};
                    const char* rdN[2] = {"rdata1", "rdata2"};
                    for (size_t k = 0; k < (two ? 2u : 1u); ++k) {
                        const SMem::SyncRead& sr = m.sync[r0 + k];
                        pinIn(it, two ? reN[k] : "re", sr.en);
                        pinIn(it, two ? raN[k] : "raddr", addr(m.readIdx[r0 + k]));
                        pinOut(it, two ? rdN[k] : "rdata", sr.q, sr.qRefs);
                        m_regsInBlock.emplace_back(sr.q, m.dataWidth);
                    }
                }
                if (nr > 2) warn("memory " + m.name + ": " + std::to_string(nr) + " synchronous read ports; replicated into banks");
                continue;
            }
            if (nr > 2 && nw <= 1) {
                // More read ports than a primitive has: replicate the memory
                // (register-file banking), every copy sharing the write port
                warn("memory " + m.name + ": " + std::to_string(nr)
                     + " read ports; replicated into " + std::to_string((nr + 1) / 2) + " memory_1w2r banks");
                for (size_t bank = 0; bank * 2 < nr; ++bank) {
                    const size_t r0 = bank * 2;
                    const size_t r1 = std::min(r0 + 1, nr - 1);
                    SItem& it = addCell("memory_1w2r", m.name + "_inst" + (bank ? "_" + std::to_string(bank + 1) : ""));
                    it.keep = true;
                    it.params = params;
                    pinIn(it, "clk", clk);
                    pinIn(it, "we", nw ? m.writes[0].en : constExpr(0, 1));
                    pinIn(it, "waddr", nw ? addr(m.writes[0].idx) : zeroA);
                    pinIn(it, "wdata", nw ? m.writes[0].data : zeroD);
                    pinIn(it, "raddr1", addr(m.readIdx[r0]));
                    pinIn(it, "raddr2", addr(m.readIdx[r1]));
                    for (size_t r = r0; r <= r1; ++r) declRd(r);
                    pinOut(it, "rdata1", rdName(r0));
                    if (r1 != r0) {
                        pinOut(it, "rdata2", rdName(r1));
                    } else {
                        it.pins.push_back({"rdata2", ""});
                    }
                }
                continue;
            }
            if (nr > 2) warn("memory " + m.name + ": " + std::to_string(nr) + " read ports, only 2 supported with 2 write ports");
            if (nw <= 1 && (nr == 0 || (nr == 1 && (nw == 0 || m.readIdx[0].text == m.writes[0].idx.text)))) {
                // Single-port: clk, we, addr, wdata, rdata
                SItem& it = addCell("memory_sp", m.name + "_inst");
                it.keep = true;
                it.params = params;
                pinIn(it, "clk", clk);
                pinIn(it, "we", nw ? m.writes[0].en : constExpr(0, 1));
                pinIn(it, "addr", nw ? addr(m.writes[0].idx) : (nr ? addr(m.readIdx[0]) : zeroA));
                pinIn(it, "wdata", nw ? m.writes[0].data : zeroD);
                if (nr) {
                    declRd(0);
                    pinOut(it, "rdata", rdName(0));
                } else {
                    it.pins.push_back({"rdata", ""});
                }
            } else if (nw <= 1) {
                // 1 write, up to 2 reads
                SItem& it = addCell("memory_1w2r", m.name + "_inst");
                it.keep = true;
                it.params = params;
                pinIn(it, "clk", clk);
                pinIn(it, "we", nw ? m.writes[0].en : constExpr(0, 1));
                pinIn(it, "waddr", nw ? addr(m.writes[0].idx) : zeroA);
                pinIn(it, "wdata", nw ? m.writes[0].data : zeroD);
                pinIn(it, "raddr1", addr(m.readIdx[0]));
                pinIn(it, "raddr2", addr(nr > 1 ? m.readIdx[1] : m.readIdx[0]));
                declRd(0);
                pinOut(it, "rdata1", rdName(0));
                if (nr > 1) {
                    declRd(1);
                    pinOut(it, "rdata2", rdName(1));
                } else {
                    it.pins.push_back({"rdata2", ""});
                }
            } else {
                // 2 writes, independent reads: register-file style
                SItem& it = addCell("memory_2w2r_rf", m.name + "_inst");
                it.keep = true;
                it.params = params;
                pinIn(it, "clk", clk);
                for (size_t p = 0; p < 2; ++p) {
                    const std::string sfx = std::to_string(p + 1);
                    pinIn(it, "we" + sfx, m.writes[p].en);
                    pinIn(it, "waddr" + sfx, addr(m.writes[p].idx));
                    pinIn(it, "wdata" + sfx, m.writes[p].data);
                }
                for (size_t p = 0; p < 2; ++p) {
                    const std::string sfx = std::to_string(p + 1);
                    if (p < nr) {
                        pinIn(it, "raddr" + sfx, addr(m.readIdx[p]));
                        declRd(p);
                        pinOut(it, "rdata" + sfx, rdName(p));
                    } else {
                        pinIn(it, "raddr" + sfx, zeroA);
                        it.pins.push_back({"rdata" + sfx, ""});
                    }
                }
            }
            if (nr == 1) m_renames[rdName(0)] = m.name + "_rdata";
        }
        applyRenames();
    }
    SExpr m_memClk;
    SExpr memClock() {
        if (!m_memClk.text.empty()) return m_memClk;
        // The clock of the (first) clocked block that wrote a memory, else any clock
        for (const SDecl& d : m_decls) {
            if (d.dir.isInput() && d.width == 1) {
                const std::string n = d.name;
                if (n == "clk" || n == "clock" || n == "clk_i" || n == "CLK") return identExpr(n, 1);
            }
        }
        for (const SDecl& d : m_decls) {
            if (d.dir.isInput() && d.width == 1) return identExpr(d.name, 1);
        }
        return identExpr("clk", 1);
    }
    std::unordered_map<std::string, std::string> m_renames;
    void applyRenames() {
        if (m_renames.empty()) return;
        auto ren = [&](std::string& s) {
            for (const auto& kv : m_renames) {
                size_t p = 0;
                while ((p = s.find(kv.first, p)) != std::string::npos) {
                    const bool before = p == 0 || !(std::isalnum(static_cast<unsigned char>(s[p - 1])) || s[p - 1] == '_');
                    const size_t e = p + kv.first.size();
                    const bool after = e >= s.size() || !(std::isalnum(static_cast<unsigned char>(s[e])) || s[e] == '_');
                    if (before && after) {
                        s.replace(p, kv.first.size(), kv.second);
                        p += kv.second.size();
                    } else {
                        p = e;
                    }
                }
            }
        };
        for (SItem& it : m_items) {
            for (SPin& p : it.pins) ren(p.expr);
            ren(it.lhs);
            ren(it.rhs);
            for (std::string& r : it.reads) ren(r);
            for (std::string& w : it.writes) ren(w);
        }
        for (SDecl& d : m_wires) {
            const std::string old = d.name;
            ren(d.name);
            if (old != d.name) m_widths[d.name] = m_widths[old];
        }
        m_renames.clear();
    }

    //==================================================================
    // 4. Dead-cell elimination (sv_tran_struct module_dce, extended to all primitives)

    // Which items are live given these extra root consumers (fixed point of
    // "an item is dead if nothing live reads what it drives")
    std::vector<bool> markLive(const std::unordered_set<std::string>& roots) const {
        std::vector<bool> alive(m_items.size(), true);
        bool changed = true;
        while (changed) {
            changed = false;
            std::unordered_set<std::string> consumed = roots;
            for (const SDecl& d : m_decls) {
                if (d.dir.isWritable()) consumed.insert(d.name);
            }
            for (size_t i = 0; i < m_items.size(); ++i) {
                if (!alive[i]) continue;
                for (const std::string& r : m_items[i].reads) consumed.insert(r);
            }
            for (size_t i = 0; i < m_items.size(); ++i) {
                if (!alive[i]) continue;
                const SItem& it = m_items[i];
                if (it.keep || it.kind == SItem::USERCELL || it.kind == SItem::COMMENT) continue;
                bool used = false;
                for (const std::string& w : it.writes) used |= consumed.count(w) > 0;
                if (!used) {
                    alive[i] = false;
                    changed = true;
                }
            }
        }
        return alive;
    }

    void dce() {
        const std::vector<bool> alive = markLive({});
        std::vector<SItem> kept;
        for (size_t i = 0; i < m_items.size(); ++i) {
            if (alive[i]) kept.push_back(m_items[i]);
        }
        m_items.swap(kept);
        // Orphaned declarations: neither read nor driven by anything left
        std::unordered_set<std::string> used;
        for (const SItem& it : m_items) {
            for (const std::string& r : it.reads) used.insert(r);
            for (const std::string& w : it.writes) used.insert(w);
        }
        auto prune = [&](std::vector<SDecl>& decls) {
            std::vector<SDecl> out;
            for (const SDecl& d : decls) {
                if (d.dir.isAny() || d.isParam || used.count(d.name)) out.push_back(d);
            }
            decls.swap(out);
        };
        prune(m_decls);
        prune(m_wires);
    }

    //==================================================================
    // 5. Vivado RTL_* relabeling (sv_gen_xilinx_rtl)

    void xilinxRelabel() {
        for (SItem& it : m_items) {
            if (it.kind != SItem::CELL) continue;
            std::vector<std::pair<std::string, std::string>> ren;
            std::string name;
            const std::string& p = it.prim;
            if (p == "bitwise_not") { name = "RTL_INV"; ren = {{"in", "I0"}, {"out", "O"}}; }
            else if (p == "bitwise_and") { name = "RTL_AND"; ren = {{"a", "I0"}, {"b", "I1"}, {"out", "O"}}; }
            else if (p == "bitwise_or") { name = "RTL_OR"; ren = {{"a", "I0"}, {"b", "I1"}, {"out", "O"}}; }
            else if (p == "bitwise_xor") { name = "RTL_XOR"; ren = {{"a", "I0"}, {"b", "I1"}, {"out", "O"}}; }
            else if (p == "mux2") { name = "RTL_MUX"; ren = {{"sel", "S"}, {"in0", "I0"}, {"in1", "I1"}, {"out", "O"}}; }
            else if (p == "adder") { name = "RTL_ADD"; ren = {{"a", "I0"}, {"b", "I1"}, {"out", "O"}}; }
            else if (p == "subtractor") { name = "RTL_SUB"; ren = {{"a", "I0"}, {"b", "I1"}, {"out", "O"}}; }
            else if (p == "multiplier" || p == "multiplier_signed") { name = "RTL_MUL"; ren = {{"a", "I0"}, {"b", "I1"}, {"out", "O"}}; }
            else if (p == "shifter_left") { name = "RTL_LSHIFT"; ren = {{"a", "I0"}, {"b", "I1"}, {"out", "O"}}; }
            else if (p == "shifter_right" || p == "shifter_right_arith") { name = "RTL_RSHIFT"; ren = {{"a", "I0"}, {"b", "I1"}, {"out", "O"}}; }
            else if (p == "comparator_eq") { name = "RTL_EQ"; ren = {{"a", "I0"}, {"b", "I1"}, {"out", "O"}}; }
            else if (p == "comparator_neq") { name = "RTL_NEQ"; ren = {{"a", "I0"}, {"b", "I1"}, {"out", "O"}}; }
            else if (p == "comparator_lt" || p == "comparator_lt_signed") { name = "RTL_LT"; ren = {{"a", "I0"}, {"b", "I1"}, {"out", "O"}}; }
            else if (p == "comparator_lte" || p == "comparator_lte_signed") { name = "RTL_LEQ"; ren = {{"a", "I0"}, {"b", "I1"}, {"out", "O"}}; }
            else if (p == "comparator_gt" || p == "comparator_gt_signed") { name = "RTL_GT"; ren = {{"a", "I0"}, {"b", "I1"}, {"out", "O"}}; }
            else if (p == "comparator_gte" || p == "comparator_gte_signed") { name = "RTL_GEQ"; ren = {{"a", "I0"}, {"b", "I1"}, {"out", "O"}}; }
            else if (p == "dff_en" || p == "dffn_en") {
                std::string width = "1";
                bool isAsync = false;
                for (const auto& kv : it.params) {
                    if (kv.first == "WIDTH") width = kv.second;
                    if (kv.first == "IS_ASYNC") isAsync = kv.second == "1";
                }
                bool hasRst = false;
                bool hasEn = false;
                for (const SPin& pin : it.pins) {
                    if (pin.name == "rst" && pin.expr != "1'b0") hasRst = true;
                    if (pin.name == "en" && pin.expr != "1'b1") hasEn = true;
                }
                name = !hasRst ? "RTL_REG" : isAsync ? "RTL_REG_ASYNC" : "RTL_REG_SYNC";
                if (hasEn) name += "_CE";
                if (p == "dffn_en") name += "_N";
                name += "__BREG_" + width;
                ren = {{"clk", "C"}, {"d", "D"}, {"q", "Q"}};
                if (hasRst) ren.emplace_back("rst", "RST");
                if (hasEn) ren.emplace_back("en", "CE");
            } else {
                continue;
            }
            std::vector<SPin> pins;
            for (const SPin& pin : it.pins) {
                for (const auto& r : ren) {
                    if (r.first == pin.name) pins.push_back({r.second, pin.expr});
                }
            }
            it.prim = name;
            it.pins = pins;
            it.params.clear();
        }
    }

    //==================================================================
    // 6. Text (sv_gen)

    static std::string rangeStr(const SDecl& d) {
        std::string s = "logic";
        if (d.isSigned) s += " signed";
        if (d.width > 1) s += " [" + std::to_string(d.width - 1) + ":0]";
        return s;
    }

    void print(std::ostream& os) {
        os << "module " << sanitizeName(m_modp->prettyName());
        std::vector<const SDecl*> ports;
        for (const SDecl& d : m_decls) {
            if (d.dir.isAny()) ports.push_back(&d);
        }
        if (ports.empty()) {
            os << ";\n";
        } else {
            os << " (\n";
            for (size_t i = 0; i < ports.size(); ++i) {
                const SDecl& d = *ports[i];
                os << "  " << d.dir.verilogKwd() << " " << rangeStr(d) << " " << d.name << d.unpacked
                   << (i + 1 < ports.size() ? ",\n" : "\n");
            }
            os << ");\n";
        }
        for (const std::string& w : m_warnings) os << "  // WARNING: " << w << "\n";
        for (const SDecl& d : m_decls) {
            if (d.isParam) os << "  localparam " << d.name << " = " << d.paramValue << ";\n";
        }
        for (const SDecl& d : m_decls) {
            if (!d.dir.isAny() && !d.isParam) os << "  " << rangeStr(d) << " " << d.name << d.unpacked << ";\n";
        }
        for (const SDecl& d : m_wires) os << "  " << rangeStr(d) << " " << d.name << ";\n";
        if (!m_items.empty()) os << "\n";
        for (const SItem& it : m_items) {
            switch (it.kind) {
            case SItem::COMMENT: os << "  " << it.text << "\n"; break;
            case SItem::ASSIGN: os << "  assign " << it.lhs << " = " << it.rhs << ";\n"; break;
            case SItem::CELL:
            case SItem::USERCELL: {
                os << "  " << it.prim;
                if (!it.params.empty()) {
                    os << " #(";
                    for (size_t i = 0; i < it.params.size(); ++i) {
                        os << (i ? ", " : "") << "." << it.params[i].first << "(" << it.params[i].second << ")";
                    }
                    os << ")";
                }
                os << " " << it.inst;
                if (it.pins.empty()) {
                    os << " ();\n";
                } else {
                    os << " (\n";
                    for (size_t i = 0; i < it.pins.size(); ++i) {
                        os << "    ." << it.pins[i].name << "(" << it.pins[i].expr << ")"
                           << (i + 1 < it.pins.size() ? ",\n" : "\n");
                    }
                    os << "  );\n";
                }
                break;
            }
            }
        }
        os << "endmodule\n";
    }
};

}  // namespace

//######################################################################
// V3EmitStruct class functions

static void emitStructTo(std::ostream& os);

bool V3EmitStruct::isBlackbox(const AstNodeModule* modp) {
    const auto& bb = v3Global.opt.structOnlyBlackbox();
    if (bb.empty()) return false;
    if (bb.count(modp->prettyName())) return true;
    return bb.count(AstNode::prettyName(modp->origName())) > 0;
}

std::string V3EmitStruct::cellTypeName(const AstNodeModule* modp) {
    if (isBlackbox(modp)) return sanitizeName(AstNode::prettyName(modp->origName()));
    return sanitizeName(modp->prettyName());
}

void V3EmitStruct::emit(const std::string& filename) {
    UINFO(2, __FUNCTION__ << ":");
    std::ofstream os{filename};
    if (!os) {
        v3fatal("Cannot write structural Verilog output: " << filename);
        return;
    }
    emitStructTo(os);
}

std::string V3EmitStruct::emitString() {
    std::ostringstream os;
    emitStructTo(os);
    return os.str();
}

static void emitStructTo(std::ostream& os) {
    const bool xilinx = v3Global.opt.structOnlyXilinxRtl();
    if (xilinx) {
        os << "// Generated by xilinx_rtl backend\n"
              "// Cells use Vivado RTL elaboration vocabulary (RTL_INV, RTL_AND, RTL_REG_SYNC, ...)\n\n";
    } else {
        os << "// Generated by structural converter\n"
              "// Primitives defined in: structural_primitives.sv\n\n";
    }
    bool first = true;
    std::set<std::string> bbDeclared;
    for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp;
         modp = VN_AS(modp->nextp(), NodeModule)) {
        if (!VN_IS(modp, Module)) continue;  // packages, interfaces, classes, $unit
        if (modp->dead()) continue;
        if (V3EmitStruct::isBlackbox(modp)) {
            // kept as instances only, but declared (ports and directions) so
            // the netlist tools know which pins are outputs
            const std::string name = V3EmitStruct::cellTypeName(modp);
            if (bbDeclared.count(name)) continue;
            bbDeclared.insert(name);
            os << "\n(* blackbox *)\nmodule " << name << " (";
            bool firstPort = true;
            for (AstNode* sp = modp->stmtsp(); sp; sp = sp->nextp()) {
                const AstVar* const vp = VN_CAST(sp, Var);
                if (!vp || !vp->isIO()) continue;
                os << (firstPort ? "\n" : ",\n") << "  " << vp->direction().verilogKwd();
                if (vp->width() > 1) os << " [" << (vp->width() - 1) << ":0]";
                os << " " << vp->prettyName();
                firstPort = false;
            }
            os << "\n);\nendmodule\n";
            continue;
        }
        if (!first) os << "\n";
        first = false;
        StructModule sm{modp, xilinx, v3Global.opt.structOnlyWidePackedMem(),
                        v3Global.opt.structOnlyReport()};
        sm.run(os);
        os.flush();
    }
}
