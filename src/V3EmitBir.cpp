// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit the System-Verilog-suite Behavioral IR
//
// Port of System-Verilog-suite/verilator_to_behavioral.ml (which reads the
// --json-only tree through sv_parse.ml) onto Verilator's in-memory AST.
// Same decisions, same intrinsics (@mem_write, @slice_write,
// @part_sel_write_up), same process shapes; streamed as the JSON schema
// documented in the suite's bir_json_load.ml.
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

#include "V3EmitBir.h"

#include "V3Global.h"
#include "V3EmitStruct.h"

#include <cstdlib>
#include <fstream>
#include <map>
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

std::string jstr(const std::string& s) {
    std::string o = "\"";
    for (const char c : s) {
        switch (c) {
        case '"': o += "\\\""; break;
        case '\\': o += "\\\\"; break;
        case '\n': o += "\\n"; break;
        case '\t': o += "\\t"; break;
        default:
            if (static_cast<unsigned char>(c) < 0x20) {
                char buf[8];
                snprintf(buf, sizeof buf, "\\u%04x", c);
                o += buf;
            } else {
                o += c;
            }
        }
    }
    return o + "\"";
}

std::string sanitizeName(const std::string& s) {
    std::string out;
    out.reserve(s.size());
    for (const char c : s) {
        if (std::isalnum(static_cast<unsigned char>(c)) || c == '_' || c == '$') out += c;
        else out += '_';
    }
    if (out.empty()) out = "_";
    return out;
}

std::string joinList(const std::vector<std::string>& xs) {
    std::string o = "[";
    for (size_t i = 0; i < xs.size(); ++i) {
        if (i) o += ",";
        o += xs[i];
    }
    return o + "]";
}

std::string jconst(const std::string& v, int w) {
    return "{\"e\":\"const\",\"v\":\"" + v + "\",\"w\":" + std::to_string(w) + "}";
}
std::string jconstU(uint64_t v, int w) { return jconst(std::to_string(v), w); }
std::string jvar(const std::string& n) { return "{\"e\":\"var\",\"n\":" + jstr(n) + "}"; }
std::string jbin(const char* op, const std::string& l, const std::string& r, int w, bool sg) {
    return std::string("{\"e\":\"bin\",\"op\":\"") + op + "\",\"l\":" + l + ",\"r\":" + r
           + ",\"w\":" + std::to_string(w) + ",\"signed\":" + (sg ? "true" : "false") + "}";
}
std::string jun(const char* op, const std::string& x, int w, bool sg) {
    return std::string("{\"e\":\"un\",\"op\":\"") + op + "\",\"x\":" + x + ",\"w\":"
           + std::to_string(w) + ",\"signed\":" + (sg ? "true" : "false") + "}";
}
std::string jslice(const std::string& x, int msb, int lsb) {
    return "{\"e\":\"slice\",\"x\":" + x + ",\"msb\":" + std::to_string(msb) + ",\"lsb\":" + std::to_string(lsb) + "}";
}
std::string jcat(const std::vector<std::string>& xs) { return "{\"e\":\"cat\",\"xs\":" + joinList(xs) + "}"; }
std::string jrep(int n, const std::string& x) {
    return "{\"e\":\"rep\",\"n\":" + std::to_string(n) + ",\"x\":" + x + "}";
}
std::string jassign(const std::string& lhs, const std::string& rhs) {
    return "{\"s\":\"assign\",\"lhs\":" + jstr(lhs) + ",\"rhs\":" + rhs + "}";
}
std::string jcallStmt(const std::string& f, const std::vector<std::string>& args) {
    return "{\"s\":\"call\",\"f\":" + jstr(f) + ",\"args\":" + joinList(args) + "}";
}
std::string jblock(const std::vector<std::string>& body) { return "{\"s\":\"block\",\"body\":" + joinList(body) + "}"; }
std::string jcomb(const std::string& name, const std::vector<std::string>& body) {
    return "{\"kind\":\"comb\",\"name\":" + jstr(name) + ",\"body\":" + joinList(body) + "}";
}

//######################################################################

class BirModule final {
    AstNodeModule* const m_modp;
    const std::vector<std::string>& m_pkgFuncs;
    std::unordered_map<const AstVar*, std::string> m_varName;
    std::unordered_map<const AstCell*, std::string> m_cellName;
    std::unordered_set<std::string> m_sigNames;
    std::vector<std::string> m_signals;
    std::vector<std::string> m_processes;
    std::vector<std::string> m_instances;
    std::vector<std::string> m_funcs;
    std::string m_genPrefix;
    int m_initialSeq = 0;
    struct Item final {
        AstNode* nodep;
        std::string prefix;
    };
    std::vector<Item> m_items;

public:
    BirModule(AstNodeModule* modp, const std::vector<std::string>& pkgFuncs)
        : m_modp{modp}
        , m_pkgFuncs{pkgFuncs} {}

    std::string run() {
        collectItems(m_modp->stmtsp());
        // Pass 1: names for every declared var / cell (generate-scope prefixed)
        for (const Item& it : m_items) {
            if (AstVar* const vp = VN_CAST(it.nodep, Var)) nameVar(vp, it.prefix);
            if (AstCell* const cp = VN_CAST(it.nodep, Cell)) m_cellName[cp] = sanitizeName(it.prefix + cp->prettyName());
        }
        // Signals: module-level vars, then procedural-scope locals (Internal)
        for (const Item& it : m_items) {
            if (AstVar* const vp = VN_CAST(it.nodep, Var)) declSignal(vp, false);
        }
        for (const Item& it : m_items) {
            if (AstNodeProcedure* const pp = VN_CAST(it.nodep, NodeProcedure)) {
                VL_RESTORER_COPY(m_genPrefix);
                m_genPrefix = it.prefix;
                declNested(pp->stmtsp());
            }
        }
        // Processes / instances / functions
        for (const Item& it : m_items) {
            VL_RESTORER_COPY(m_genPrefix);
            m_genPrefix = it.prefix;
            AstNode* const nodep = it.nodep;
            if (AstAlways* const ap = VN_CAST(nodep, Always)) {
                lowerAlways(ap);
            } else if (AstAssignW* const wp = VN_CAST(nodep, AssignW)) {
                lowerAssignW(wp);
            } else if (AstCell* const cp = VN_CAST(nodep, Cell)) {
                lowerCell(cp);
            } else if (VN_IS(nodep, Initial) || VN_IS(nodep, InitialStatic)) {
                lowerInitial(VN_AS(nodep, NodeProcedure));
            } else if (AstNodeFTask* const fp = VN_CAST(nodep, NodeFTask)) {
                m_funcs.push_back(lowerFunc(fp));
            }
        }
        for (const std::string& f : m_pkgFuncs) m_funcs.push_back(f);
        return "{\"name\":" + jstr(sanitizeName(m_modp->prettyName())) + ",\"signals\":" + joinList(m_signals)
               + ",\"processes\":" + joinList(m_processes) + ",\"instances\":" + joinList(m_instances)
               + ",\"funcs\":" + joinList(m_funcs) + "}";
    }

    // Functions defined in a package (visible to every module via import)
    static std::vector<std::string> packageFuncs(AstNodeModule* pkgp) {
        BirModule bm{pkgp, {}};
        std::vector<std::string> out;
        for (AstNode* sp = pkgp->stmtsp(); sp; sp = sp->nextp()) {
            if (AstNodeFTask* const fp = VN_CAST(sp, NodeFTask)) out.push_back(bm.lowerFunc(fp));
        }
        return out;
    }

private:
    void warn(const AstNode* nodep, const std::string& msg) {
        UINFO(3, "bir: " << msg << " (" << nodep->prettyTypeName() << " at " << nodep->fileline()->ascii() << ")");
        if (v3Global.opt.structOnlyReport()) {
            std::cerr << "%Warning-BIR: " << nodep->fileline()->ascii() << ": " << msg << " ("
                      << nodep->prettyTypeName() << ")\n";
        }
    }

    // ---- item collection (sv_parse flattening of generate scopes) ----
    void collectItems(AstNode* nodep) {
        for (; nodep; nodep = nodep->nextp()) {
            if (AstGenBlock* const gp = VN_CAST(nodep, GenBlock)) {
                VL_RESTORER_COPY(m_genPrefix);
                if (gp->prettyName().find('[') != std::string::npos) {
                    m_genPrefix += sanitizeName(gp->prettyName()) + "_";
                }
                collectItems(gp->genforp());
                collectItems(gp->itemsp());
            } else if (AstBegin* const bp = VN_CAST(nodep, Begin)) {
                collectItems(bp->declsp());
                collectItems(bp->stmtsp());
            } else {
                m_items.push_back({nodep, m_genPrefix});
            }
        }
    }
    void nameVar(AstVar* vp, const std::string& prefix) {
        if (m_varName.count(vp)) return;
        m_varName[vp] = sanitizeName(prefix + vp->prettyName());
    }
    std::string varName(const AstVar* vp) {
        const auto it = m_varName.find(vp);
        if (it != m_varName.end()) return it->second;
        return sanitizeName(vp->prettyName());
    }

    static const AstNodeDType* unpackedOf(const AstNodeDType* dtp, int& depth) {
        depth = 1;
        const AstNodeDType* d = dtp->skipRefp();
        while (const AstUnpackArrayDType* const ap = VN_CAST(d, UnpackArrayDType)) {
            depth *= ap->elementsConst();
            d = ap->subDTypep()->skipRefp();
        }
        return d;
    }
    void declSignal(AstVar* vp, bool procedural) {
        if (vp->isParam() || vp->isGenVar() || vp->isIfaceRef()) return;
        if (vp->varType() == VVarType::GENVAR) return;
        nameVar(vp, m_genPrefix);
        const std::string name = varName(vp);
        if (m_sigNames.count(name)) return;  // top-level definition wins over a procedural shadow
        m_sigNames.insert(name);
        int depth = 1;
        const AstNodeDType* const ep = unpackedOf(vp->dtypep(), depth);
        const char* dir = "internal";
        if (!procedural) {
            if (vp->direction() == VDirection::INPUT) dir = "input";
            else if (vp->direction() == VDirection::OUTPUT) dir = "output";
            else if (vp->direction() == VDirection::INOUT) dir = "inout";
        }
        m_signals.push_back("{\"name\":" + jstr(name) + ",\"width\":" + std::to_string(ep->width() > 0 ? ep->width() : 1)
                            + ",\"signed\":" + (ep->isSigned() ? "true" : "false") + ",\"dir\":\"" + dir
                            + "\",\"depth\":" + std::to_string(depth) + "}");
    }
    void declNested(AstNode* nodep) {
        for (; nodep; nodep = nodep->nextp()) {
            if (AstVar* const vp = VN_CAST(nodep, Var)) {
                declSignal(vp, true);
            } else if (AstBegin* const bp = VN_CAST(nodep, Begin)) {
                declNested(bp->declsp());
                declNested(bp->stmtsp());
            } else if (AstNodeIf* const ip = VN_CAST(nodep, NodeIf)) {
                declNested(ip->thensp());
                declNested(ip->elsesp());
            } else if (AstCase* const cp = VN_CAST(nodep, Case)) {
                for (AstCaseItem* ip = cp->itemsp(); ip; ip = VN_AS(ip->nextp(), CaseItem)) declNested(ip->stmtsp());
            } else if (AstLoop* const lp = VN_CAST(nodep, Loop)) {
                declNested(lp->stmtsp());
                declNested(lp->contsp());
            } else if (AstJumpBlock* const jp = VN_CAST(nodep, JumpBlock)) {
                declNested(jp->stmtsp());
            }
        }
    }

    // ---- constants ----
    static std::string constValue(const V3Number& num) {
        if (num.isString() || num.isDouble()) return "0";
        if (num.width() <= 64 && !num.isFourState()) return std::to_string(num.toUQuad());
        std::string hex;
        for (int b = ((num.width() + 3) / 4) * 4 - 4; b >= 0; b -= 4) {
            int v = 0;
            for (int k = 3; k >= 0; --k) {
                v <<= 1;
                if (b + k < num.width() && num.bitIs1(b + k)) v |= 1;
            }
            hex += "0123456789abcdef"[v];
        }
        return "0x" + (hex.empty() ? std::string("0") : hex);
    }
    static bool constInt(AstNodeExpr* ep, int64_t& out) {
        AstConst* const cp = VN_CAST(ep, Const);
        if (!cp || cp->num().isFourState() || cp->num().width() > 64) return false;
        out = static_cast<int64_t>(cp->num().toUQuad());
        if (cp->num().isSigned() && cp->num().width() < 64 && (out >> (cp->num().width() - 1)) & 1)
            out |= ~((int64_t{1} << cp->num().width()) - 1);
        return true;
    }

    // ---- expressions (expr_to_bexpr) ----
    std::string expr(AstNodeExpr* nodep) {
        if (!nodep) return jconstU(0, 1);
        const int w = nodep->width() > 0 ? nodep->width() : 1;
        const bool sg = nodep->isSigned();
        if (AstVarRef* const vp = VN_CAST(nodep, VarRef)) return jvar(varName(vp->varp()));
        if (AstConst* const cp = VN_CAST(nodep, Const)) return jconst(constValue(cp->num()), cp->num().width());
        if (AstEnumItemRef* const ep = VN_CAST(nodep, EnumItemRef)) {
            if (ep->itemp()) {
                if (AstConst* const cp = VN_CAST(ep->itemp()->valuep(), Const)) return jconst(constValue(cp->num()), w);
            }
            return jconstU(0, w);
        }
        if (AstCond* const cp = VN_CAST(nodep, Cond)) {
            return "{\"e\":\"cond\",\"c\":" + expr(cp->condp()) + ",\"t\":" + expr(cp->thenp()) + ",\"f\":" + expr(cp->elsep()) + "}";
        }
        if (AstSel* const sp = VN_CAST(nodep, Sel)) {
            const int ww = sp->widthConst();
            int64_t lsb;
            if (constInt(sp->lsbp(), lsb)) return jslice(expr(sp->fromp()), static_cast<int>(lsb) + ww - 1, static_cast<int>(lsb));
            // dynamic part-select: (vec >> lsb) & mask
            const std::string shifted = jbin(">>", expr(sp->fromp()), expr(sp->lsbp()), ww, false);
            const std::string mask = ww >= 64 ? jconst("0x" + std::string((ww + 3) / 4, 'f'), ww)
                                              : jconstU((uint64_t{1} << ww) - 1, ww);
            return jbin("&", shifted, mask, ww, false);
        }
        if (AstArraySel* const ap = VN_CAST(nodep, ArraySel)) {
            return "{\"e\":\"sel\",\"a\":" + expr(ap->fromp()) + ",\"i\":" + expr(ap->bitp()) + "}";
        }
        if (AstConcat* const cp = VN_CAST(nodep, Concat)) {
            std::vector<AstNodeExpr*> parts;
            flattenConcat(cp, parts);
            std::vector<std::string> xs;
            for (AstNodeExpr* p : parts) xs.push_back(expr(p));
            return jcat(xs);
        }
        if (AstReplicate* const rp = VN_CAST(nodep, Replicate)) {
            int64_t n = 1;
            if (!constInt(rp->countp(), n)) n = 1;
            return jrep(static_cast<int>(n), expr(rp->srcp()));
        }
        if (AstNodeFTaskRef* const fp = VN_CAST(nodep, NodeFTaskRef)) {
            std::vector<std::string> args;
            for (AstArg* ap = fp->argsp(); ap; ap = VN_AS(ap->nextp(), Arg)) args.push_back(expr(ap->exprp()));
            return "{\"e\":\"call\",\"f\":" + jstr(sanitizeName(fp->prettyName())) + ",\"args\":" + joinList(args) + "}";
        }
        if (AstNodeBiop* const bp = VN_CAST(nodep, NodeBiop)) return biop(bp, w, sg);
        if (AstNodeUniop* const up = VN_CAST(nodep, NodeUniop)) return uniop(up, w, sg);
        if (AstCastSize* const cp = VN_CAST(nodep, CastSize)) return resize(cp->lhsp(), w, cp->lhsp()->isSigned());
        if (VN_IS(nodep, CReset)) return jconstU(0, w);
        if (AstExprStmt* const ep = VN_CAST(nodep, ExprStmt)) return expr(ep->resultp());
        warn(nodep, "unsupported expression replaced by 0");
        return jconstU(0, w);
    }
    static void flattenConcat(AstNodeExpr* ep, std::vector<AstNodeExpr*>& out) {
        if (AstConcat* const cp = VN_CAST(ep, Concat)) {
            flattenConcat(cp->lhsp(), out);
            flattenConcat(cp->rhsp(), out);
        } else {
            out.push_back(ep);
        }
    }
    // EXTEND / EXTENDS / CastSize: pad with zeros or the MSB, or truncate
    std::string resize(AstNodeExpr* xp, int w, bool sext) {
        const int xw = xp->width() > 0 ? xp->width() : 1;
        const std::string x = expr(xp);
        if (xw == w) return x;
        if (w < xw) return jslice(x, w - 1, 0);
        const std::string pad = sext ? jslice(x, xw - 1, xw - 1) : jconstU(0, 1);
        return jcat({jrep(w - xw, pad), x});
    }
    std::string truth(AstNodeExpr* xp) {  // x != 0, 1 bit
        if (xp->width() <= 1) return expr(xp);
        return jbin("!=", expr(xp), jconstU(0, xp->width()), 1, false);
    }
    std::string biop(AstNodeBiop* bp, int w, bool sg) {
        const char* op = nullptr;
        if (VN_IS(bp, Add)) op = "+";
        else if (VN_IS(bp, Sub)) op = "-";
        else if (VN_IS(bp, Mul) || VN_IS(bp, MulS)) op = "*";
        else if (VN_IS(bp, Div) || VN_IS(bp, DivS)) op = "/";
        else if (VN_IS(bp, ModDiv) || VN_IS(bp, ModDivS)) op = "%";
        else if (VN_IS(bp, And)) op = "&";
        else if (VN_IS(bp, Or)) op = "|";
        else if (VN_IS(bp, Xor)) op = "^";
        else if (VN_IS(bp, ShiftL)) op = "<<";
        else if (VN_IS(bp, ShiftR)) op = ">>";
        else if (VN_IS(bp, ShiftRS)) op = ">>>";
        else if (VN_IS(bp, Eq) || VN_IS(bp, EqCase) || VN_IS(bp, EqWild)) op = "==";
        else if (VN_IS(bp, Neq) || VN_IS(bp, NeqCase) || VN_IS(bp, NeqWild)) op = "!=";
        else if (VN_IS(bp, Lt) || VN_IS(bp, LtS)) op = "<";
        else if (VN_IS(bp, Lte) || VN_IS(bp, LteS)) op = "<=";
        else if (VN_IS(bp, Gt) || VN_IS(bp, GtS)) op = ">";
        else if (VN_IS(bp, Gte) || VN_IS(bp, GteS)) op = ">=";
        else if (VN_IS(bp, LogAnd)) return jbin("&", truth(bp->lhsp()), truth(bp->rhsp()), 1, false);
        else if (VN_IS(bp, LogOr)) return jbin("|", truth(bp->lhsp()), truth(bp->rhsp()), 1, false);
        if (!op) {
            warn(bp, "unsupported binary operator replaced by 0");
            return jconstU(0, w);
        }
        const bool signedOp = VN_IS(bp, MulS) || VN_IS(bp, DivS) || VN_IS(bp, ModDivS) || VN_IS(bp, ShiftRS)
                              || VN_IS(bp, LtS) || VN_IS(bp, LteS) || VN_IS(bp, GtS) || VN_IS(bp, GteS);
        return jbin(op, expr(bp->lhsp()), expr(bp->rhsp()), w, sg || signedOp);
    }
    std::string uniop(AstNodeUniop* up, int w, bool sg) {
        if (VN_IS(up, Not)) return jun("~", expr(up->lhsp()), w, sg);
        if (VN_IS(up, Negate)) return jun("-", expr(up->lhsp()), w, sg);
        if (VN_IS(up, RedAnd)) return jun("&", expr(up->lhsp()), 1, false);
        if (VN_IS(up, RedOr)) return jun("|", expr(up->lhsp()), 1, false);
        if (VN_IS(up, RedXor)) return jun("^", expr(up->lhsp()), 1, false);
        if (VN_IS(up, LogNot)) return jbin("==", expr(up->lhsp()), jconstU(0, up->lhsp()->width() > 0 ? up->lhsp()->width() : 1), 1, false);
        if (VN_IS(up, Extend)) return resize(up->lhsp(), w, false);
        if (VN_IS(up, ExtendS)) return resize(up->lhsp(), w, true);
        if (VN_IS(up, Signed) || VN_IS(up, Unsigned) || VN_IS(up, CastWrap)) return expr(up->lhsp());
        warn(up, "unsupported unary operator replaced by its operand");
        return expr(up->lhsp());
    }

    // ---- statements (stmt_to_bstmt) ----
    static bool baseVar(AstNodeExpr* ep, const AstVar*& out) {
        if (AstVarRef* const vp = VN_CAST(ep, VarRef)) {
            out = vp->varp();
            return true;
        }
        if (AstSel* const sp = VN_CAST(ep, Sel)) return baseVar(sp->fromp(), out);
        if (AstArraySel* const ap = VN_CAST(ep, ArraySel)) return baseVar(ap->fromp(), out);
        return false;
    }
    std::string assign(AstNodeExpr* lhsp, AstNodeExpr* rhsp) {
        const AstVar* basep = nullptr;
        if (AstArraySel* const ap = VN_CAST(lhsp, ArraySel)) {
            if (baseVar(ap->fromp(), basep)) {
                return jcallStmt("@mem_write", {jvar(varName(basep)), expr(ap->bitp()), expr(rhsp)});
            }
            warn(lhsp, "array write with unsupported base dropped");
            return jblock({});
        }
        if (AstSel* const sp = VN_CAST(lhsp, Sel)) {
            const int w = sp->widthConst();
            if (AstArraySel* const ap = VN_CAST(sp->fromp(), ArraySel)) {
                // arr[i][lsb +: w] = rhs -> read-modify-write of element i
                if (!baseVar(ap->fromp(), basep)) {
                    warn(lhsp, "slice write into array element with unsupported base dropped");
                    return jblock({});
                }
                const std::string u32field = jconstU((w >= 64) ? ~0ULL : ((uint64_t{1} << w) - 1), 32);
                const std::string lsb = sp->lsbp() ? expr(sp->lsbp()) : jconstU(0, 32);
                const std::string idx = expr(ap->bitp());
                const std::string elem = "{\"e\":\"sel\",\"a\":" + jvar(varName(basep)) + ",\"i\":" + idx + "}";
                const std::string smask = jbin("<<", u32field, lsb, 32, false);
                const std::string cleared = jbin("-", elem, jbin("&", elem, smask, 32, false), 32, false);
                const std::string ins = jbin("<<", jbin("&", expr(rhsp), u32field, 32, false), lsb, 32, false);
                return jcallStmt("@mem_write", {jvar(varName(basep)), idx, jbin("|", cleared, ins, 32, false)});
            }
            if (!baseVar(sp->fromp(), basep)) {
                warn(lhsp, "part-select write with unsupported base dropped");
                return jblock({});
            }
            int64_t lsb;
            if (constInt(sp->lsbp(), lsb)) {
                return jcallStmt("@slice_write", {jvar(varName(basep)), jconstU(lsb + w - 1, 32), jconstU(lsb, 32), expr(rhsp)});
            }
            return jcallStmt("@part_sel_write_up", {jvar(varName(basep)), expr(sp->lsbp()), jconstU(w, 32), expr(rhsp)});
        }
        if (AstConcat* const cp = VN_CAST(lhsp, Concat)) {
            // {a, b} = rhs -> slices of rhs
            std::vector<AstNodeExpr*> parts;
            flattenConcat(cp, parts);
            std::vector<std::string> body;
            const std::string r = expr(rhsp);
            int lsb = 0;
            for (auto it = parts.rbegin(); it != parts.rend(); ++it) {
                const int pw = (*it)->width() > 0 ? (*it)->width() : 1;
                // the rhs slice is an expression; assign() needs a node, so build the slice textually
                const AstVar* pb = nullptr;
                if (VN_IS(*it, VarRef) && baseVar(*it, pb)) {
                    body.push_back(jassign(varName(pb), jslice(r, lsb + pw - 1, lsb)));
                } else if (baseVar(*it, pb)) {
                    AstSel* const psp = VN_CAST(*it, Sel);
                    int64_t plsb;
                    if (psp && constInt(psp->lsbp(), plsb)) {
                        body.push_back(jcallStmt("@slice_write", {jvar(varName(pb)), jconstU(plsb + psp->widthConst() - 1, 32), jconstU(plsb, 32), jslice(r, lsb + pw - 1, lsb)}));
                    } else {
                        warn(*it, "concat assignment part dropped");
                    }
                } else {
                    warn(*it, "concat assignment part dropped");
                }
                lsb += pw;
            }
            return jblock(body);
        }
        if (baseVar(lhsp, basep)) return jassign(varName(basep), expr(rhsp));
        warn(lhsp, "assignment target dropped");
        return jblock({});
    }

    std::vector<std::string> stmts(AstNode* nodep) {
        std::vector<std::string> out;
        for (; nodep; nodep = nodep->nextp()) {
            // `i = init; loop(test; body; i = i + k)`  ->  for (sv_parse's rwlst collapse)
            if (AstAssign* const ap = VN_CAST(nodep, Assign)) {
                AstLoop* const lp = VN_CAST(nodep->nextp(), Loop);
                const AstVar* iv = nullptr;
                if (lp && VN_IS(ap->lhsp(), VarRef) && baseVar(ap->lhsp(), iv) && VN_IS(lp->stmtsp(), LoopTest)) {
                    // the update is the last statement of the body (or contsp)
                    AstNode* lastp = lp->contsp();
                    if (!lastp) {
                        lastp = lp->stmtsp();
                        while (lastp->nextp()) lastp = lastp->nextp();
                    }
                    const AstVar* uv = nullptr;
                    AstAssign* const up = VN_CAST(lastp, Assign);
                    if (up && VN_IS(up->lhsp(), VarRef) && baseVar(up->lhsp(), uv) && uv == iv) {
                        std::vector<std::string> body;
                        for (AstNode* sp = lp->stmtsp(); sp; sp = sp->nextp()) {
                            if (sp == lastp || VN_IS(sp, LoopTest)) continue;
                            const std::string s = stmt(sp);
                            if (!s.empty()) body.push_back(s);
                        }
                        out.push_back("{\"s\":\"for\",\"init\":" + jassign(varName(iv), expr(ap->rhsp())) + ",\"c\":"
                                      + expr(VN_AS(lp->stmtsp(), LoopTest)->condp()) + ",\"upd\":"
                                      + jassign(varName(uv), expr(up->rhsp())) + ",\"body\":" + joinList(body) + "}");
                        nodep = nodep->nextp();
                        continue;
                    }
                }
            }
            const std::string s = stmt(nodep);
            if (!s.empty()) out.push_back(s);
        }
        return out;
    }

    std::string stmt(AstNode* nodep) {
        if (AstNodeAssign* const ap = VN_CAST(nodep, NodeAssign)) {
            if (VN_IS(ap, AssignForce)) return "";
            return assign(ap->lhsp(), ap->rhsp());
        }
        if (AstNodeIf* const ip = VN_CAST(nodep, NodeIf)) {
            return "{\"s\":\"if\",\"c\":" + expr(ip->condp()) + ",\"t\":" + joinList(stmts(ip->thensp())) + ",\"e\":" + joinList(stmts(ip->elsesp())) + "}";
        }
        if (AstCase* const cp = VN_CAST(nodep, Case)) {
            std::vector<std::string> cases;
            std::string dflt = "[]";
            for (AstCaseItem* ip = cp->itemsp(); ip; ip = VN_AS(ip->nextp(), CaseItem)) {
                const std::string body = joinList(stmts(ip->stmtsp()));
                if (ip->isDefault()) {
                    dflt = body;
                    continue;
                }
                // one arm per label (the OCaml side took the first label only)
                for (AstNodeExpr* condp = ip->condsp(); condp; condp = VN_AS(condp->nextp(), NodeExpr)) {
                    cases.push_back("[" + expr(condp) + "," + body + "]");
                }
            }
            return "{\"s\":\"case\",\"sel\":" + expr(cp->exprp()) + ",\"cases\":" + joinList(cases) + ",\"default\":" + dflt + "}";
        }
        if (AstBegin* const bp = VN_CAST(nodep, Begin)) return jblock(stmts(bp->stmtsp()));
        if (AstJumpBlock* const jp = VN_CAST(nodep, JumpBlock)) return jblock(stmts(jp->stmtsp()));
        if (AstLoop* const lp = VN_CAST(nodep, Loop)) {
            // while (test) { body; conts }   (For' in the OCaml reader: BWhile with the increments appended)
            AstLoopTest* const tp = VN_CAST(lp->stmtsp(), LoopTest);
            std::vector<std::string> body;
            for (AstNode* sp = lp->stmtsp(); sp; sp = sp->nextp()) {
                if (VN_IS(sp, LoopTest)) continue;
                const std::string s = stmt(sp);
                if (!s.empty()) body.push_back(s);
            }
            for (const std::string& s : stmts(lp->contsp())) body.push_back(s);
            return "{\"s\":\"while\",\"c\":" + (tp ? expr(tp->condp()) : jconstU(1, 1)) + ",\"body\":" + joinList(body) + "}";
        }
        if (AstStmtExpr* const sp = VN_CAST(nodep, StmtExpr)) {
            if (AstNodeFTaskRef* const fp = VN_CAST(sp->exprp(), NodeFTaskRef)) {
                std::vector<std::string> args;
                for (AstArg* ap = fp->argsp(); ap; ap = VN_AS(ap->nextp(), Arg)) args.push_back(expr(ap->exprp()));
                return jcallStmt(sanitizeName(fp->prettyName()), args);
            }
            return "";
        }
        if (AstInitialAutomaticStmt* const iap = VN_CAST(nodep, InitialAutomaticStmt)) return jblock(stmts(iap->stmtsp()));
        if (AstInitialStaticStmt* const isp = VN_CAST(nodep, InitialStaticStmt)) return jblock(stmts(isp->stmtsp()));
        if (VN_IS(nodep, Var) || VN_IS(nodep, Comment) || VN_IS(nodep, JumpGo) || VN_IS(nodep, CReset)
            || VN_IS(nodep, Display) || VN_IS(nodep, Stop) || VN_IS(nodep, Finish) || VN_IS(nodep, StmtPragma)
            || VN_IS(nodep, NodeCoverOrAssert) || VN_IS(nodep, Delay) || VN_IS(nodep, SFormat)
            || VN_IS(nodep, FClose) || VN_IS(nodep, FFlush) || VN_IS(nodep, TimeFormat) || VN_IS(nodep, PrintTimeScale)
            || VN_IS(nodep, NodeReadWriteMem))
            return "";
        warn(nodep, "unsupported statement dropped");
        return "";
    }

    // Is this statement pure elaboration-time computation? (is_elab_stmt)
    bool isElab(AstNode* nodep) {
        for (; nodep; nodep = nodep->nextp()) {
            if (VN_IS(nodep, Assign) || VN_IS(nodep, AssignDly) || VN_IS(nodep, AssignW) || VN_IS(nodep, Var)) continue;
            if (AstBegin* const bp = VN_CAST(nodep, Begin)) {
                if (!isElab(bp->stmtsp())) return false;
                continue;
            }
            if (AstNodeIf* const ip = VN_CAST(nodep, NodeIf)) {
                if (!isElab(ip->thensp()) || !isElab(ip->elsesp())) return false;
                continue;
            }
            if (AstLoop* const lp = VN_CAST(nodep, Loop)) {
                bool ok = true;
                for (AstNode* sp = lp->stmtsp(); sp && ok; sp = sp->nextp()) {
                    if (VN_IS(sp, LoopTest)) continue;
                    ok = isElab(sp) && !sp->nextp() ? true : isElabOne(sp);
                }
                if (!ok || !isElab(lp->contsp())) return false;
                continue;
            }
            if (AstCase* const cp = VN_CAST(nodep, Case)) {
                for (AstCaseItem* ip = cp->itemsp(); ip; ip = VN_AS(ip->nextp(), CaseItem)) {
                    if (!isElab(ip->stmtsp())) return false;
                }
                continue;
            }
            if (VN_IS(nodep, JumpBlock)) {
                if (!isElab(VN_AS(nodep, JumpBlock)->stmtsp())) return false;
                continue;
            }
            return false;
        }
        return true;
    }
    bool isElabOne(AstNode* nodep) {
        AstNode* const save = nodep->nextp();
        (void)save;
        // evaluate a single statement (ignore its siblings)
        if (VN_IS(nodep, Assign) || VN_IS(nodep, AssignDly) || VN_IS(nodep, Var)) return true;
        if (AstBegin* const bp = VN_CAST(nodep, Begin)) return isElab(bp->stmtsp());
        if (AstNodeIf* const ip = VN_CAST(nodep, NodeIf)) return isElab(ip->thensp()) && isElab(ip->elsesp());
        if (AstJumpBlock* const jp = VN_CAST(nodep, JumpBlock)) return isElab(jp->stmtsp());
        if (VN_IS(nodep, Loop)) {
            AstLoop* const lp = VN_AS(nodep, Loop);
            for (AstNode* sp = lp->stmtsp(); sp; sp = sp->nextp()) {
                if (VN_IS(sp, LoopTest)) continue;
                if (!isElabOne(sp)) return false;
            }
            return true;
        }
        return false;
    }

    // ---- always blocks (always_to_bprocess) ----
    void lowerAlways(AstAlways* ap) {
        if (ap->keyword() == VAlwaysKwd::CONT_ASSIGN) {
            for (AstNode* sp = ap->stmtsp(); sp; sp = sp->nextp()) {
                if (AstAssignW* const wp = VN_CAST(sp, AssignW)) lowerAssignW(wp);
            }
            return;
        }
        const AstVar* clockp = nullptr;
        bool pos = true;
        if (AstSenTree* const stp = ap->sentreep()) {
            for (AstSenItem* ip = stp->sensesp(); ip; ip = VN_AS(ip->nextp(), SenItem)) {
                if (ip->edgeType() == VEdgeType::ET_POSEDGE || ip->edgeType() == VEdgeType::ET_NEGEDGE) {
                    if (const AstVarRef* const vp = VN_CAST(ip->sensp(), VarRef)) {
                        if (!clockp) {
                            clockp = vp->varp();
                            pos = ip->edgeType() == VEdgeType::ET_POSEDGE;
                        }
                    }
                }
            }
        }
        const std::vector<std::string> body = stmts(ap->stmtsp());
        if (clockp) {
            m_processes.push_back("{\"kind\":\"seq\",\"name\":\"always_ff\",\"clock\":" + jstr(varName(clockp)) + ",\"edge\":\""
                                  + (pos ? "pos" : "neg") + "\",\"reset\":null,\"reset_async\":false,\"body\":" + joinList(body) + "}");
        } else {
            m_processes.push_back(jcomb("always_comb", body));
        }
    }
    void lowerAssignW(AstAssignW* wp) {
        const AstVar* basep = nullptr;
        if (!baseVar(wp->lhsp(), basep) && !VN_IS(wp->lhsp(), Concat)) {
            warn(wp, "continuous assign target dropped");
            return;
        }
        const std::string name = basep ? varName(basep) : "concat";
        m_processes.push_back(jcomb("assign_" + name, {assign(wp->lhsp(), wp->rhsp())}));
    }
    void lowerInitial(AstNodeProcedure* ip) {
        // $readmemh image -> mem_init process (attach_readmem_inits)
        bool anyOther = false;
        for (AstNode* sp = ip->stmtsp(); sp; sp = sp->nextp()) {
            if (AstNodeReadWriteMem* const rp = VN_CAST(sp, NodeReadWriteMem)) {
                lowerReadMem(rp);
            } else {
                anyOther = true;
            }
        }
        if (!anyOther) return;
        // constant-folded `assign x = const` arrives as a single-assign initial
        AstNodeAssign* const ap = VN_CAST(ip->stmtsp(), NodeAssign);
        if (ap && !ap->nextp()) {
            const AstVar* basep = nullptr;
            if (baseVar(ap->lhsp(), basep)) {
                m_processes.push_back(jcomb("assign_" + varName(basep), {assign(ap->lhsp(), ap->rhsp())}));
                return;
            }
        }
        if (ip->stmtsp() && isElab(ip->stmtsp())) {
            m_processes.push_back(jcomb("__initial__" + std::to_string(++m_initialSeq), stmts(ip->stmtsp())));
        }
    }
    static bool readHexWords(const std::string& path, std::vector<std::string>& words) {
        std::vector<std::string> cands = {path};
        if (const char* d = getenv("MEM_INIT_DIR")) cands.push_back(std::string(d) + "/" + path);
        std::ifstream in;
        for (const std::string& c : cands) {
            in.open(c);
            if (in) break;
            in.clear();
        }
        if (!in) return false;
        std::string line;
        size_t addr = 0;
        while (std::getline(in, line)) {
            const size_t cpos = line.find("//");
            if (cpos != std::string::npos) line = line.substr(0, cpos);
            std::istringstream ls{line};
            std::string tok;
            while (ls >> tok) {
                if (tok[0] == '@') {
                    addr = std::stoul(tok.substr(1), nullptr, 16);
                    continue;
                }
                std::string h;
                for (const char c : tok) if (c != '_') h += static_cast<char>(std::tolower(c));
                if (words.size() <= addr) words.resize(addr + 1, "0");
                words[addr++] = "0x" + h;
            }
        }
        return true;
    }
    void lowerReadMem(AstNodeReadWriteMem* rp) {
        const AstVarRef* const mp = VN_CAST(rp->memp(), VarRef);
        const AstConst* const fp = VN_CAST(rp->filenamep(), Const);
        if (!mp || !fp || !fp->num().isString() || !VN_IS(rp, ReadMem)) return;
        std::string f = fp->num().ascii(false, false);
        if (f.size() >= 2 && f.front() == '"' && f.back() == '"') f = f.substr(1, f.size() - 2);
        std::vector<std::string> words;
        if (!readHexWords(f, words) || words.empty()) {
            warn(rp, "$readmemh image " + f + " not found (set MEM_INIT_DIR); memory left uninitialised");
            return;
        }
        int depth = 1;
        const AstNodeDType* const ep = unpackedOf(mp->varp()->dtypep(), depth);
        const int dw = ep->width() > 0 ? ep->width() : 1;
        std::vector<std::string> parts;
        for (auto it = words.rbegin(); it != words.rend(); ++it) parts.push_back(jconst(*it, dw));  // highest address first
        m_processes.push_back(jcomb("mem_init_" + varName(mp->varp()), {jassign(varName(mp->varp()), jcat(parts))}));
    }

    // ---- cells (cell_to_bprocess / cell_to_binstance) ----
    std::string pinExpr(AstCell* cp, const char* name) {
        for (AstPin* pp = cp->pinsp(); pp; pp = VN_AS(pp->nextp(), Pin)) {
            if (pp->name() == name && pp->exprp()) return expr(VN_AS(pp->exprp(), NodeExpr));
        }
        return "";
    }
    const AstVar* pinVar(AstCell* cp, const char* name) {
        for (AstPin* pp = cp->pinsp(); pp; pp = VN_AS(pp->nextp(), Pin)) {
            if (pp->name() == name) {
                if (const AstVarRef* const vp = VN_CAST(pp->exprp(), VarRef)) return vp->varp();
            }
        }
        return nullptr;
    }
    void lowerCell(AstCell* cp) {
        const std::string modName = cp->modp() ? V3EmitStruct::cellTypeName(cp->modp()) : sanitizeName(cp->modName());
        if (modName.rfind("RTL_", 0) == 0 && rtlCell(cp, modName)) return;
        std::vector<std::string> ports;
        for (AstPin* pp = cp->pinsp(); pp; pp = VN_AS(pp->nextp(), Pin)) {
            if (!pp->exprp()) continue;
            ports.push_back("[" + jstr(pp->name()) + "," + expr(VN_AS(pp->exprp(), NodeExpr)) + "]");
        }
        std::vector<std::string> pvals, pstrs;
        if (cp->modp()) {
            for (AstNode* sp = cp->modp()->stmtsp(); sp; sp = sp->nextp()) {
                AstVar* const vp = VN_CAST(sp, Var);
                if (!vp || !vp->isParam()) continue;
                const std::string n = vp->prettyName();
                auto ends = [&](const char* suf) { return n.size() >= std::strlen(suf) && n.compare(n.size() - std::strlen(suf), std::string::npos, suf) == 0; };
                if (ends("_FREQ_MAX") || ends("_FREQ_MIN")) continue;  // simulation-only guard rails
                AstConst* const kp = VN_CAST(vp->valuep(), Const);
                if (!kp) continue;
                const V3Number& num = kp->num();
                if (num.isString() || num.isDouble() || num.isFourState() || num.width() > 62) {
                    std::string lit = num.ascii(true, true);
                    if (num.isString() && lit.size() >= 2 && lit.front() == '"') lit = lit.substr(1, lit.size() - 2);
                    pstrs.push_back("[" + jstr(n) + "," + jstr(lit) + "]");
                } else {
                    pvals.push_back("[" + jstr(n) + "," + std::to_string(static_cast<int64_t>(num.toUQuad())) + "]");
                }
            }
        }
        m_instances.push_back("{\"inst\":" + jstr(m_cellName[cp]) + ",\"module\":" + jstr(modName) + ",\"params\":" + joinList(pvals)
                              + ",\"param_strs\":" + joinList(pstrs) + ",\"ports\":" + joinList(ports) + "}");
    }
    // Vivado RTL_* primitive instances become processes (cell_to_bprocess)
    bool rtlCell(AstCell* cp, const std::string& mn) {
        const AstVar* const o = pinVar(cp, "O");
        const AstVar* const q = pinVar(cp, "Q");
        auto comb2 = [&](const char* op, int w, bool boolr) {
            if (!o) return false;
            const std::string a = pinExpr(cp, "I0"), b = pinExpr(cp, "I1");
            if (a.empty() || b.empty()) return false;
            m_processes.push_back(jcomb(mn + "_inst", {jassign(varName(o), jbin(op, a, b, boolr ? 1 : w, false))}));
            return true;
        };
        if (mn == "RTL_INV") {
            const std::string a = pinExpr(cp, "I0");
            if (!o || a.empty()) return false;
            m_processes.push_back(jcomb(mn + "_inst", {jassign(varName(o), jun("~", a, 64, false))}));
            return true;
        }
        if (mn == "RTL_AND") return comb2("&", 64, false);
        if (mn == "RTL_OR") return comb2("|", 64, false);
        if (mn == "RTL_XOR") return comb2("^", 64, false);
        if (mn == "RTL_ADD") return comb2("+", 64, false);
        if (mn == "RTL_SUB") return comb2("-", 64, false);
        if (mn == "RTL_MUL") return comb2("*", 64, false);
        if (mn == "RTL_LSHIFT") return comb2("<<", 64, false);
        if (mn == "RTL_RSHIFT") return comb2(">>", 64, false);
        if (mn == "RTL_EQ") return comb2("==", 1, true);
        if (mn == "RTL_NEQ") return comb2("!=", 1, true);
        if (mn == "RTL_LT") return comb2("<", 1, true);
        if (mn == "RTL_LEQ") return comb2("<=", 1, true);
        if (mn == "RTL_GT") return comb2(">", 1, true);
        if (mn == "RTL_GEQ") return comb2(">=", 1, true);
        if (mn == "RTL_MUX") {
            const std::string s = pinExpr(cp, "S"), a = pinExpr(cp, "I0"), b = pinExpr(cp, "I1");
            if (!o || s.empty() || a.empty() || b.empty()) return false;
            m_processes.push_back(jcomb(mn + "_inst", {jassign(varName(o), "{\"e\":\"cond\",\"c\":" + s + ",\"t\":" + a + ",\"f\":" + b + "}")}));
            return true;
        }
        if (mn.rfind("RTL_REG", 0) == 0) {
            const AstVar* const c = pinVar(cp, "C");
            const std::string d = pinExpr(cp, "D");
            if (!q || !c || d.empty()) return false;
            const bool async = mn.rfind("RTL_REG_ASYNC", 0) == 0;
            const AstVar* const rstv = pinVar(cp, "RST");
            const std::string rst = pinExpr(cp, "RST");
            const std::string ce = pinExpr(cp, "CE");
            const std::string qn = varName(q);
            std::string data = jassign(qn, d);
            if (!ce.empty()) {
                data = "{\"s\":\"if\",\"c\":" + ce + ",\"t\":[" + data + "],\"e\":[" + jassign(qn, jvar(qn)) + "]}";
            }
            std::string body = data;
            if (!rst.empty()) {
                body = "{\"s\":\"if\",\"c\":" + rst + ",\"t\":[" + jassign(qn, jconstU(0, 64)) + "],\"e\":[" + data + "]}";
            }
            m_processes.push_back("{\"kind\":\"seq\",\"name\":" + jstr(mn + "_inst") + ",\"clock\":" + jstr(varName(c))
                                  + ",\"edge\":\"pos\",\"reset\":" + (rstv ? jstr(varName(rstv)) : std::string("null"))
                                  + ",\"reset_async\":" + (async ? "true" : "false") + ",\"body\":[" + body + "]}");
            return true;
        }
        return false;
    }

    // ---- functions / tasks (extract_funcs) ----
    std::string lowerFunc(AstNodeFTask* fp) {
        std::vector<std::string> params;
        std::vector<std::string> body;
        for (AstNode* sp = fp->stmtsp(); sp; sp = sp->nextp()) {
            if (AstVar* const vp = VN_CAST(sp, Var)) {
                nameVar(vp, "");
                if (vp->isIO()) {
                    const char* dir = vp->direction() == VDirection::OUTPUT ? "output" : vp->direction() == VDirection::INOUT ? "inout" : "input";
                    params.push_back("[" + jstr(varName(vp)) + "," + std::to_string(vp->width() > 0 ? vp->width() : 1) + ",\"" + dir + "\"]");
                }
            }
        }
        if (AstVar* const rv = VN_CAST(fp->fvarp(), Var)) nameVar(rv, "");
        for (AstNode* sp = fp->stmtsp(); sp; sp = sp->nextp()) {
            if (VN_IS(sp, Var)) continue;
            const std::string s = stmt(sp);
            if (!s.empty()) body.push_back(s);
        }
        return "{\"name\":" + jstr(sanitizeName(fp->prettyName())) + ",\"task\":" + (fp->isFunction() ? "false" : "true")
               + ",\"params\":" + joinList(params) + ",\"body\":" + joinList(body) + "}";
    }
};

}  // namespace

//######################################################################

void V3EmitBir::emit(const std::string& filename) {
    UINFO(2, __FUNCTION__ << ":");
    std::ofstream os{filename};
    if (!os) {
        v3fatal("Cannot write BIR output: " << filename);
        return;
    }
    std::vector<std::string> pkgFuncs;
    for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp; modp = VN_AS(modp->nextp(), NodeModule)) {
        if (VN_IS(modp, Package)) {
            for (const std::string& f : BirModule::packageFuncs(modp)) pkgFuncs.push_back(f);
        }
    }
    os << "{\"modules\":[";
    bool first = true;
    for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp; modp = VN_AS(modp->nextp(), NodeModule)) {
        if (!VN_IS(modp, Module) || modp->dead()) continue;
        if (V3EmitStruct::isBlackbox(modp)) continue;
        if (!first) os << ",\n";
        first = false;
        BirModule bm{modp, pkgFuncs};
        os << bm.run();
        os.flush();
    }
    os << "]}\n";
}
