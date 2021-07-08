// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2021 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3String.h"
#include "V3EmitCFunc.h"
#include "V3TSP.h"

#include <map>
#include <vector>

// We use a static char array in VL_VALUE_STRING
constexpr int VL_VALUE_STRING_MAX_WIDTH = 8192;

//######################################################################
// Establish mtask variable sort order in mtasks mode

class EmitVarTspSorter final : public V3TSP::TspStateBase {
private:
    // MEMBERS
    const MTaskIdSet& m_mtaskIds;  // Mtask we're ordering
    static unsigned s_serialNext;  // Unique ID to establish serial order
    unsigned m_serial;  // Serial ordering
public:
    // CONSTRUCTORS
    explicit EmitVarTspSorter(const MTaskIdSet& mtaskIds)
        : m_mtaskIds(mtaskIds) {  // Cannot be {} or GCC 4.8 false warning
        m_serial = ++s_serialNext;  // Cannot be ()/{} or GCC 4.8 false warning
    }
    virtual ~EmitVarTspSorter() = default;
    // METHODS
    virtual bool operator<(const TspStateBase& other) const override {
        return operator<(dynamic_cast<const EmitVarTspSorter&>(other));
    }
    bool operator<(const EmitVarTspSorter& other) const { return m_serial < other.m_serial; }
    const MTaskIdSet& mtaskIds() const { return m_mtaskIds; }
    virtual int cost(const TspStateBase* otherp) const override {
        return cost(dynamic_cast<const EmitVarTspSorter*>(otherp));
    }
    virtual int cost(const EmitVarTspSorter* otherp) const {
        int cost = diffs(m_mtaskIds, otherp->m_mtaskIds);
        cost += diffs(otherp->m_mtaskIds, m_mtaskIds);
        return cost;
    }
    // Returns the number of elements in set_a that don't appear in set_b
    static int diffs(const MTaskIdSet& set_a, const MTaskIdSet& set_b) {
        int diffs = 0;
        for (int i : set_a) {
            if (set_b.find(i) == set_b.end()) ++diffs;
        }
        return diffs;
    }
};

unsigned EmitVarTspSorter::s_serialNext = 0;

//######################################################################
// EmitCFunc

void EmitCFunc::emitCtorSep(bool* firstp) {
    if (*firstp) {
        puts("  : ");
        *firstp = false;
    } else {
        puts(", ");
    }
    if (ofp()->exceededWidth()) puts("\n  ");
}

void EmitCFunc::emitVarCtors(bool* firstp) {
    if (!m_ctorVarsVec.empty()) {
        ofp()->indentInc();
        if (*firstp) puts("\n");
        for (const AstVar* varp : m_ctorVarsVec) {
            const AstBasicDType* const dtypep = VN_CAST(varp->dtypeSkipRefp(), BasicDType);
            if (!dtypep) {
                puts("// Skipping array: ");
                puts(varp->nameProtect());
                puts("\n");
            } else if (dtypep->keyword().isMTaskState()) {
                emitCtorSep(firstp);
                puts(varp->nameProtect());
                puts("(");
                iterate(varp->valuep());
                puts(")");
            } else {
                emitCtorSep(firstp);
                puts(varp->nameProtect());
                puts("(");
                putsQuoted(varp->nameProtect());
                puts(")");
            }
        }
        puts("\n");
        ofp()->indentDec();
    }
}

bool EmitCFunc::emitSimpleOk(AstNodeMath* nodep) {
    // Can we put out a simple (A + B) instead of VL_ADD_III(A,B)?
    if (nodep->emitSimpleOperator() == "") return false;
    if (nodep->isWide()) return false;
    if (nodep->op1p()) {
        if (nodep->op1p()->isWide()) return false;
    }
    if (nodep->op2p()) {
        if (nodep->op2p()->isWide()) return false;
    }
    if (nodep->op3p()) {
        if (nodep->op3p()->isWide()) return false;
    }
    return true;
}

void EmitCFunc::emitOpName(AstNode* nodep, const string& format, AstNode* lhsp, AstNode* rhsp,
                           AstNode* thsp) {
    // Look at emitOperator() format for term/uni/dual/triops,
    // and write out appropriate text.
    //  %n*     node
    //   %nq      emitIQW on the [node]
    //   %nw      width in bits
    //   %nW      width in words
    //   %ni      iterate
    //  %l*     lhsp - if appropriate, then second char as above
    //  %r*     rhsp - if appropriate, then second char as above
    //  %t*     thsp - if appropriate, then second char as above
    //  %k      Potential line break
    //  %P      Wide temporary name
    //  ,       Commas suppressed if the previous field is suppressed
    string nextComma;
    bool needComma = false;
#define COMMA \
    do { \
        if (!nextComma.empty()) { \
            puts(nextComma); \
            nextComma = ""; \
        } \
    } while (false)

    putbs("");
    for (string::const_iterator pos = format.begin(); pos != format.end(); ++pos) {
        if (pos[0] == ',') {
            // Remember we need to add one, but don't do yet to avoid ",)"
            if (needComma) {
                if (pos[1] == ' ') {
                    nextComma = ", ";
                } else
                    nextComma = ",";
                needComma = false;
            }
            if (pos[1] == ' ') ++pos;  // Must do even if no nextComma
        } else if (pos[0] == '%') {
            ++pos;
            bool detail = false;
            AstNode* detailp = nullptr;
            switch (pos[0]) {
            case '%': puts("%"); break;
            case 'k': putbs(""); break;
            case 'n':
                detail = true;
                detailp = nodep;
                break;
            case 'l':
                detail = true;
                detailp = lhsp;
                break;
            case 'r':
                detail = true;
                detailp = rhsp;
                break;
            case 't':
                detail = true;
                detailp = thsp;
                break;
            case 'P':
                if (nodep->isWide()) {
                    UASSERT_OBJ(m_wideTempRefp, nodep,
                                "Wide Op w/ no temp, perhaps missing op in V3EmitC?");
                    COMMA;
                    if (!m_wideTempRefp->selfPointer().empty()) {
                        emitDereference(m_wideTempRefp->selfPointerProtect(m_useSelfForThis));
                    }
                    puts(m_wideTempRefp->varp()->nameProtect());
                    m_wideTempRefp = nullptr;
                    needComma = true;
                }
                break;
            default: nodep->v3fatalSrc("Unknown emitOperator format code: %" << pos[0]); break;
            }
            if (detail) {
                // Get next letter of %[nlrt]
                ++pos;
                switch (pos[0]) {
                case 'q': emitIQW(detailp); break;
                case 'w':
                    COMMA;
                    puts(cvtToStr(detailp->widthMin()));
                    needComma = true;
                    break;
                case 'W':
                    if (lhsp->isWide()) {
                        COMMA;
                        puts(cvtToStr(lhsp->widthWords()));
                        needComma = true;
                    }
                    break;
                case 'i':
                    COMMA;
                    UASSERT_OBJ(detailp, nodep, "emitOperator() references undef node");
                    iterateAndNextNull(detailp);
                    needComma = true;
                    break;
                default:
                    nodep->v3fatalSrc("Unknown emitOperator format code: %[nlrt]" << pos[0]);
                    break;
                }
            }
        } else if (pos[0] == ')') {
            nextComma = "";
            puts(")");
        } else if (pos[0] == '(') {
            COMMA;
            needComma = false;
            puts("(");
        } else {
            // Normal text
            if (isalnum(pos[0])) needComma = true;
            COMMA;
            string s;
            s += pos[0];
            puts(s);
        }
    }
}

// We only do one display at once, so can just use static state
static struct EmitDispState {
    string m_format;  // "%s" and text from user
    std::vector<char> m_argsChar;  // Format of each argument to be printed
    std::vector<AstNode*> m_argsp;  // Each argument to be printed
    std::vector<string> m_argsFunc;  // Function before each argument to be printed
    EmitDispState() { clear(); }
    void clear() {
        m_format = "";
        m_argsChar.clear();
        m_argsp.clear();
        m_argsFunc.clear();
    }
    void pushFormat(const string& fmt) { m_format += fmt; }
    void pushFormat(char fmt) { m_format += fmt; }
    void pushArg(char fmtChar, AstNode* nodep, const string& func) {
        m_argsChar.push_back(fmtChar);
        m_argsp.push_back(nodep);
        m_argsFunc.push_back(func);
    }
} emitDispState;

void EmitCFunc::displayEmit(AstNode* nodep, bool isScan) {
    if (emitDispState.m_format == ""
        && VN_IS(nodep, Display)) {  // not fscanf etc, as they need to return value
        // NOP
    } else {
        // Format
        bool isStmt = false;
        if (const AstFScanF* dispp = VN_CAST(nodep, FScanF)) {
            isStmt = false;
            puts("VL_FSCANF_IX(");
            iterate(dispp->filep());
            puts(",");
        } else if (const AstSScanF* dispp = VN_CAST(nodep, SScanF)) {
            isStmt = false;
            checkMaxWords(dispp->fromp());
            puts("VL_SSCANF_I");
            emitIQW(dispp->fromp());
            puts("X(");
            puts(cvtToStr(dispp->fromp()->widthMin()));
            puts(",");
            iterate(dispp->fromp());
            puts(",");
        } else if (const AstDisplay* dispp = VN_CAST(nodep, Display)) {
            isStmt = true;
            if (dispp->filep()) {
                puts("VL_FWRITEF(");
                iterate(dispp->filep());
                puts(",");
            } else {
                puts("VL_WRITEF(");
            }
        } else if (const AstSFormat* dispp = VN_CAST(nodep, SFormat)) {
            isStmt = true;
            puts("VL_SFORMAT_X(");
            puts(cvtToStr(dispp->lhsp()->widthMin()));
            putbs(",");
            iterate(dispp->lhsp());
            putbs(",");
        } else if (VN_IS(nodep, SFormatF)) {
            isStmt = false;
            puts("VL_SFORMATF_NX(");
        } else {
            nodep->v3fatalSrc("Unknown displayEmit node type");
        }
        ofp()->putsQuoted(emitDispState.m_format);
        // Arguments
        for (unsigned i = 0; i < emitDispState.m_argsp.size(); i++) {
            const char fmt = emitDispState.m_argsChar[i];
            AstNode* argp = emitDispState.m_argsp[i];
            const string func = emitDispState.m_argsFunc[i];
            if (func != "" || argp) {
                puts(",");
                ofp()->indentInc();
                ofp()->putbs("");
                if (func != "") {
                    puts(func);
                } else if (argp) {
                    const bool addrof = isScan || (fmt == '@');
                    if (addrof) puts("&(");
                    iterate(argp);
                    if (!addrof) emitDatap(argp);
                    if (addrof) puts(")");
                }
                ofp()->indentDec();
            }
        }
        // End
        puts(")");
        if (isStmt) {
            puts(";\n");
        } else {
            puts(" ");
        }
        // Prep for next
        emitDispState.clear();
    }
}

void EmitCFunc::displayArg(AstNode* dispp, AstNode** elistp, bool isScan, const string& vfmt,
                           bool ignore, char fmtLetter) {
    // Print display argument, edits elistp
    AstNode* argp = nullptr;
    if (!ignore) {
        argp = *elistp;
        // Prep for next parameter
        *elistp = (*elistp)->nextp();
        if (VL_UNCOVERABLE(!argp)) {
            // expectDisplay() checks this first, so internal error if found here
            dispp->v3error(
                "Internal: Missing arguments for $display-like format");  // LCOV_EXCL_LINE
            return;  // LCOV_EXCL_LINE
        }
        if (argp->widthMin() > VL_VALUE_STRING_MAX_WIDTH) {
            dispp->v3error("Exceeded limit of " + cvtToStr(VL_VALUE_STRING_MAX_WIDTH)
                           + " bits for any $display-like arguments");
        }
        if (argp->widthMin() > 8 && fmtLetter == 'c') {
            // Technically legal, but surely not what the user intended.
            argp->v3warn(WIDTH, dispp->verilogKwd() << "of %c format of > 8 bit value");
        }
    }
    // string pfmt = "%"+displayFormat(argp, vfmt, fmtLetter)+fmtLetter;
    string pfmt;
    if ((fmtLetter == '#' || fmtLetter == 'd') && !isScan
        && vfmt == "") {  // Size decimal output.  Spec says leading spaces, not zeros
        const double mantissabits = ignore ? 0 : (argp->widthMin() - ((fmtLetter == 'd') ? 1 : 0));
        // This is log10(2**mantissabits) as log2(2**mantissabits)/log2(10),
        // + 1.0 rounding bias.
        double dchars = mantissabits / 3.321928094887362 + 1.0;
        if (fmtLetter == 'd') dchars++;  // space for sign
        const int nchars = int(dchars);
        pfmt = string("%") + cvtToStr(nchars) + fmtLetter;
    } else {
        pfmt = string("%") + vfmt + fmtLetter;
    }
    emitDispState.pushFormat(pfmt);
    if (!ignore) {
        if (argp->dtypep()->basicp()->keyword() == AstBasicDTypeKwd::STRING) {
            // string in SystemVerilog is std::string in C++ which is not POD
            emitDispState.pushArg(' ', nullptr, "-1");
        } else {
            emitDispState.pushArg(' ', nullptr, cvtToStr(argp->widthMin()));
        }
        emitDispState.pushArg(fmtLetter, argp, "");
        if (fmtLetter == 't' || fmtLetter == '^') {
            AstSFormatF* fmtp = nullptr;
            if (AstDisplay* nodep = VN_CAST(dispp, Display))
                fmtp = nodep->fmtp();
            else if (AstSFormat* nodep = VN_CAST(dispp, SFormat))
                fmtp = nodep->fmtp();
            else
                fmtp = VN_CAST(dispp, SFormatF);
            UASSERT_OBJ(fmtp, dispp,
                        "Use of %t must be under AstDisplay, AstSFormat, or AstSFormatF");
            UASSERT_OBJ(!fmtp->timeunit().isNone(), fmtp, "timenunit must be set");
            emitDispState.pushArg(' ', nullptr, cvtToStr((int)fmtp->timeunit().powerOfTen()));
        }
    } else {
        emitDispState.pushArg(fmtLetter, nullptr, "");
    }
}

void EmitCFunc::displayNode(AstNode* nodep, AstScopeName* scopenamep, const string& vformat,
                            AstNode* exprsp, bool isScan) {
    AstNode* elistp = exprsp;

    // Convert Verilog display to C printf formats
    //          "%0t" becomes "%d"
    emitDispState.clear();
    string vfmt;
    string::const_iterator pos = vformat.begin();
    bool inPct = false;
    bool ignore = false;
    for (; pos != vformat.end(); ++pos) {
        // UINFO(1, "Parse '" << *pos << "'  IP" << inPct << " List " << cvtToHex(elistp) << endl);
        if (!inPct && pos[0] == '%') {
            inPct = true;
            ignore = false;
            vfmt = "";
        } else if (!inPct) {  // Normal text
            emitDispState.pushFormat(*pos);
        } else {  // Format character
            inPct = false;
            switch (tolower(pos[0])) {
            case '0':  // FALLTHRU
            case '1':  // FALLTHRU
            case '2':  // FALLTHRU
            case '3':  // FALLTHRU
            case '4':  // FALLTHRU
            case '5':  // FALLTHRU
            case '6':  // FALLTHRU
            case '7':  // FALLTHRU
            case '8':  // FALLTHRU
            case '9':  // FALLTHRU
            case '.':  // FALLTHRU
            case '-':
                // Digits, like %5d, etc.
                vfmt += pos[0];
                inPct = true;  // Get more digits
                break;
            case '%':
                emitDispState.pushFormat("%%");  // We're printf'ing it, so need to quote the %
                break;
            case '*':
                vfmt += pos[0];
                inPct = true;  // Get more digits
                ignore = true;
                break;
            // Special codes
            case '~':
                displayArg(nodep, &elistp, isScan, vfmt, ignore, 'd');
                break;  // Signed decimal
            case '@':
                displayArg(nodep, &elistp, isScan, vfmt, ignore, '@');
                break;  // Packed string
            // Spec: h d o b c l
            case 'b': displayArg(nodep, &elistp, isScan, vfmt, ignore, 'b'); break;
            case 'c': displayArg(nodep, &elistp, isScan, vfmt, ignore, 'c'); break;
            case 't': displayArg(nodep, &elistp, isScan, vfmt, ignore, 't'); break;
            case 'd':
                displayArg(nodep, &elistp, isScan, vfmt, ignore, '#');
                break;  // Unsigned decimal
            case 'o': displayArg(nodep, &elistp, isScan, vfmt, ignore, 'o'); break;
            case 'h':  // FALLTHRU
            case 'x': displayArg(nodep, &elistp, isScan, vfmt, ignore, 'x'); break;
            case 's': displayArg(nodep, &elistp, isScan, vfmt, ignore, 's'); break;
            case 'e': displayArg(nodep, &elistp, isScan, vfmt, ignore, 'e'); break;
            case 'f': displayArg(nodep, &elistp, isScan, vfmt, ignore, 'f'); break;
            case 'g': displayArg(nodep, &elistp, isScan, vfmt, ignore, 'g'); break;
            case '^': displayArg(nodep, &elistp, isScan, vfmt, ignore, '^'); break;  // Realtime
            case 'v': displayArg(nodep, &elistp, isScan, vfmt, ignore, 'v'); break;
            case 'u': displayArg(nodep, &elistp, isScan, vfmt, ignore, 'u'); break;
            case 'z': displayArg(nodep, &elistp, isScan, vfmt, ignore, 'z'); break;
            case 'm': {
                UASSERT_OBJ(scopenamep, nodep, "Display with %m but no AstScopeName");
                const string suffix = scopenamep->scopePrettySymName();
                if (suffix == "") {
                    emitDispState.pushFormat("%S");
                } else {
                    emitDispState.pushFormat("%N");  // Add a . when needed
                }
                emitDispState.pushArg(' ', nullptr, "vlSymsp->name()");
                emitDispState.pushFormat(suffix);
                break;
            }
            case 'l': {
                // Better than not compiling
                emitDispState.pushFormat("----");
                break;
            }
            default:
                nodep->v3error("Unknown $display-like format code: '%" << pos[0] << "'");
                break;
            }
        }
    }
    if (VL_UNCOVERABLE(elistp)) {
        // expectFormat also checks this, and should have found it first, so internal
        elistp->v3error("Internal: Extra arguments for $display-like format");  // LCOV_EXCL_LINE
    }
    displayEmit(nodep, isScan);
}

void EmitCFunc::emitVarList(AstNode* firstp, EisWhich which, const string& prefixIfImp,
                            string& sectionr) {
    // Put out a list of signal declarations
    // in order of 0:clocks, 1:vluint8, 2:vluint16, 4:vluint32, 5:vluint64, 6:wide, 7:arrays
    // This aids cache packing and locality
    //
    // Largest->smallest reduces the number of pad variables.  Also
    // experimented with alternating between large->small and small->large
    // on successive Mtask groups, but then when a new mtask gets added may
    // cause a huge delta.
    //
    // TODO: Move this sort to an earlier visitor stage.
    VarSortMap varAnonMap;
    VarSortMap varNonanonMap;

    for (int isstatic = 1; isstatic >= 0; isstatic--) {
        if (prefixIfImp != "" && !isstatic) continue;
        for (AstNode* nodep = firstp; nodep; nodep = nodep->nextp()) {
            if (const AstVar* varp = VN_CAST(nodep, Var)) {
                bool doit = true;
                switch (which) {
                case EVL_CLASS_IO: doit = varp->isIO(); break;
                case EVL_CLASS_SIG:
                    doit = ((varp->isSignal() || varp->isClassMember()) && !varp->isIO());
                    break;
                case EVL_CLASS_TEMP: doit = (varp->isTemp() && !varp->isIO()); break;
                case EVL_CLASS_PAR:
                    doit = (varp->isParam() && !VN_IS(varp->valuep(), Const));
                    break;
                case EVL_CLASS_ALL: doit = true; break;
                case EVL_FUNC_ALL: doit = true; break;
                default: v3fatalSrc("Bad Case");
                }
                if (varp->isStatic() ? !isstatic : isstatic) doit = false;
                if (doit) {
                    const int sigbytes = varp->dtypeSkipRefp()->widthAlignBytes();
                    int sortbytes = 9;
                    if (varp->isUsedClock() && varp->widthMin() == 1) {
                        sortbytes = 0;
                    } else if (VN_IS(varp->dtypeSkipRefp(), UnpackArrayDType)) {
                        sortbytes = 8;
                    } else if (varp->basicp() && varp->basicp()->isOpaque()) {
                        sortbytes = 7;
                    } else if (varp->isScBv() || varp->isScBigUint()) {
                        sortbytes = 6;
                    } else if (sigbytes == 8) {
                        sortbytes = 5;
                    } else if (sigbytes == 4) {
                        sortbytes = 4;
                    } else if (sigbytes == 2) {
                        sortbytes = 2;
                    } else if (sigbytes == 1) {
                        sortbytes = 1;
                    }
                    const bool anonOk
                        = (v3Global.opt.compLimitMembers() != 0  // Enabled
                           && !varp->isStatic() && !varp->isIO()  // Confusing to user
                           && !varp->isSc()  // Aggregates can't be anon
                           && (varp->basicp()
                               && !varp->basicp()->isOpaque())  // Aggregates can't be anon
                           && which != EVL_FUNC_ALL);  // Anon not legal in funcs, and gcc
                                                       // bug free there anyhow
                    if (anonOk) {
                        varAnonMap[sortbytes].push_back(varp);
                    } else {
                        varNonanonMap[sortbytes].push_back(varp);
                    }
                }
            }
        }
    }

    if (!varAnonMap.empty() || !varNonanonMap.empty()) {
        if (!sectionr.empty()) {
            puts(sectionr);
            sectionr = "";
        }
        VarVec anons;
        VarVec nonanons;
        emitVarSort(varAnonMap, &anons);
        emitVarSort(varNonanonMap, &nonanons);
        emitSortedVarList(anons, nonanons, prefixIfImp);
    }
}

void EmitCFunc::emitVarSort(const VarSortMap& vmap, VarVec* sortedp) {
    UASSERT(sortedp->empty(), "Sorted should be initially empty");
    if (!v3Global.opt.mtasks()) {
        // Plain old serial mode. Sort by size, from small to large,
        // to optimize for both packing and small offsets in code.
        for (const auto& itr : vmap) {
            for (VarVec::const_iterator jt = itr.second.begin(); jt != itr.second.end(); ++jt) {
                sortedp->push_back(*jt);
            }
        }
        return;
    }

    // MacroTask mode.  Sort by MTask-affinity group first, size second.
    using MTaskVarSortMap = std::map<const MTaskIdSet, VarSortMap>;
    MTaskVarSortMap m2v;
    for (VarSortMap::const_iterator it = vmap.begin(); it != vmap.end(); ++it) {
        const int size_class = it->first;
        const VarVec& vec = it->second;
        for (const AstVar* varp : vec) { m2v[varp->mtaskIds()][size_class].push_back(varp); }
    }

    // Create a TSP sort state for each MTaskIdSet footprint
    V3TSP::StateVec states;
    for (MTaskVarSortMap::iterator it = m2v.begin(); it != m2v.end(); ++it) {
        states.push_back(new EmitVarTspSorter(it->first));
    }

    // Do the TSP sort
    V3TSP::StateVec sorted_states;
    V3TSP::tspSort(states, &sorted_states);

    for (V3TSP::StateVec::iterator it = sorted_states.begin(); it != sorted_states.end(); ++it) {
        const EmitVarTspSorter* statep = dynamic_cast<const EmitVarTspSorter*>(*it);
        const VarSortMap& localVmap = m2v[statep->mtaskIds()];
        // use rbegin/rend to sort size large->small
        for (VarSortMap::const_reverse_iterator jt = localVmap.rbegin(); jt != localVmap.rend();
             ++jt) {
            const VarVec& vec = jt->second;
            for (VarVec::const_iterator kt = vec.begin(); kt != vec.end(); ++kt) {
                sortedp->push_back(*kt);
            }
        }
        VL_DO_DANGLING(delete statep, statep);
    }
}

void EmitCFunc::emitSortedVarList(const VarVec& anons, const VarVec& nonanons,
                                  const string& prefixIfImp) {
    string curVarCmt;
    // Output anons
    {
        const int anonMembers = anons.size();
        const int lim = v3Global.opt.compLimitMembers();
        int anonL3s = 1;
        int anonL2s = 1;
        int anonL1s = 1;
        if (anonMembers > (lim * lim * lim)) {
            anonL3s = (anonMembers + (lim * lim * lim) - 1) / (lim * lim * lim);
            anonL2s = lim;
            anonL1s = lim;
        } else if (anonMembers > (lim * lim)) {
            anonL2s = (anonMembers + (lim * lim) - 1) / (lim * lim);
            anonL1s = lim;
        } else if (anonMembers > lim) {
            anonL1s = (anonMembers + lim - 1) / lim;
        }
        if (anonL1s != 1)
            puts("// Anonymous structures to workaround compiler member-count bugs\n");
        auto it = anons.cbegin();
        for (int l3 = 0; l3 < anonL3s && it != anons.cend(); ++l3) {
            if (anonL3s != 1) puts("struct {\n");
            for (int l2 = 0; l2 < anonL2s && it != anons.cend(); ++l2) {
                if (anonL2s != 1) puts("struct {\n");
                for (int l1 = 0; l1 < anonL1s && it != anons.cend(); ++l1) {
                    if (anonL1s != 1) puts("struct {\n");
                    for (int l0 = 0; l0 < lim && it != anons.cend(); ++l0) {
                        const AstVar* varp = *it;
                        emitVarDecl(varp, prefixIfImp);
                        ++it;
                    }
                    if (anonL1s != 1) puts("};\n");
                }
                if (anonL2s != 1) puts("};\n");
            }
            if (anonL3s != 1) puts("};\n");
        }
        // Leftovers, just in case off by one error somewhere above
        for (; it != anons.end(); ++it) {
            const AstVar* varp = *it;
            emitVarDecl(varp, prefixIfImp);
        }
    }
    // Output nonanons
    for (const AstVar* varp : nonanons) {
        if (varp->isIO() && varp->isSc()) { m_ctorVarsVec.push_back(varp); }
        AstBasicDType* const basicp = varp->basicp();
        if (basicp && basicp->keyword().isMTaskState()) { m_ctorVarsVec.push_back(varp); }
        emitVarDecl(varp, prefixIfImp);
    }
}

void EmitCFunc::emitCCallArgs(AstNodeCCall* nodep) {
    bool comma = false;
    if (nodep->funcp()->isLoose() && !nodep->funcp()->isStatic()) {
        UASSERT_OBJ(!nodep->selfPointer().empty(), nodep,
                    "Call to loose method without self pointer");
        puts(nodep->selfPointerProtect(m_useSelfForThis));
        comma = true;
    }
    if (!nodep->argTypes().empty()) {
        if (comma) puts(", ");
        puts(nodep->argTypes());
        comma = true;
    }
    for (AstNode* subnodep = nodep->argsp(); subnodep; subnodep = subnodep->nextp()) {
        if (comma) puts(", ");
        iterate(subnodep);
        comma = true;
    }
}

void EmitCFunc::emitDereference(const string& pointer) {
    if (pointer[0] == '(' && pointer[1] == '&') {
        // remove "address of" followed by immediate dereference
        // Note: this relies on only the form '(&OBJECT)' being used by Verilator
        puts(pointer.substr(2, pointer.length() - 3));
        puts(".");
    } else {
        puts(pointer);
        puts("->");
    }
}

void EmitCFunc::emitCvtPackStr(AstNode* nodep) {
    if (const AstConst* constp = VN_CAST(nodep, Const)) {
        putbs("std::string(");
        putsQuoted(constp->num().toString());
        puts(")");
    } else {
        putbs("VL_CVT_PACK_STR_N");
        emitIQW(nodep);
        puts("(");
        if (nodep->isWide()) {
            // Note argument width, not node width (which is always 32)
            puts(cvtToStr(nodep->widthWords()));
            puts(", ");
        }
        iterateAndNextNull(nodep);
        puts(")");
    }
}

void EmitCFunc::emitCvtWideArray(AstNode* nodep, AstNode* fromp) {
    putbs("VL_CVT_W_A(");
    iterate(nodep);
    puts(", ");
    iterate(fromp);
    putbs(".atDefault()");  // Not accessed; only to get the proper type of values
    puts(")");
}

void EmitCFunc::emitConstant(AstConst* nodep, AstVarRef* assigntop, const string& assignString) {
    // Put out constant set to the specified variable, or given variable in a string
    if (nodep->num().isFourState()) {
        nodep->v3warn(E_UNSUPPORTED, "Unsupported: 4-state numbers in this context");
    } else if (nodep->num().isString()) {
        putbs("std::string(");
        putsQuoted(nodep->num().toString());
        puts(")");
    } else if (nodep->isWide()) {
        int upWidth = nodep->num().widthMin();
        int chunks = 0;
        if (upWidth > EMITC_NUM_CONSTW * VL_EDATASIZE) {
            // Output e.g. 8 words in groups of e.g. 8
            chunks = (upWidth - 1) / (EMITC_NUM_CONSTW * VL_EDATASIZE);
            upWidth %= (EMITC_NUM_CONSTW * VL_EDATASIZE);
            if (upWidth == 0) upWidth = (EMITC_NUM_CONSTW * VL_EDATASIZE);
        }
        {  // Upper e.g. 8 words
            if (chunks) {
                putbs("VL_CONSTHI_W_");
                puts(cvtToStr(VL_WORDS_I(upWidth)));
                puts("X(");
                puts(cvtToStr(nodep->widthMin()));
                puts(",");
                puts(cvtToStr(chunks * EMITC_NUM_CONSTW * VL_EDATASIZE));
            } else {
                putbs("VL_CONST_W_");
                puts(cvtToStr(VL_WORDS_I(upWidth)));
                puts("X(");
                puts(cvtToStr(nodep->widthMin()));
            }
            puts(",");
            if (!assigntop) {
                puts(assignString);
            } else if (VN_IS(assigntop, VarRef)) {
                if (!assigntop->selfPointer().empty()) {
                    emitDereference(assigntop->selfPointerProtect(m_useSelfForThis));
                }
                puts(assigntop->varp()->nameProtect());
            } else {
                iterateAndNextNull(assigntop);
            }
            for (int word = VL_WORDS_I(upWidth) - 1; word >= 0; word--) {
                // Only 32 bits - llx + long long here just to appease CPP format warning
                ofp()->printf(",0x%08" VL_PRI64 "x",
                              static_cast<vluint64_t>(
                                  nodep->num().edataWord(word + chunks * EMITC_NUM_CONSTW)));
            }
            puts(")");
        }
        for (chunks--; chunks >= 0; chunks--) {
            puts(";\n");
            putbs("VL_CONSTLO_W_");
            puts(cvtToStr(EMITC_NUM_CONSTW));
            puts("X(");
            puts(cvtToStr(chunks * EMITC_NUM_CONSTW * VL_EDATASIZE));
            puts(",");
            if (!assigntop) {
                puts(assignString);
            } else if (VN_IS(assigntop, VarRef)) {
                if (!assigntop->selfPointer().empty()) {
                    emitDereference(assigntop->selfPointerProtect(m_useSelfForThis));
                }
                puts(assigntop->varp()->nameProtect());
            } else {
                iterateAndNextNull(assigntop);
            }
            for (int word = EMITC_NUM_CONSTW - 1; word >= 0; word--) {
                // Only 32 bits - llx + long long here just to appease CPP format warning
                ofp()->printf(",0x%08" VL_PRI64 "x",
                              static_cast<vluint64_t>(
                                  nodep->num().edataWord(word + chunks * EMITC_NUM_CONSTW)));
            }
            puts(")");
        }
    } else if (nodep->isDouble()) {
        if (int(nodep->num().toDouble()) == nodep->num().toDouble()
            && nodep->num().toDouble() < 1000 && nodep->num().toDouble() > -1000) {
            ofp()->printf("%3.1f", nodep->num().toDouble());  // Force decimal point
        } else {
            // Not %g as will not always put in decimal point, so not obvious to compiler
            // is a real number
            ofp()->printf("%.17e", nodep->num().toDouble());
        }
    } else if (nodep->isQuad()) {
        vluint64_t num = nodep->toUQuad();
        if (num < 10) {
            ofp()->printf("%" VL_PRI64 "uULL", num);
        } else {
            ofp()->printf("0x%" VL_PRI64 "xULL", num);
        }
    } else {
        uint32_t num = nodep->toUInt();
        // Only 32 bits - llx + long long here just to appease CPP format warning
        if (num < 10) {
            puts(cvtToStr(num));
        } else {
            ofp()->printf("0x%" VL_PRI64 "x", static_cast<vluint64_t>(num));
        }
        // If signed, we'll do our own functions
        // But must be here, or <= comparisons etc may end up signed
        puts("U");
    }
}

void EmitCFunc::emitSetVarConstant(const string& assignString, AstConst* constp) {
    if (!constp->isWide()) {
        puts(assignString);
        puts(" = ");
    }
    emitConstant(constp, nullptr, assignString);
    puts(";\n");
}

void EmitCFunc::emitVarReset(AstVar* varp) {
    AstNodeDType* const dtypep = varp->dtypep()->skipRefp();
    const string varNameProtected
        = VN_IS(m_modp, Class) ? varp->nameProtect() : "vlSelf->" + varp->nameProtect();
    if (varp->isIO() && m_modp->isTop() && optSystemC()) {
        // System C top I/O doesn't need loading, as the lower level subinst code does it.}
    } else if (varp->isParam()) {
        UASSERT_OBJ(varp->valuep(), varp, "No init for a param?");
        // If a simple CONST value we initialize it using an enum
        // If an ARRAYINIT we initialize it using an initial block similar to a signal
        // puts("// parameter "+varp->nameProtect()+" = "+varp->valuep()->name()+"\n");
    } else if (AstInitArray* initarp = VN_CAST(varp->valuep(), InitArray)) {
        if (AstUnpackArrayDType* adtypep = VN_CAST(dtypep, UnpackArrayDType)) {
            if (initarp->defaultp()) {
                puts("for (int __Vi=0; __Vi<" + cvtToStr(adtypep->elementsConst()));
                puts("; ++__Vi) {\n");
                emitSetVarConstant(varNameProtected + "[__Vi]",
                                   VN_CAST(initarp->defaultp(), Const));
                puts("}\n");
            }
            const AstInitArray::KeyItemMap& mapr = initarp->map();
            for (const auto& itr : mapr) {
                AstNode* valuep = itr.second->valuep();
                emitSetVarConstant(varNameProtected + "[" + cvtToStr(itr.first) + "]",
                                   VN_CAST(valuep, Const));
            }
        } else {
            varp->v3fatalSrc("InitArray under non-arrayed var");
        }
    } else {
        puts(emitVarResetRecurse(varp, varNameProtected, dtypep, 0, ""));
    }
}

string EmitCFunc::emitVarResetRecurse(const AstVar* varp, const string& varNameProtected,
                                      AstNodeDType* dtypep, int depth, const string& suffix) {
    dtypep = dtypep->skipRefp();
    AstBasicDType* basicp = dtypep->basicp();
    // Returns string to do resetting, empty to do nothing (which caller should handle)
    if (AstAssocArrayDType* adtypep = VN_CAST(dtypep, AssocArrayDType)) {
        // Access std::array as C array
        const string cvtarray = (adtypep->subDTypep()->isWide() ? ".data()" : "");
        return emitVarResetRecurse(varp, varNameProtected, adtypep->subDTypep(), depth + 1,
                                   suffix + ".atDefault()" + cvtarray);
    } else if (VN_IS(dtypep, ClassRefDType)) {
        return "";  // Constructor does it
    } else if (AstDynArrayDType* adtypep = VN_CAST(dtypep, DynArrayDType)) {
        // Access std::array as C array
        const string cvtarray = (adtypep->subDTypep()->isWide() ? ".data()" : "");
        return emitVarResetRecurse(varp, varNameProtected, adtypep->subDTypep(), depth + 1,
                                   suffix + ".atDefault()" + cvtarray);
    } else if (AstQueueDType* adtypep = VN_CAST(dtypep, QueueDType)) {
        // Access std::array as C array
        const string cvtarray = (adtypep->subDTypep()->isWide() ? ".data()" : "");
        return emitVarResetRecurse(varp, varNameProtected, adtypep->subDTypep(), depth + 1,
                                   suffix + ".atDefault()" + cvtarray);
    } else if (AstUnpackArrayDType* adtypep = VN_CAST(dtypep, UnpackArrayDType)) {
        UASSERT_OBJ(adtypep->hi() >= adtypep->lo(), varp,
                    "Should have swapped msb & lsb earlier.");
        const string ivar = string("__Vi") + cvtToStr(depth);
        const string pre = ("for (int " + ivar + "=" + cvtToStr(0) + "; " + ivar + "<"
                            + cvtToStr(adtypep->elementsConst()) + "; ++" + ivar + ") {\n");
        const string below = emitVarResetRecurse(varp, varNameProtected, adtypep->subDTypep(),
                                                 depth + 1, suffix + "[" + ivar + "]");
        const string post = "}\n";
        return below.empty() ? "" : pre + below + post;
    } else if (basicp && basicp->keyword() == AstBasicDTypeKwd::STRING) {
        // String's constructor deals with it
        return "";
    } else if (basicp) {
        bool zeroit
            = (varp->attrFileDescr()  // Zero so we don't core dump if never $fopen
               || (basicp && basicp->isZeroInit())
               || (v3Global.opt.underlineZero() && !varp->name().empty() && varp->name()[0] == '_')
               || (v3Global.opt.xInitial() == "fast" || v3Global.opt.xInitial() == "0"));
        splitSizeInc(1);
        if (dtypep->isWide()) {  // Handle unpacked; not basicp->isWide
            string out;
            if (varp->valuep()) {
                AstConst* const constp = VN_CAST(varp->valuep(), Const);
                if (!constp) varp->v3fatalSrc("non-const initializer for variable");
                for (int w = 0; w < varp->widthWords(); ++w) {
                    out += varNameProtected + suffix + "[" + cvtToStr(w) + "] = ";
                    out += cvtToStr(constp->num().edataWord(w)) + "U;\n";
                }
            } else {
                out += zeroit ? "VL_ZERO_RESET_W(" : "VL_RAND_RESET_W(";
                out += cvtToStr(dtypep->widthMin());
                out += ", " + varNameProtected + suffix + ");\n";
            }
            return out;
        } else {
            string out = varNameProtected + suffix;
            // If --x-initial-edge is set, we want to force an initial
            // edge on uninitialized clocks (from 'X' to whatever the
            // first value is). Since the class is instantiated before
            // initial blocks are evaluated, this should not clash
            // with any initial block settings.
            if (zeroit || (v3Global.opt.xInitialEdge() && varp->isUsedClock())) {
                out += " = 0;\n";
            } else {
                out += " = VL_RAND_RESET_";
                out += dtypep->charIQWN();
                out += "(" + cvtToStr(dtypep->widthMin()) + ");\n";
            }
            return out;
        }
    } else {
        v3fatalSrc("Unknown node type in reset generator: " << varp->prettyTypeName());
    }
    return "";
}

void EmitCFunc::doubleOrDetect(AstChangeDet* changep, bool& gotOne) {
    // cppcheck-suppress variableScope
    static int s_addDoubleOr = 10;  // Determined experimentally as best
    if (!changep->rhsp()) {
        if (!gotOne) {
            gotOne = true;
        } else {
            puts(" | ");
        }
        iterateAndNextNull(changep->lhsp());
    } else {
        AstNode* lhsp = changep->lhsp();
        AstNode* rhsp = changep->rhsp();
        UASSERT_OBJ(VN_IS(lhsp, VarRef) || VN_IS(lhsp, ArraySel), changep, "Not ref?");
        UASSERT_OBJ(VN_IS(rhsp, VarRef) || VN_IS(rhsp, ArraySel), changep, "Not ref?");
        for (int word = 0; word < (changep->lhsp()->isWide() ? changep->lhsp()->widthWords() : 1);
             ++word) {
            if (!gotOne) {
                gotOne = true;
                s_addDoubleOr = 10;
                puts("(");
            } else if (--s_addDoubleOr == 0) {
                puts("|| (");
                s_addDoubleOr = 10;
            } else {
                puts(" | (");
            }
            iterateAndNextNull(changep->lhsp());
            if (changep->lhsp()->isWide()) puts("[" + cvtToStr(word) + "]");
            if (changep->lhsp()->isDouble()) {
                puts(" != ");
            } else {
                puts(" ^ ");
            }
            iterateAndNextNull(changep->rhsp());
            if (changep->lhsp()->isWide()) puts("[" + cvtToStr(word) + "]");
            puts(")");
        }
    }
}

void EmitCFunc::emitChangeDet() {
    putsDecoration("// Change detection\n");
    puts("QData __req = false;  // Logically a bool\n");  // But not because it results in
    // faster code
    bool gotOne = false;
    for (AstChangeDet* changep : m_blkChangeDetVec) {
        if (changep->lhsp()) {
            if (!gotOne) {  // Not a clocked block
                puts("__req |= (");
            } else {
                puts("\n");
            }
            doubleOrDetect(changep, gotOne);
        }
    }
    if (gotOne) puts(");\n");
    if (gotOne && !v3Global.opt.protectIds()) {
        // puts("VL_DEBUG_IF( if (__req) cout<<\"- CLOCKREQ );");
        for (AstChangeDet* nodep : m_blkChangeDetVec) {
            if (nodep->lhsp()) {
                puts("VL_DEBUG_IF( if(__req && (");
                bool gotOneIgnore = false;
                doubleOrDetect(nodep, gotOneIgnore);
                string varname;
                if (VN_IS(nodep->lhsp(), VarRef)) {
                    varname = ": " + VN_CAST(nodep->lhsp(), VarRef)->varp()->prettyName();
                }
                puts(")) VL_DBG_MSGF(\"        CHANGE: ");
                puts(protect(nodep->fileline()->filename()));
                puts(":" + cvtToStr(nodep->fileline()->lineno()));
                puts(varname + "\\n\"); );\n");
            }
        }
    }
}
