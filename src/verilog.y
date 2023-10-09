// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Bison grammer file
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// Original code here by Paul Wasson and Duane Galbi
//*************************************************************************
// clang-format off

%{
#ifdef NEVER_JUST_FOR_CLANG_FORMAT
 }
#endif
// clang-format on
#include "V3Ast.h"
#include "V3Config.h"
#include "V3Global.h"
#include "V3ParseImp.h"  // Defines YYTYPE; before including bison header

#include <cstdarg>
#include <cstdlib>
#include <stack>

#define YYERROR_VERBOSE 1  // For prior to Bison 3.6
#define YYINITDEPTH 10000  // Older bisons ignore YYMAXDEPTH
#define YYMAXDEPTH 10000

// Pick up new lexer
#define yylex PARSEP->tokenToBison
#define BBUNSUP(fl, msg) (fl)->v3warn(E_UNSUPPORTED, msg)
#define GATEUNSUP(fl, tok) \
    { BBUNSUP((fl), "Unsupported: Verilog 1995 gate primitive: " << (tok)); }
#define RISEFALLDLYUNSUP(nodep) \
    if (nodep->fileline()->timingOn() && v3Global.opt.timing().isSetTrue()) { \
        nodep->v3warn(RISEFALLDLY, \
                      "Unsupported: rising/falling/turn-off delays. Using the first delay"); \
    }
#define MINTYPMAXDLYUNSUP(nodep) \
    if (nodep->fileline()->timingOn() && v3Global.opt.timing().isSetTrue()) { \
        nodep->v3warn( \
            MINTYPMAXDLY, \
            "Unsupported: minimum/typical/maximum delay expressions. Using the typical delay"); \
    }
// Given a list of assignments, if there is a delay add it to each assignment
#define DELAY_LIST(delayp, assignsp) \
    if (delayp) { \
        for (auto* nodep = assignsp; nodep; nodep = nodep->nextp()) { \
            auto* const assignp = VN_AS(nodep, NodeAssign); \
            assignp->timingControlp(nodep == assignsp ? delayp : delayp->cloneTree(false)); \
        } \
    }
#define STRENGTHUNSUP(nodep) \
    { \
        if (nodep) { \
            BBUNSUP((nodep->fileline()), "Unsupported: Strength specifier on this gate type"); \
            nodep->deleteTree(); \
        } \
    }

//======================================================================
// Statics (for here only)

#define PARSEP V3ParseImp::parsep()
#define SYMP PARSEP->symp()
#define GRAMMARP V3ParseGrammar::singletonp()

class V3ParseGrammar {
public:
    AstVar* m_varAttrp = nullptr;  // Current variable for attribute adding
    AstRange* m_gateRangep = nullptr;  // Current range for gate declarations
    AstNode* m_scopedSigAttr = nullptr;  // Pointer to default signal attribute
    AstCase* m_caseAttrp = nullptr;  // Current case statement for attribute adding
    AstNodeDType* m_varDTypep = nullptr;  // Pointer to data type for next signal declaration
    AstNodeDType* m_memDTypep = nullptr;  // Pointer to data type for next member declaration
    AstDelay* m_netDelayp = nullptr;  // Pointer to delay for next signal declaration
    AstStrengthSpec* m_netStrengthp = nullptr;  // Pointer to strength for next net declaration
    FileLine* m_instModuleFl = nullptr;  // Fileline of module referenced for instantiations
    AstPin* m_instParamp = nullptr;  // Parameters for instantiations
    string m_instModule;  // Name of module referenced for instantiations
    VVarType m_varDecl;  // Type for next signal declaration (reg/wire/etc)
    VDirection m_varIO;  // Direction for next signal declaration (reg/wire/etc)
    VLifetime m_varLifetime;  // Static/Automatic for next signal
    bool m_impliedDecl = false;  // Allow implied wire declarations
    bool m_varDeclTyped = false;  // Var got reg/wire for dedup check
    bool m_pinAnsi = false;  // In ANSI parameter or port list
    bool m_tracingParse = true;  // Tracing disable for parser
    bool m_inImplements = false;  // Is inside class implements list
    bool m_insideProperty = false;  // Is inside property declaration
    bool m_typedPropertyPort = false;  // Typed property port occurred on port lists
    bool m_modportImpExpActive
        = false;  // Standalone ID is a tf_identifier instead of port_identifier
    bool m_modportImpExpLastIsExport
        = false;  // Last import_export statement in modportPortsDecl is an export

    int m_pinNum = -1;  // Pin number currently parsing
    std::stack<int> m_pinStack;  // Queue of pin numbers being parsed

    static int s_modTypeImpNum;  // Implicit type number, incremented each module

    // CONSTRUCTORS
    V3ParseGrammar() {
        m_varDecl = VVarType::UNKNOWN;
        m_varIO = VDirection::NONE;
    }
    static V3ParseGrammar* singletonp() {
        static V3ParseGrammar singleton;
        return &singleton;
    }

    // METHODS
    AstArg* argWrapList(AstNodeExpr* nodep) VL_MT_DISABLED;
    bool allTracingOn(FileLine* fl) {
        return v3Global.opt.trace() && m_tracingParse && fl->tracingOn();
    }
    AstRange* scrubRange(AstNodeRange* rangep) VL_MT_DISABLED;
    AstNodeDType* createArray(AstNodeDType* basep, AstNodeRange* rangep,
                              bool isPacked) VL_MT_DISABLED;
    AstVar* createVariable(FileLine* fileline, const string& name, AstNodeRange* arrayp,
                           AstNode* attrsp) VL_MT_DISABLED;
    AstNode* createSupplyExpr(FileLine* fileline, const string& name, int value) VL_MT_DISABLED;
    AstText* createTextQuoted(FileLine* fileline, const string& text) {
        string newtext = GRAMMARP->unquoteString(fileline, text);
        return new AstText{fileline, newtext};
    }
    AstNode* createCellOrIfaceRef(FileLine* fileline, const string& name, AstPin* pinlistp,
                                  AstNodeRange* rangelistp, bool parens) {
        // Must clone m_instParamp as may be comma'ed list of instances
        VSymEnt* const foundp = SYMP->symCurrentp()->findIdFallback(name);
        if (foundp && VN_IS(foundp->nodep(), Port)) {
            // It's a non-ANSI interface, not a cell declaration
            m_varAttrp = nullptr;
            m_varDecl = VVarType::IFACEREF;
            m_varIO = VDirection::NONE;
            m_varLifetime = VLifetime::NONE;
            setDType(new AstIfaceRefDType{fileline, "", GRAMMARP->m_instModule});
            m_varDeclTyped = true;
            AstVar* const nodep = createVariable(fileline, name, rangelistp, nullptr);
            return nodep;
        }
        AstCell* const nodep = new AstCell{
            fileline,
            GRAMMARP->m_instModuleFl,
            name,
            GRAMMARP->m_instModule,
            pinlistp,
            (GRAMMARP->m_instParamp ? GRAMMARP->m_instParamp->cloneTree(true) : nullptr),
            GRAMMARP->scrubRange(rangelistp)};
        nodep->hasNoParens(!parens);
        nodep->trace(GRAMMARP->allTracingOn(fileline));
        return nodep;
    }
    AstDisplay* createDisplayError(FileLine* fileline) {
        AstDisplay* nodep = new AstDisplay{fileline, VDisplayType::DT_ERROR, "", nullptr, nullptr};
        AstNode::addNext<AstNode, AstNode>(nodep, new AstStop{fileline, true});
        return nodep;
    }
    AstNodeExpr* createGatePin(AstNodeExpr* exprp) {
        AstRange* const rangep = m_gateRangep;
        if (!rangep) {
            return exprp;
        } else {
            return new AstGatePin{rangep->fileline(), exprp, rangep->cloneTree(true)};
        }
    }
    AstSenTree* createClockSenTree(FileLine* fl, AstNodeExpr* exprp) {
        return new AstSenTree{fl, new AstSenItem{fl, VEdgeType::ET_CHANGED, exprp}};
    }
    AstNodeExpr* createGlobalClockParseRef(FileLine* fl) {
        return new AstParseRef{fl, VParseRefExp::PX_TEXT, "__024global_clock", nullptr, nullptr};
    }
    AstSenTree* createGlobalClockSenTree(FileLine* fl) {
        return createClockSenTree(fl, createGlobalClockParseRef(fl));
    }
    AstNode* createTypedef(FileLine* fl, const string& name, AstNode* attrsp, AstNodeDType* basep,
                           AstNodeRange* rangep) {
        AstNode* const nodep = new AstTypedef{fl, name, attrsp, VFlagChildDType{},
                                              GRAMMARP->createArray(basep, rangep, false)};
        SYMP->reinsert(nodep);
        PARSEP->tagNodep(nodep);
        return nodep;
    }
    AstNode* createTypedefFwd(FileLine* fl, const string& name) {
        AstNode* const nodep = new AstTypedefFwd{fl, name};
        SYMP->reinsert(nodep);
        PARSEP->tagNodep(nodep);
        return nodep;
    }
    void endLabel(FileLine* fl, AstNode* nodep, string* endnamep) {
        endLabel(fl, nodep->prettyName(), endnamep);
    }
    void endLabel(FileLine* fl, const string& name, string* endnamep) {
        if (fl && endnamep && *endnamep != "" && name != *endnamep
            && name != AstNode::prettyName(*endnamep)) {
            fl->v3warn(ENDLABEL, "End label '" << *endnamep << "' does not match begin label '"
                                               << name << "'");
        }
    }
    void setVarDecl(VVarType type) { m_varDecl = type; }
    void setDType(AstNodeDType* dtypep) {
        if (m_varDTypep) VL_DO_CLEAR(m_varDTypep->deleteTree(), m_varDTypep = nullptr);
        m_varDTypep = dtypep;
    }
    void setNetDelay(AstDelay* netDelayp) { m_netDelayp = netDelayp; }
    void setNetStrength(AstStrengthSpec* netStrengthp) { m_netStrengthp = netStrengthp; }
    void pinPush() {
        m_pinStack.push(m_pinNum);
        m_pinNum = 1;
    }
    void pinPop(FileLine* fl) {
        if (VL_UNCOVERABLE(m_pinStack.empty())) { fl->v3fatalSrc("Underflow of pin stack"); }
        m_pinNum = m_pinStack.top();
        m_pinStack.pop();
    }
    AstNodeDType* addRange(AstBasicDType* dtypep, AstNodeRange* rangesp, bool isPacked) {
        // If dtypep isn't basic, don't use this, call createArray() instead
        if (!rangesp) {
            return dtypep;
        } else {
            // If rangesp is "wire [3:3][2:2][1:1] foo [5:5][4:4]"
            // then [1:1] becomes the basicdtype range; everything else is arraying
            // the final [5:5][4:4] will be passed in another call to createArray
            AstNodeRange* rangearraysp = nullptr;
            if (dtypep->isRanged()) {
                rangearraysp = rangesp;  // Already a range; everything is an array
            } else {
                AstNodeRange* finalp = rangesp;
                while (finalp->nextp()) finalp = VN_CAST(finalp->nextp(), Range);
                if (finalp != rangesp) {
                    finalp->unlinkFrBack();
                    rangearraysp = rangesp;
                }
                if (AstRange* const finalRangep = VN_CAST(finalp, Range)) {  // not an UnsizedRange
                    if (dtypep->implicit()) {
                        // It's no longer implicit but a wire logic type
                        AstBasicDType* const newp = new AstBasicDType{
                            dtypep->fileline(), VBasicDTypeKwd::LOGIC, dtypep->numeric(),
                            dtypep->width(), dtypep->widthMin()};
                        VL_DO_DANGLING(dtypep->deleteTree(), dtypep);
                        dtypep = newp;
                    }
                    dtypep->rangep(finalRangep);
                }
            }
            return createArray(dtypep, rangearraysp, isPacked);
        }
    }
    string unquoteString(FileLine* fileline, string text) VL_MT_DISABLED;
    void checkDpiVer(FileLine* fileline, const string& str) {
        if (str != "DPI-C" && !v3Global.opt.bboxSys()) {
            fileline->v3error("Unsupported DPI type '" << str << "': Use 'DPI-C'");
        }
    }
    // Given a list of clocking declarations, put them in clocking items
    AstClockingItem* makeClockingItemList(FileLine* flp, const VDirection direction,
                                          AstNodeExpr* skewp, AstNode* const clockingDeclps) {
        AstClockingItem* itemsp = nullptr;
        for (AstNode *nodep = clockingDeclps, *nextp; nodep; nodep = nextp) {
            nextp = nodep->nextp();
            if (nextp) nextp->unlinkFrBackWithNext();
            if (itemsp && skewp) skewp = skewp->cloneTree(false);
            AstClockingItem* itemp = new AstClockingItem{flp, direction, skewp, nodep};
            itemsp = itemsp ? itemsp->addNext(itemp) : itemp;
        }
        return itemsp;
    }

    void setScopedSigAttr(AstNode* attrsp) {
        if (m_scopedSigAttr) {  // clearing set attribute
            VL_DO_DANGLING(m_scopedSigAttr->deleteTree(), m_scopedSigAttr);
        }
        m_scopedSigAttr = attrsp;
    }

    void createScopedSigAttr(VAttrType vattrT) {
        setScopedSigAttr(new AstAttrOf{PARSEP->lexFileline(), vattrT});
    }

    AstNode* cloneScopedSigAttr() const {
        return m_scopedSigAttr ? m_scopedSigAttr->cloneTree(true) : nullptr;
    }

    static void addForkStmtsp(AstFork* forkp, AstNode* stmtsp) {
        forkp->addStmtsp(stmtsp);
        for (AstNode* stmtp = stmtsp; stmtp; stmtp = stmtp->nextp()) {
            AstVar* const varp = VN_CAST(stmtp, Var);
            if (!varp) break;
            varp->unlinkFrBack();
            varp->funcLocal(true);
            forkp->addInitsp(varp);
        }
    }
};

const VBasicDTypeKwd LOGIC = VBasicDTypeKwd::LOGIC;  // Shorthand "LOGIC"
const VBasicDTypeKwd LOGIC_IMPLICIT = VBasicDTypeKwd::LOGIC_IMPLICIT;

int V3ParseGrammar::s_modTypeImpNum = 0;

//======================================================================
// Macro functions

// Only use in empty rules, so lines point at beginnings
#define CRELINE() (PARSEP->bisonLastFileline()->copyOrSameFileLineApplied())
#define FILELINE_OR_CRE(nodep) ((nodep) ? (nodep)->fileline() : CRELINE())

#define VARRESET_LIST(decl) \
    { \
        GRAMMARP->m_pinNum = 1; \
        VARRESET(); \
        VARDECL(decl); \
    }  // Start of pinlist
#define VARRESET_NONLIST(decl) \
    { \
        GRAMMARP->m_pinNum = 0; \
        VARRESET(); \
        VARDECL(decl); \
    }  // Not in a pinlist
#define VARRESET() \
    { \
        VARDECL(UNKNOWN); \
        VARIO(NONE); \
        VARDTYPE_NDECL(nullptr); \
        GRAMMARP->m_varLifetime = VLifetime::NONE; \
        GRAMMARP->m_varDeclTyped = false; \
    }
#define VARDECL(type) \
    { GRAMMARP->setVarDecl(VVarType::type); }
#define VARIO(type) \
    { GRAMMARP->m_varIO = VDirection::type; }
#define VARLIFE(flag) \
    { GRAMMARP->m_varLifetime = flag; }
#define VARDTYPE(dtypep) \
    { \
        GRAMMARP->setDType(dtypep); \
        GRAMMARP->m_varDeclTyped = true; \
    }
#define VARDTYPE_NDECL(dtypep) \
    { GRAMMARP->setDType(dtypep); }  // Port that is range or signed only (not a decl)

#define VARDONEA(fl, name, array, attrs) GRAMMARP->createVariable((fl), (name), (array), (attrs))
#define VARDONEP(portp, array, attrs) \
    GRAMMARP->createVariable((portp)->fileline(), (portp)->name(), (array), (attrs))
#define PINNUMINC() (GRAMMARP->m_pinNum++)

#define GATERANGE(rangep) \
    { GRAMMARP->m_gateRangep = rangep; }

#define INSTPREP(modfl, modname, paramsp) \
    { \
        GRAMMARP->m_impliedDecl = true; \
        GRAMMARP->m_instModuleFl = modfl; \
        GRAMMARP->m_instModule = modname; \
        GRAMMARP->m_instParamp = paramsp; \
    }

#define DEL(nodep) \
    { \
        if (nodep) nodep->deleteTree(); \
    }

// Apply a strength to a list of nodes under beginp
#define STRENGTH_LIST(beginp, strengthSpecNodep, typeToCast) \
    { \
        if (AstStrengthSpec* const specp = VN_CAST(strengthSpecNodep, StrengthSpec)) { \
            for (auto* nodep = beginp; nodep; nodep = nodep->nextp()) { \
                auto* const assignp = VN_AS(nodep, typeToCast); \
                assignp->strengthSpecp(nodep == beginp ? specp : specp->cloneTree(false)); \
            } \
        } \
    }

static void ERRSVKWD(FileLine* fileline, const string& tokname) {
    static int toldonce = 0;
    fileline->v3error(
        std::string{"Unexpected '"} + tokname + "': '" + tokname
        + "' is a SystemVerilog keyword misused as an identifier."
        + (!toldonce++ ? "\n" + fileline->warnMore()
                             + "... Suggest modify the Verilog-2001 code to avoid SV keywords,"
                             + " or use `begin_keywords or --language."
                       : ""));
}

static void UNSUPREAL(FileLine* fileline) {
    fileline->v3warn(SHORTREAL,
                     "Unsupported: shortreal being promoted to real (suggest use real instead)");
}

//======================================================================

void yyerror(const char* errmsg) { PARSEP->bisonLastFileline()->v3error(errmsg); }

template <typename T_Node, typename T_Next>
static T_Node* addNextNull(T_Node* nodep, T_Next* nextp) {
    if (!nextp) return nodep;
    return AstNode::addNext<T_Node, T_Next>(nodep, nextp);
}

//======================================================================

class AstSenTree;
// clang-format off
%}

// Bison 3.0 and newer
BISONPRE_VERSION(3.0,%define parse.error verbose)

// We run bison with the -d argument. This tells it to generate a
// header file with token names. Old versions of bison pasted the
// contents of that file into the generated source as well; newer
// versions just include it.
//
// Since we run bison through ../bisonpre, it doesn't know the correct
// header file name, so we need to tell it.
BISONPRE_VERSION(3.7,%define api.header.include {"V3ParseBison.h"})

// When writing Bison patterns we use yTOKEN instead of "token",
// so Bison will error out on unknown "token"s.

// Generic lexer tokens, for example a number
// IEEE: real_number
%token<cdouble>         yaFLOATNUM      "FLOATING-POINT NUMBER"

// IEEE: identifier, class_identifier, class_variable_identifier,
// covergroup_variable_identifier, dynamic_array_variable_identifier,
// enum_identifier, interface_identifier, interface_instance_identifier,
// package_identifier, type_identifier, variable_identifier,
%token<strp>            yaID__ETC       "IDENTIFIER"
%token<strp>            yaID__CC        "IDENTIFIER-::"
%token<strp>            yaID__LEX       "IDENTIFIER-in-lex"
%token<strp>            yaID__aTYPE     "TYPE-IDENTIFIER"
//                      Can't predecode aFUNCTION, can declare after use
//                      Can't predecode aINTERFACE, can declare after use
//                      Can't predecode aTASK, can declare after use

// IEEE: integral_number
%token<nump>            yaINTNUM        "INTEGER NUMBER"
// IEEE: time_literal + time_unit
%token<cdouble>         yaTIMENUM       "TIME NUMBER"
// IEEE: string_literal
%token<strp>            yaSTRING        "STRING"
%token<strp>            yaSTRING__IGNORE "STRING-ignored"       // Used when expr:string not allowed

%token<fl>              yaTIMINGSPEC    "TIMING SPEC ELEMENT"

%token<fl>              ygenSTRENGTH    "STRENGTH keyword (strong1/etc)"

%token<strp>            yaTABLELINE     "TABLE LINE"

%token<strp>            yaSCHDR         "`systemc_header BLOCK"
%token<strp>            yaSCINT         "`systemc_ctor BLOCK"
%token<strp>            yaSCIMP         "`systemc_dtor BLOCK"
%token<strp>            yaSCIMPH        "`systemc_interface BLOCK"
%token<strp>            yaSCCTOR        "`systemc_implementation BLOCK"
%token<strp>            yaSCDTOR        "`systemc_imp_header BLOCK"

%token<fl>              yVLT_CLOCKER                "clocker"
%token<fl>              yVLT_CLOCK_ENABLE           "clock_enable"
%token<fl>              yVLT_COVERAGE_BLOCK_OFF     "coverage_block_off"
%token<fl>              yVLT_COVERAGE_OFF           "coverage_off"
%token<fl>              yVLT_COVERAGE_ON            "coverage_on"
%token<fl>              yVLT_FORCEABLE              "forceable"
%token<fl>              yVLT_FULL_CASE              "full_case"
%token<fl>              yVLT_HIER_BLOCK             "hier_block"
%token<fl>              yVLT_INLINE                 "inline"
%token<fl>              yVLT_ISOLATE_ASSIGNMENTS    "isolate_assignments"
%token<fl>              yVLT_LINT_OFF               "lint_off"
%token<fl>              yVLT_LINT_ON                "lint_on"
%token<fl>              yVLT_NO_CLOCKER             "no_clocker"
%token<fl>              yVLT_NO_INLINE              "no_inline"
%token<fl>              yVLT_PARALLEL_CASE          "parallel_case"
%token<fl>              yVLT_PROFILE_DATA           "profile_data"
%token<fl>              yVLT_PUBLIC                 "public"
%token<fl>              yVLT_PUBLIC_FLAT            "public_flat"
%token<fl>              yVLT_PUBLIC_FLAT_RD         "public_flat_rd"
%token<fl>              yVLT_PUBLIC_FLAT_RW         "public_flat_rw"
%token<fl>              yVLT_PUBLIC_MODULE          "public_module"
%token<fl>              yVLT_SC_BV                  "sc_bv"
%token<fl>              yVLT_SFORMAT                "sformat"
%token<fl>              yVLT_SPLIT_VAR              "split_var"
%token<fl>              yVLT_TIMING_OFF             "timing_off"
%token<fl>              yVLT_TIMING_ON              "timing_on"
%token<fl>              yVLT_TRACING_OFF            "tracing_off"
%token<fl>              yVLT_TRACING_ON             "tracing_on"

%token<fl>              yVLT_D_BLOCK    "--block"
%token<fl>              yVLT_D_COST     "--cost"
%token<fl>              yVLT_D_FILE     "--file"
%token<fl>              yVLT_D_FUNCTION "--function"
%token<fl>              yVLT_D_LEVELS   "--levels"
%token<fl>              yVLT_D_LINES    "--lines"
%token<fl>              yVLT_D_MATCH    "--match"
%token<fl>              yVLT_D_MODEL    "--model"
%token<fl>              yVLT_D_MODULE   "--module"
%token<fl>              yVLT_D_MTASK    "--mtask"
%token<fl>              yVLT_D_RULE     "--rule"
%token<fl>              yVLT_D_SCOPE    "--scope"
%token<fl>              yVLT_D_TASK     "--task"
%token<fl>              yVLT_D_VAR      "--var"

%token<strp>            yaD_PLI         "${pli-system}"

%token<fl>              yaT_NOUNCONNECTED  "`nounconnecteddrive"
%token<fl>              yaT_RESETALL    "`resetall"
%token<fl>              yaT_UNCONNECTED_PULL0  "`unconnected_drive pull0"
%token<fl>              yaT_UNCONNECTED_PULL1  "`unconnected_drive pull1"

// <fl> is the fileline, abbreviated to shorten "$<fl>1" references
%token<fl>              '!'
%token<fl>              '#'
%token<fl>              '%'
%token<fl>              '&'
%token<fl>              '('  // See also yP_PAR__STRENGTH
%token<fl>              ')'
%token<fl>              '*'
%token<fl>              '+'
%token<fl>              ','
%token<fl>              '-'
%token<fl>              '.'
%token<fl>              '/'
%token<fl>              ':'  // See also yP_COLON__BEGIN or yP_COLON__FORK
%token<fl>              ';'
%token<fl>              '<'
%token<fl>              '='
%token<fl>              '>'
%token<fl>              '?'
%token<fl>              '@'
%token<fl>              '['
%token<fl>              ']'
%token<fl>              '^'
%token<fl>              '{'
%token<fl>              '|'
%token<fl>              '}'
%token<fl>              '~'

// Specific keywords
// yKEYWORD means match "keyword"
// Other cases are yXX_KEYWORD where XX makes it unique,
// for example yP_ for punctuation based operators.
// Double underscores "yX__Y" means token X followed by Y,
// and "yX__ETC" means X folled by everything but Y(s).
%token<fl>              ya1STEP         "1step"
%token<fl>              yACCEPT_ON      "accept_on"
%token<fl>              yALIAS          "alias"
%token<fl>              yALWAYS         "always"
%token<fl>              yALWAYS_COMB    "always_comb"
%token<fl>              yALWAYS_FF      "always_ff"
%token<fl>              yALWAYS_LATCH   "always_latch"
%token<fl>              yAND            "and"
%token<fl>              yASSERT         "assert"
%token<fl>              yASSIGN         "assign"
%token<fl>              yASSUME         "assume"
%token<fl>              yAUTOMATIC      "automatic"
%token<fl>              yBEFORE         "before"
%token<fl>              yBEGIN          "begin"
%token<fl>              yBIND           "bind"
%token<fl>              yBINS           "bins"
%token<fl>              yBINSOF         "binsof"
%token<fl>              yBIT            "bit"
%token<fl>              yBREAK          "break"
%token<fl>              yBUF            "buf"
%token<fl>              yBUFIF0         "bufif0"
%token<fl>              yBUFIF1         "bufif1"
%token<fl>              yBYTE           "byte"
%token<fl>              yCASE           "case"
%token<fl>              yCASEX          "casex"
%token<fl>              yCASEZ          "casez"
%token<fl>              yCHANDLE        "chandle"
%token<fl>              yCHECKER        "checker"
%token<fl>              yCLASS          "class"
%token<fl>              yCLOCKING       "clocking"
%token<fl>              yCMOS           "cmos"
%token<fl>              yCONSTRAINT     "constraint"
%token<fl>              yCONST__ETC     "const"
%token<fl>              yCONST__LEX     "const-in-lex"
%token<fl>              yCONST__REF     "const-then-ref"
%token<fl>              yCONTEXT        "context"
%token<fl>              yCONTINUE       "continue"
%token<fl>              yCOVER          "cover"
%token<fl>              yCOVERGROUP     "covergroup"
%token<fl>              yCOVERPOINT     "coverpoint"
%token<fl>              yCROSS          "cross"
%token<fl>              yDEASSIGN       "deassign"
%token<fl>              yDEFAULT        "default"
%token<fl>              yDEFPARAM       "defparam"
%token<fl>              yDISABLE        "disable"
%token<fl>              yDIST           "dist"
%token<fl>              yDO             "do"
%token<fl>              yEDGE           "edge"
%token<fl>              yELSE           "else"
%token<fl>              yEND            "end"
%token<fl>              yENDCASE        "endcase"
%token<fl>              yENDCHECKER     "endchecker"
%token<fl>              yENDCLASS       "endclass"
%token<fl>              yENDCLOCKING    "endclocking"
%token<fl>              yENDFUNCTION    "endfunction"
%token<fl>              yENDGENERATE    "endgenerate"
%token<fl>              yENDGROUP       "endgroup"
%token<fl>              yENDINTERFACE   "endinterface"
%token<fl>              yENDMODULE      "endmodule"
%token<fl>              yENDPACKAGE     "endpackage"
%token<fl>              yENDPRIMITIVE   "endprimitive"
%token<fl>              yENDPROGRAM     "endprogram"
%token<fl>              yENDPROPERTY    "endproperty"
%token<fl>              yENDSEQUENCE    "endsequence"
%token<fl>              yENDSPECIFY     "endspecify"
%token<fl>              yENDTABLE       "endtable"
%token<fl>              yENDTASK        "endtask"
%token<fl>              yENUM           "enum"
%token<fl>              yEVENT          "event"
%token<fl>              yEVENTUALLY     "eventually"
%token<fl>              yEXPECT         "expect"
%token<fl>              yEXPORT         "export"
%token<fl>              yEXTENDS        "extends"
%token<fl>              yEXTERN         "extern"
%token<fl>              yFINAL          "final"
%token<fl>              yFIRST_MATCH    "first_match"
%token<fl>              yFOR            "for"
%token<fl>              yFORCE          "force"
%token<fl>              yFOREACH        "foreach"
%token<fl>              yFOREVER        "forever"
%token<fl>              yFORK           "fork"
%token<fl>              yFORKJOIN       "forkjoin"
%token<fl>              yFUNCTION       "function"
%token<fl>              yGENERATE       "generate"
%token<fl>              yGENVAR         "genvar"
%token<fl>              yGLOBAL__CLOCKING "global-then-clocking"
%token<fl>              yGLOBAL__ETC    "global"
%token<fl>              yGLOBAL__LEX    "global-in-lex"
%token<fl>              yHIGHZ0         "highz0"
%token<fl>              yHIGHZ1         "highz1"
%token<fl>              yIF             "if"
%token<fl>              yIFF            "iff"
%token<fl>              yIGNORE_BINS    "ignore_bins"
%token<fl>              yILLEGAL_BINS   "illegal_bins"
%token<fl>              yIMPLEMENTS     "implements"
%token<fl>              yIMPLIES        "implies"
%token<fl>              yIMPORT         "import"
%token<fl>              yINITIAL        "initial"
%token<fl>              yINOUT          "inout"
%token<fl>              yINPUT          "input"
%token<fl>              yINSIDE         "inside"
%token<fl>              yINT            "int"
%token<fl>              yINTEGER        "integer"
%token<fl>              yINTERCONNECT   "interconnect"
%token<fl>              yINTERFACE      "interface"
%token<fl>              yINTERSECT      "intersect"
%token<fl>              yJOIN           "join"
%token<fl>              yJOIN_ANY       "join_any"
%token<fl>              yJOIN_NONE      "join_none"
%token<fl>              yLET            "let"
%token<fl>              yLOCALPARAM     "localparam"
%token<fl>              yLOCAL__COLONCOLON "local-then-::"
%token<fl>              yLOCAL__ETC     "local"
%token<fl>              yLOCAL__LEX     "local-in-lex"
%token<fl>              yLOGIC          "logic"
%token<fl>              yLONGINT        "longint"
%token<fl>              yMATCHES        "matches"
%token<fl>              yMODPORT        "modport"
%token<fl>              yMODULE         "module"
%token<fl>              yNAND           "nand"
%token<fl>              yNEGEDGE        "negedge"
%token<fl>              yNETTYPE        "nettype"
%token<fl>              yNEW__ETC       "new"
%token<fl>              yNEW__LEX       "new-in-lex"
%token<fl>              yNEW__PAREN     "new-then-paren"
%token<fl>              yNEXTTIME       "nexttime"
%token<fl>              yNMOS           "nmos"
%token<fl>              yNOR            "nor"
%token<fl>              yNOT            "not"
%token<fl>              yNOTIF0         "notif0"
%token<fl>              yNOTIF1         "notif1"
%token<fl>              yNULL           "null"
%token<fl>              yOR             "or"
%token<fl>              yOUTPUT         "output"
%token<fl>              yPACKAGE        "package"
%token<fl>              yPACKED         "packed"
%token<fl>              yPARAMETER      "parameter"
%token<fl>              yPMOS           "pmos"
%token<fl>              yPOSEDGE        "posedge"
%token<fl>              yPRIMITIVE      "primitive"
%token<fl>              yPRIORITY       "priority"
%token<fl>              yPROGRAM        "program"
%token<fl>              yPROPERTY       "property"
%token<fl>              yPROTECTED      "protected"
%token<fl>              yPULL0          "pull0"
%token<fl>              yPULL1          "pull1"
%token<fl>              yPULLDOWN       "pulldown"
%token<fl>              yPULLUP         "pullup"
%token<fl>              yPURE           "pure"
%token<fl>              yRAND           "rand"
%token<fl>              yRANDC          "randc"
%token<fl>              yRANDCASE       "randcase"
%token<fl>              yRANDOMIZE      "randomize"
%token<fl>              yRANDSEQUENCE   "randsequence"
%token<fl>              yRCMOS          "rcmos"
%token<fl>              yREAL           "real"
%token<fl>              yREALTIME       "realtime"
%token<fl>              yREF            "ref"
%token<fl>              yREG            "reg"
%token<fl>              yREJECT_ON      "reject_on"
%token<fl>              yRELEASE        "release"
%token<fl>              yREPEAT         "repeat"
%token<fl>              yRESTRICT       "restrict"
%token<fl>              yRETURN         "return"
%token<fl>              yRNMOS          "rnmos"
%token<fl>              yRPMOS          "rpmos"
%token<fl>              yRTRAN          "rtran"
%token<fl>              yRTRANIF0       "rtranif0"
%token<fl>              yRTRANIF1       "rtranif1"
%token<fl>              ySCALARED       "scalared"
%token<fl>              ySEQUENCE       "sequence"
%token<fl>              ySHORTINT       "shortint"
%token<fl>              ySHORTREAL      "shortreal"
%token<fl>              ySIGNED         "signed"
%token<fl>              ySOFT           "soft"
%token<fl>              ySOLVE          "solve"
%token<fl>              ySPECIFY        "specify"
%token<fl>              ySPECPARAM      "specparam"
%token<fl>              ySTATIC__CONSTRAINT "static-then-constraint"
%token<fl>              ySTATIC__ETC    "static"
%token<fl>              ySTATIC__LEX    "static-in-lex"
%token<fl>              ySTRING         "string"
%token<fl>              ySTRONG         "strong"
%token<fl>              ySTRONG0        "strong0"
%token<fl>              ySTRONG1        "strong1"
%token<fl>              ySTRUCT         "struct"
%token<fl>              ySUPER          "super"
%token<fl>              ySUPPLY0        "supply0"
%token<fl>              ySUPPLY1        "supply1"
%token<fl>              ySYNC_ACCEPT_ON "sync_accept_on"
%token<fl>              ySYNC_REJECT_ON "sync_reject_on"
%token<fl>              yS_ALWAYS       "s_always"
%token<fl>              yS_EVENTUALLY   "s_eventually"
%token<fl>              yS_NEXTTIME     "s_nexttime"
%token<fl>              yS_UNTIL        "s_until"
%token<fl>              yS_UNTIL_WITH   "s_until_with"
%token<fl>              yTABLE          "table"
//UNSUP %token<fl>      yTAGGED         "tagged"
%token<fl>              yTASK           "task"
%token<fl>              yTHIS           "this"
%token<fl>              yTHROUGHOUT     "throughout"
%token<fl>              yTIME           "time"
%token<fl>              yTIMEPRECISION  "timeprecision"
%token<fl>              yTIMEUNIT       "timeunit"
%token<fl>              yTRAN           "tran"
%token<fl>              yTRANIF0        "tranif0"
%token<fl>              yTRANIF1        "tranif1"
%token<fl>              yTRI            "tri"
%token<fl>              yTRI0           "tri0"
%token<fl>              yTRI1           "tri1"
%token<fl>              yTRIAND         "triand"
%token<fl>              yTRIOR          "trior"
%token<fl>              yTRIREG         "trireg"
%token<fl>              yTRUE           "true"
%token<fl>              yTYPEDEF        "typedef"
%token<fl>              yTYPE__EQ       "type-then-eqneq"
%token<fl>              yTYPE__ETC      "type"
%token<fl>              yTYPE__LEX      "type-in-lex"
%token<fl>              yUNION          "union"
%token<fl>              yUNIQUE         "unique"
%token<fl>              yUNIQUE0        "unique0"
%token<fl>              yUNSIGNED       "unsigned"
%token<fl>              yUNTIL          "until"
%token<fl>              yUNTIL_WITH     "until_with"
%token<fl>              yUNTYPED        "untyped"
%token<fl>              yVAR            "var"
%token<fl>              yVECTORED       "vectored"
%token<fl>              yVIRTUAL__CLASS "virtual-then-class"
%token<fl>              yVIRTUAL__ETC   "virtual"
%token<fl>              yVIRTUAL__INTERFACE     "virtual-then-interface"
%token<fl>              yVIRTUAL__LEX   "virtual-in-lex"
%token<fl>              yVIRTUAL__anyID "virtual-then-identifier"
%token<fl>              yVOID           "void"
%token<fl>              yWAIT           "wait"
%token<fl>              yWAIT_ORDER     "wait_order"
%token<fl>              yWAND           "wand"
%token<fl>              yWEAK           "weak"
%token<fl>              yWEAK0          "weak0"
%token<fl>              yWEAK1          "weak1"
%token<fl>              yWHILE          "while"
%token<fl>              yWILDCARD       "wildcard"
%token<fl>              yWIRE           "wire"
%token<fl>              yWITHIN         "within"
%token<fl>              yWITH__BRA      "with-then-["
%token<fl>              yWITH__CUR      "with-then-{"
%token<fl>              yWITH__ETC      "with"
%token<fl>              yWITH__LEX      "with-in-lex"
%token<fl>              yWITH__PAREN    "with-then-("
%token<fl>              yWOR            "wor"
%token<fl>              yWREAL          "wreal"
%token<fl>              yXNOR           "xnor"
%token<fl>              yXOR            "xor"

%token<fl>              yD_ACOS         "$acos"
%token<fl>              yD_ACOSH        "$acosh"
%token<fl>              yD_ASIN         "$asin"
%token<fl>              yD_ASINH        "$asinh"
%token<fl>              yD_ATAN         "$atan"
%token<fl>              yD_ATAN2        "$atan2"
%token<fl>              yD_ATANH        "$atanh"
%token<fl>              yD_BITS         "$bits"
%token<fl>              yD_BITSTOREAL   "$bitstoreal"
%token<fl>              yD_BITSTOSHORTREAL "$bitstoshortreal"
%token<fl>              yD_C            "$c"
%token<fl>              yD_CAST         "$cast"
%token<fl>              yD_CEIL         "$ceil"
%token<fl>              yD_CHANGED      "$changed"
%token<fl>              yD_CHANGED_GCLK "$changed_gclk"
%token<fl>              yD_CLOG2        "$clog2"
%token<fl>              yD_COS          "$cos"
%token<fl>              yD_COSH         "$cosh"
%token<fl>              yD_COUNTBITS    "$countbits"
%token<fl>              yD_COUNTONES    "$countones"
%token<fl>              yD_DIMENSIONS   "$dimensions"
%token<fl>              yD_DISPLAY      "$display"
%token<fl>              yD_DISPLAYB     "$displayb"
%token<fl>              yD_DISPLAYH     "$displayh"
%token<fl>              yD_DISPLAYO     "$displayo"
%token<fl>              yD_DIST_CHI_SQUARE "$dist_chi_square"
%token<fl>              yD_DIST_ERLANG  "$dist_erlang"
%token<fl>              yD_DIST_EXPONENTIAL "$dist_exponential"
%token<fl>              yD_DIST_NORMAL  "$dist_normal"
%token<fl>              yD_DIST_POISSON "$dist_poisson"
%token<fl>              yD_DIST_T       "$dist_t"
%token<fl>              yD_DIST_UNIFORM "$dist_uniform"
%token<fl>              yD_DUMPALL      "$dumpall"
%token<fl>              yD_DUMPFILE     "$dumpfile"
%token<fl>              yD_DUMPFLUSH    "$dumpflush"
%token<fl>              yD_DUMPLIMIT    "$dumplimit"
%token<fl>              yD_DUMPOFF      "$dumpoff"
%token<fl>              yD_DUMPON       "$dumpon"
%token<fl>              yD_DUMPPORTS    "$dumpports"
%token<fl>              yD_DUMPVARS     "$dumpvars"
%token<fl>              yD_ERROR        "$error"
%token<fl>              yD_EXIT         "$exit"
%token<fl>              yD_EXP          "$exp"
%token<fl>              yD_FATAL        "$fatal"
%token<fl>              yD_FCLOSE       "$fclose"
%token<fl>              yD_FDISPLAY     "$fdisplay"
%token<fl>              yD_FDISPLAYB    "$fdisplayb"
%token<fl>              yD_FDISPLAYH    "$fdisplayh"
%token<fl>              yD_FDISPLAYO    "$fdisplayo"
%token<fl>              yD_FELL         "$fell"
%token<fl>              yD_FELL_GCLK    "$fell_gclk"
%token<fl>              yD_FEOF         "$feof"
%token<fl>              yD_FERROR       "$ferror"
%token<fl>              yD_FFLUSH       "$fflush"
%token<fl>              yD_FGETC        "$fgetc"
%token<fl>              yD_FGETS        "$fgets"
%token<fl>              yD_FINISH       "$finish"
%token<fl>              yD_FLOOR        "$floor"
%token<fl>              yD_FMONITOR     "$fmonitor"
%token<fl>              yD_FMONITORB    "$fmonitorb"
%token<fl>              yD_FMONITORH    "$fmonitorh"
%token<fl>              yD_FMONITORO    "$fmonitoro"
%token<fl>              yD_FOPEN        "$fopen"
%token<fl>              yD_FREAD        "$fread"
%token<fl>              yD_FREWIND      "$frewind"
%token<fl>              yD_FSCANF       "$fscanf"
%token<fl>              yD_FSEEK        "$fseek"
%token<fl>              yD_FSTROBE      "$fstrobe"
%token<fl>              yD_FSTROBEB     "$fstrobeb"
%token<fl>              yD_FSTROBEH     "$fstrobeh"
%token<fl>              yD_FSTROBEO     "$fstrobeo"
%token<fl>              yD_FTELL        "$ftell"
%token<fl>              yD_FWRITE       "$fwrite"
%token<fl>              yD_FWRITEB      "$fwriteb"
%token<fl>              yD_FWRITEH      "$fwriteh"
%token<fl>              yD_FWRITEO      "$fwriteo"
%token<fl>              yD_GLOBAL_CLOCK "$global_clock"
%token<fl>              yD_HIGH         "$high"
%token<fl>              yD_HYPOT        "$hypot"
%token<fl>              yD_INCREMENT    "$increment"
%token<fl>              yD_INFO         "$info"
%token<fl>              yD_ISUNBOUNDED  "$isunbounded"
%token<fl>              yD_ISUNKNOWN    "$isunknown"
%token<fl>              yD_ITOR         "$itor"
%token<fl>              yD_LEFT         "$left"
%token<fl>              yD_LN           "$ln"
%token<fl>              yD_LOG10        "$log10"
%token<fl>              yD_LOW          "$low"
%token<fl>              yD_MONITOR      "$monitor"
%token<fl>              yD_MONITORB     "$monitorb"
%token<fl>              yD_MONITORH     "$monitorh"
%token<fl>              yD_MONITORO     "$monitoro"
%token<fl>              yD_MONITOROFF   "$monitoroff"
%token<fl>              yD_MONITORON    "$monitoron"
%token<fl>              yD_ONEHOT       "$onehot"
%token<fl>              yD_ONEHOT0      "$onehot0"
%token<fl>              yD_PAST         "$past"
%token<fl>              yD_POW          "$pow"
%token<fl>              yD_PRINTTIMESCALE "$printtimescale"
%token<fl>              yD_RANDOM       "$random"
%token<fl>              yD_READMEMB     "$readmemb"
%token<fl>              yD_READMEMH     "$readmemh"
%token<fl>              yD_REALTIME     "$realtime"
%token<fl>              yD_REALTOBITS   "$realtobits"
%token<fl>              yD_REWIND       "$rewind"
%token<fl>              yD_RIGHT        "$right"
%token<fl>              yD_ROOT         "$root"
%token<fl>              yD_ROSE         "$rose"
%token<fl>              yD_ROSE_GCLK    "$rose_gclk"
%token<fl>              yD_RTOI         "$rtoi"
%token<fl>              yD_SAMPLED      "$sampled"
%token<fl>              yD_SFORMAT      "$sformat"
%token<fl>              yD_SFORMATF     "$sformatf"
%token<fl>              yD_SHORTREALTOBITS "$shortrealtobits"
%token<fl>              yD_SIGNED       "$signed"
%token<fl>              yD_SIN          "$sin"
%token<fl>              yD_SINH         "$sinh"
%token<fl>              yD_SIZE         "$size"
%token<fl>              yD_SQRT         "$sqrt"
%token<fl>              yD_SSCANF       "$sscanf"
%token<fl>              yD_STABLE       "$stable"
%token<fl>              yD_STABLE_GCLK  "$stable_gclk"
%token<fl>              yD_STACKTRACE   "$stacktrace"
%token<fl>              yD_STIME        "$stime"
%token<fl>              yD_STOP         "$stop"
%token<fl>              yD_STROBE       "$strobe"
%token<fl>              yD_STROBEB      "$strobeb"
%token<fl>              yD_STROBEH      "$strobeh"
%token<fl>              yD_STROBEO      "$strobeo"
%token<fl>              yD_SWRITE       "$swrite"
%token<fl>              yD_SWRITEB      "$swriteb"
%token<fl>              yD_SWRITEH      "$swriteh"
%token<fl>              yD_SWRITEO      "$swriteo"
%token<fl>              yD_SYSTEM       "$system"
%token<fl>              yD_TAN          "$tan"
%token<fl>              yD_TANH         "$tanh"
%token<fl>              yD_TESTPLUSARGS "$test$plusargs"
%token<fl>              yD_TIME         "$time"
%token<fl>              yD_TIMEFORMAT   "$timeformat"
%token<fl>              yD_TIMEPRECISION "$timeprecision"
%token<fl>              yD_TIMEUNIT     "$timeunit"
%token<fl>              yD_TYPENAME     "$typename"
%token<fl>              yD_UNGETC       "$ungetc"
%token<fl>              yD_UNIT         "$unit"
%token<fl>              yD_UNPACKED_DIMENSIONS "$unpacked_dimensions"
%token<fl>              yD_UNSIGNED     "$unsigned"
%token<fl>              yD_URANDOM      "$urandom"
%token<fl>              yD_URANDOM_RANGE "$urandom_range"
%token<fl>              yD_VALUEPLUSARGS "$value$plusargs"
%token<fl>              yD_WARNING      "$warning"
%token<fl>              yD_WRITE        "$write"
%token<fl>              yD_WRITEB       "$writeb"
%token<fl>              yD_WRITEH       "$writeh"
%token<fl>              yD_WRITEMEMB    "$writememb"
%token<fl>              yD_WRITEMEMH    "$writememh"
%token<fl>              yD_WRITEO       "$writeo"

%token<fl>              yVL_CLOCKER               "/*verilator clocker*/"
%token<fl>              yVL_CLOCK_ENABLE          "/*verilator clock_enable*/"
%token<fl>              yVL_COVERAGE_BLOCK_OFF    "/*verilator coverage_block_off*/"
%token<fl>              yVL_FORCEABLE             "/*verilator forceable*/"
%token<fl>              yVL_FULL_CASE             "/*verilator full_case*/"
%token<fl>              yVL_HIER_BLOCK            "/*verilator hier_block*/"
%token<fl>              yVL_INLINE_MODULE         "/*verilator inline_module*/"
%token<fl>              yVL_ISOLATE_ASSIGNMENTS   "/*verilator isolate_assignments*/"
%token<fl>              yVL_NO_CLOCKER            "/*verilator no_clocker*/"
%token<fl>              yVL_NO_INLINE_MODULE      "/*verilator no_inline_module*/"
%token<fl>              yVL_NO_INLINE_TASK        "/*verilator no_inline_task*/"
%token<fl>              yVL_PARALLEL_CASE         "/*verilator parallel_case*/"
%token<fl>              yVL_PUBLIC                "/*verilator public*/"
%token<fl>              yVL_PUBLIC_FLAT           "/*verilator public_flat*/"
%token<fl>              yVL_PUBLIC_FLAT_ON        "/*verilator public_flat_on*/"
%token<fl>              yVL_PUBLIC_FLAT_RD        "/*verilator public_flat_rd*/"
%token<fl>              yVL_PUBLIC_FLAT_RD_ON     "/*verilator public_flat_rd_on*/"
%token<fl>              yVL_PUBLIC_FLAT_RW        "/*verilator public_flat_rw*/"
%token<fl>              yVL_PUBLIC_FLAT_RW_ON     "/*verilator public_flat_rw_on*/"
%token<fl>              yVL_PUBLIC_FLAT_RW_ON_SNS "/*verilator public_flat_rw_on_sns*/"
%token<fl>              yVL_PUBLIC_ON             "/*verilator public_on*/"
%token<fl>              yVL_PUBLIC_OFF            "/*verilator public_off*/"
%token<fl>              yVL_PUBLIC_MODULE         "/*verilator public_module*/"
%token<fl>              yVL_SC_BV                 "/*verilator sc_bv*/"
%token<fl>              yVL_SFORMAT               "/*verilator sformat*/"
%token<fl>              yVL_SPLIT_VAR             "/*verilator split_var*/"
%token<strp>            yVL_TAG                   "/*verilator tag*/"
%token<fl>              yVL_TRACE_INIT_TASK       "/*verilator trace_init_task*/"

%token<fl>              yP_TICK         "'"
%token<fl>              yP_TICKBRA      "'{"
%token<fl>              yP_OROR         "||"
%token<fl>              yP_ANDAND       "&&"
%token<fl>              yP_NOR          "~|"
%token<fl>              yP_XNOR         "^~"
%token<fl>              yP_NAND         "~&"
%token<fl>              yP_EQUAL        "=="
%token<fl>              yP_NOTEQUAL     "!="
%token<fl>              yP_CASEEQUAL    "==="
%token<fl>              yP_CASENOTEQUAL "!=="
%token<fl>              yP_WILDEQUAL    "==?"
%token<fl>              yP_WILDNOTEQUAL "!=?"
%token<fl>              yP_GTE          ">="
%token<fl>              yP_LTE          "<="
%token<fl>              yP_LTE__IGNORE  "<=-ignored"    // Used when expr:<= means assignment
%token<fl>              yP_SLEFT        "<<"
%token<fl>              yP_SRIGHT       ">>"
%token<fl>              yP_SSRIGHT      ">>>"
%token<fl>              yP_POW          "**"

%token<fl>              yP_COLON__BEGIN ":-begin"
%token<fl>              yP_COLON__FORK  ":-fork"
%token<fl>              yP_PAR__IGNORE  "(-ignored"     // Used when sequence_expr:expr:( is ignored
%token<fl>              yP_PAR__STRENGTH "(-for-strength"

%token<fl>              yP_LTMINUSGT    "<->"
%token<fl>              yP_PLUSCOLON    "+:"
%token<fl>              yP_MINUSCOLON   "-:"
%token<fl>              yP_MINUSGT      "->"
%token<fl>              yP_MINUSGTGT    "->>"
%token<fl>              yP_EQGT         "=>"
%token<fl>              yP_ASTGT        "*>"
%token<fl>              yP_ANDANDAND    "&&&"
%token<fl>              yP_POUNDPOUND   "##"
%token<fl>              yP_POUNDMINUSPD "#-#"
%token<fl>              yP_POUNDEQPD    "#=#"
%token<fl>              yP_DOTSTAR      ".*"

%token<fl>              yP_ATAT         "@@"
%token<fl>              yP_COLONCOLON   "::"
%token<fl>              yP_COLONEQ      ":="
%token<fl>              yP_COLONDIV     ":/"
%token<fl>              yP_ORMINUSGT    "|->"
%token<fl>              yP_OREQGT       "|=>"
%token<fl>              yP_BRASTAR      "[*"
%token<fl>              yP_BRAEQ        "[="
%token<fl>              yP_BRAMINUSGT   "[->"
%token<fl>              yP_BRAPLUSKET   "[+]"

%token<fl>              yP_PLUSPLUS     "++"
%token<fl>              yP_MINUSMINUS   "--"
%token<fl>              yP_PLUSEQ       "+="
%token<fl>              yP_MINUSEQ      "-="
%token<fl>              yP_TIMESEQ      "*="
%token<fl>              yP_DIVEQ        "/="
%token<fl>              yP_MODEQ        "%="
%token<fl>              yP_ANDEQ        "&="
%token<fl>              yP_OREQ         "|="
%token<fl>              yP_XOREQ        "^="
%token<fl>              yP_SLEFTEQ      "<<="
%token<fl>              yP_SRIGHTEQ     ">>="
%token<fl>              yP_SSRIGHTEQ    ">>>="

// [* is not an operator, as "[ * ]" is legal
// [= and [-> could be repitition operators, but to match [* we don't add them.
// '( is not an operator, as "' (" is legal

//********************
// Verilog op precedence
//UNSUP %token<fl>      prUNARYARITH
//UNSUP %token<fl>      prREDUCTION
//UNSUP %token<fl>      prNEGATION
//UNSUP %token<fl>      prEVENTBEGIN
%token<fl>      prTAGGED

// These prevent other conflicts
%left           yP_ANDANDAND
%left           yMATCHES
//UNSUP %left   prTAGGED
//UNSUP %left   prSEQ_CLOCKING

// PSL op precedence

// Lowest precedence
// These are in IEEE 17.7.1
%nonassoc       yALWAYS yS_ALWAYS yEVENTUALLY yS_EVENTUALLY yACCEPT_ON yREJECT_ON ySYNC_ACCEPT_ON ySYNC_REJECT_ON

%right          yP_ORMINUSGT yP_OREQGT yP_POUNDMINUSPD yP_POUNDEQPD
%right          yUNTIL yS_UNTIL yUNTIL_WITH yS_UNTIL_WITH yIMPLIES
%right          yIFF
%left           yOR
%left           yAND
%nonassoc       yNOT yNEXTTIME yS_NEXTTIME
%left           yINTERSECT
%left           yWITHIN
%right          yTHROUGHOUT
%left           prPOUNDPOUND_MULTI
%left           yP_POUNDPOUND
%left           yP_BRASTAR yP_BRAEQ yP_BRAMINUSGT yP_BRAPLUSKET

// Not specified, but needed higher than yOR, lower than normal non-pexpr expressions
//UNSUP %left           yPOSEDGE yNEGEDGE yEDGE

//UNSUP %left           '{' '}'

// Verilog op precedence
%right          yP_MINUSGT yP_LTMINUSGT
%right          '?' ':' yP_COLON__BEGIN yP_COLON__FORK
%left           yP_OROR
%left           yP_ANDAND
%left           '|' yP_NOR
%left           '^' yP_XNOR
%left           '&' yP_NAND
%left           yP_EQUAL yP_NOTEQUAL yP_CASEEQUAL yP_CASENOTEQUAL yP_WILDEQUAL yP_WILDNOTEQUAL
%left           '>' '<' yP_GTE yP_LTE yP_LTE__IGNORE yINSIDE yDIST
%left           yP_SLEFT yP_SRIGHT yP_SSRIGHT
%left           '+' '-'
%left           '*' '/' '%'
%left           yP_POW
%left           prUNARYARITH yP_MINUSMINUS yP_PLUSPLUS prREDUCTION prNEGATION
%left           '.'
// Not in IEEE, but need to avoid conflicts; TICK should bind tightly just lower than COLONCOLON
%left           yP_TICK
//%left         '(' ')' '[' ']' yP_COLONCOLON '.'

%nonassoc prLOWER_THAN_ELSE
%nonassoc yELSE

//BISONPRE_TYPES
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion

%start source_text

%%
//**********************************************************************
// Files

source_text:                    // ==IEEE: source_text
                /* empty */                             { }
        //                      // timeunits_declaration moved into description:package_item
        |       descriptionList                         { }
        ;

descriptionList:                // IEEE: part of source_text
                description                             { }
        |       descriptionList description             { }
        ;

description:                    // ==IEEE: description
                module_declaration                      { }
        //                      // udp_declaration moved into module_declaration
        |       interface_declaration                   { }
        |       program_declaration                     { }
        |       package_declaration                     { }
        |       package_item                            { if ($1) PARSEP->unitPackage($1->fileline())->addStmtsp($1); }
        |       bind_directive                          { if ($1) PARSEP->unitPackage($1->fileline())->addStmtsp($1); }
        //UNSUP config_declaration                      { }
        //                      // Verilator only
        |       yaT_RESETALL                            { }  // Else, under design, and illegal based on IEEE 22.3
        |       yaT_NOUNCONNECTED                       { PARSEP->unconnectedDrive(VOptionBool::OPT_DEFAULT_FALSE); }
        |       yaT_UNCONNECTED_PULL0                   { PARSEP->unconnectedDrive(VOptionBool::OPT_FALSE); }
        |       yaT_UNCONNECTED_PULL1                   { PARSEP->unconnectedDrive(VOptionBool::OPT_TRUE); }
        |       vltItem                                 { }
        |       error                                   { }
        ;

timeunits_declaration<nodep>:   // ==IEEE: timeunits_declaration
                yTIMEUNIT yaTIMENUM ';'
                        { PARSEP->timescaleMod($<fl>2, SYMP->findTopNodeModule($<fl>1, false), true, $2, false, 0);
                          $$ = nullptr; }
        |       yTIMEUNIT yaTIMENUM '/' yaTIMENUM ';'
                        { PARSEP->timescaleMod($<fl>2, SYMP->findTopNodeModule($<fl>1, false), true, $2, true, $4);
                          $$ = nullptr; }
        |       yTIMEPRECISION yaTIMENUM ';'
                        { PARSEP->timescaleMod($<fl>2, SYMP->findTopNodeModule($<fl>1, false), false, 0, true, $2);
                          $$ = nullptr; }
        ;

//**********************************************************************
// Packages

package_declaration:            // ==IEEE: package_declaration
                packageFront package_itemListE yENDPACKAGE endLabelE
                        { $1->modTrace(GRAMMARP->allTracingOn($1->fileline()));  // Stash for implicit wires, etc
                          if ($2) $1->addStmtsp($2);
                          SYMP->popScope($1);
                          GRAMMARP->endLabel($<fl>4, $1, $4); }
        ;

packageFront<nodeModulep>:
                yPACKAGE lifetimeE idAny ';'
                        { $$ = new AstPackage{$<fl>3, *$3};
                          if ($$->name() == "std") {
                              if ($$->fileline()->filename() != V3Options::getStdPackagePath()) {
                                  $$->v3error("Redeclaring the 'std' package is not allowed");
                              } else {
                                  PARSEP->rootp()->stdPackagep(VN_AS($$, Package));
                              }
                          }
                          $$->inLibrary(true);  // packages are always libraries; don't want to make them a "top"
                          $$->lifetime($2);
                          $$->modTrace(GRAMMARP->allTracingOn($$->fileline()));
                          $$->timeunit(PARSEP->timeLastUnit());
                          PARSEP->rootp()->addModulesp($$);
                          SYMP->pushNew($$); }
        ;

package_itemListE<nodep>:       // IEEE: [{ package_item }]
                /* empty */                             { $$ = nullptr; }
        |       package_itemList                        { $$ = $1; }
        ;

package_itemList<nodep>:        // IEEE: { package_item }
                package_item                            { $$ = $1; }
        |       package_itemList package_item           { $$ = addNextNull($1, $2); }
        ;

package_item<nodep>:            // ==IEEE: package_item
                package_or_generate_item_declaration    { $$ = $1; }
        |       anonymous_program                       { $$ = $1; }
        |       package_export_declaration              { $$ = $1; }
        |       timeunits_declaration                   { $$ = $1; }
        |       sigAttrScope                            { $$ = nullptr; }
        ;

package_or_generate_item_declaration<nodep>:    // ==IEEE: package_or_generate_item_declaration
                net_declaration                         { $$ = $1; }
        |       data_declaration                        { $$ = $1; }
        |       task_declaration                        { $$ = $1; }
        |       function_declaration                    { $$ = $1; }
        |       checker_declaration                     { $$ = $1; }
        |       dpi_import_export                       { $$ = $1; }
        |       extern_constraint_declaration           { $$ = $1; }
        |       class_declaration                       { $$ = $1; }
        //                      // class_constructor_declaration is part of function_declaration
        //                      // local_parameter_declaration under parameter_declaration
        |       parameter_declaration ';'               { $$ = $1; }
        |       covergroup_declaration                  { $$ = $1; }
        |       assertion_item_declaration              { $$ = $1; }
        |       ';'                                     { $$ = nullptr; }
        ;

package_import_declarationList<nodep>:
                package_import_declaration              { $$ = $1; }
        |       package_import_declarationList package_import_declaration
                        { $$ = addNextNull($1, $2); }
        ;

package_import_declaration<nodep>:      // ==IEEE: package_import_declaration
                yIMPORT package_import_itemList ';'     { $$ = $2; }
        ;

package_import_itemList<nodep>:
                package_import_item                     { $$ = $1; }
        |       package_import_itemList ',' package_import_item { $$ = addNextNull($1, $3); }
        ;

package_import_item<nodep>:     // ==IEEE: package_import_item
                idCC/*package_identifier*/ yP_COLONCOLON package_import_itemObj
                        {
                          if (!VN_IS($<scp>1, Package)) {
                              $$ = nullptr;
                              $<fl>1->v3error("Importing from missing package '" << *$<strp>1 << "'");
                          } else {
                              $$ = new AstPackageImport{$<fl>2, VN_CAST($<scp>1, Package), *$3};
                              SYMP->importItem($<scp>1, *$3);
                          } }
        ;

package_import_itemObj<strp>:   // IEEE: part of package_import_item
                idAny/*package_identifier*/             { $<fl>$ = $<fl>1; $$ = $1; }
        |       '*'                                     { $<fl>$ = $<fl>1; static string star = "*"; $$ = &star; }
        ;

package_export_declaration<nodep>: // IEEE: package_export_declaration
                yEXPORT '*' yP_COLONCOLON '*' ';'
                        { $$ = new AstPackageExportStarStar{$<fl>2}; SYMP->exportStarStar(); }
        |       yEXPORT package_export_itemList ';'     { $$ = $2; }
        ;

package_export_itemList<nodep>:
                package_export_item                     { $$ = $1; }
        |       package_export_itemList ',' package_export_item { $$ = addNextNull($1, $3); }
        ;

package_export_item<nodep>:     // ==IEEE: package_export_item
                idCC yP_COLONCOLON package_import_itemObj
                        { $$ = new AstPackageExport{$<fl>3, VN_CAST($<scp>1, Package), *$3};
                          if ($<scp>1) SYMP->exportItem($<scp>1, *$3); }
        ;

//**********************************************************************
// Module headers

module_declaration:             // ==IEEE: module_declaration
        //                      // timeunits_declaration instead in module_item
        //                      // IEEE: module_nonansi_header + module_ansi_header
                modFront importsAndParametersE portsStarE ';'
        /*cont*/    module_itemListE yENDMODULE endLabelE
                        { $1->modTrace(GRAMMARP->allTracingOn($1->fileline()));  // Stash for implicit wires, etc
                          if ($2) $1->addStmtsp($2);
                          if ($3) $1->addStmtsp($3);
                          if ($5) $1->addStmtsp($5);
                          SYMP->popScope($1);
                          GRAMMARP->endLabel($<fl>7, $1, $7); }
        |       udpFront portsStarE ';'
        /*cont*/    module_itemListE yENDPRIMITIVE endLabelE
                        { $1->modTrace(false);  // Stash for implicit wires, etc
                          if ($2) $1->addStmtsp($2);
                          if ($4) $1->addStmtsp($4);
                          GRAMMARP->m_tracingParse = true;
                          SYMP->popScope($1);
                          GRAMMARP->endLabel($<fl>6, $1, $6); }
        //
        |       yEXTERN modFront parameter_port_listE portsStarE ';'
                        { BBUNSUP($<fl>1, "Unsupported: extern module"); }
        ;

modFront<nodeModulep>:
        //                      // General note: all *Front functions must call symPushNew before
        //                      // any formal arguments, as the arguments must land in the new scope.
                yMODULE lifetimeE idAny
                        { $$ = new AstModule{$<fl>3, *$3};
                          $$->lifetime($2);
                          $$->inLibrary(PARSEP->inLibrary() || $$->fileline()->celldefineOn());
                          $$->modTrace(GRAMMARP->allTracingOn($$->fileline()));
                          $$->timeunit(PARSEP->timeLastUnit());
                          $$->unconnectedDrive(PARSEP->unconnectedDrive());
                          PARSEP->rootp()->addModulesp($$);
                          SYMP->pushNew($$); }
        |       modFront sigAttrScope                   { $$ = $1; }
        ;

importsAndParametersE<nodep>:   // IEEE: common part of module_declaration, interface_declaration, program_declaration
        //                      // { package_import_declaration } [ parameter_port_list ]
                parameter_port_listE                    { $$ = $1; }
        |       package_import_declarationList parameter_port_listE     { $$ = addNextNull($1, $2); }
        ;

udpFront<nodeModulep>:
                yPRIMITIVE lifetimeE idAny
                        { $$ = new AstPrimitive{$<fl>3, *$3};
                          $$->inLibrary(true);
                          $$->lifetime($2);
                          $$->modTrace(false);
                          $$->addStmtsp(new AstPragma{$<fl>3, VPragmaType::INLINE_MODULE});
                          GRAMMARP->m_tracingParse = false;
                          PARSEP->rootp()->addModulesp($$);
                          SYMP->pushNew($$); }
        ;

parameter_value_assignmentE<pinp>:      // IEEE: [ parameter_value_assignment ]
                /* empty */                             { $$ = nullptr; }
        |       parameter_value_assignment              { $$ = $1; }
        ;

parameter_value_assignment<pinp>:       // IEEE: parameter_value_assignment
                '#' '(' cellparamListE ')'              { $$ = $3; }
        //                      // Parentheses are optional around a single parameter
        |       '#' yaINTNUM                            { $$ = new AstPin{$<fl>2, 1, "", new AstConst{$<fl>2, *$2}}; }
        |       '#' yaFLOATNUM                          { $$ = new AstPin{$<fl>2, 1, "",
                                                                          new AstConst{$<fl>2, AstConst::RealDouble{}, $2}}; }
        |       '#' timeNumAdjusted                     { $$ = new AstPin{$<fl>2, 1, "", $2}; }
        |       '#' idClassSel                          { $$ = new AstPin{$<fl>2, 1, "", $2}; }
        //                      // Not needed in Verilator:
        //                      // Side effect of combining *_instantiations
        //                      // '#' delay_value      { UNSUP }
        ;

parameter_value_assignmentClass<pinp>:  // IEEE: [ parameter_value_assignment ] (for classes)
        //                      // Like parameter_value_assignment, but for classes only, which always have #()
                '#' '(' cellparamListE ')'              { $$ = $3; }
        ;

parameter_port_listE<nodep>:    // IEEE: parameter_port_list + empty == parameter_value_assignment
                /* empty */                             { $$ = nullptr; }
        |       '#' '(' ')'                             { $$ = nullptr;
                                                          SYMP->findTopNodeModule($<fl>1)->hasParameterList(true); }
        //                      // IEEE: '#' '(' list_of_param_assignments { ',' parameter_port_declaration } ')'
        //                      // IEEE: '#' '(' parameter_port_declaration { ',' parameter_port_declaration } ')'
        //                      // Can't just do that as "," conflicts with between vars and between stmts, so
        //                      // split into pre-comma and post-comma parts
        |       '#' '('                                 { VARRESET_LIST(GPARAM);
                                                          SYMP->findTopNodeModule($<fl>1)->hasParameterList(true);
                                                          GRAMMARP->m_pinAnsi = true; }
        /*cont*/    paramPortDeclOrArgList ')'          { $$ = $4;
                                                          VARRESET_NONLIST(UNKNOWN);
                                                          GRAMMARP->m_pinAnsi = false; }
        //                      // Note legal to start with "a=b" with no parameter statement
        ;

paramPortDeclOrArgList<nodep>:  // IEEE: list_of_param_assignments + { parameter_port_declaration }
                paramPortDeclOrArg                              { $$ = $1; }
        |       paramPortDeclOrArgList ',' paramPortDeclOrArg   { $$ = $1->addNext($3); }
        |       paramPortDeclOrArgList sigAttrScope             { $$ = $1; }
        ;

paramPortDeclOrArg<nodep>:      // IEEE: param_assignment + parameter_port_declaration
        //                      // We combine the two as we can't tell which follows a comma
                paramPortDeclOrArgSub                   { $$ = $1; }
        |       vlTag                                   { $$ = nullptr; }
        ;
paramPortDeclOrArgSub<nodep>:
                parameter_port_declarationFrontE param_assignment       { $$ = $2; }
        |       parameter_port_declarationTypeFrontE type_assignment    { $$ = $2; }
        |       sigAttrScope paramPortDeclOrArgSub                      { $$ = $2; }
        ;

portsStarE<nodep>:              // IEEE: .* + list_of_ports + list_of_port_declarations + empty
                /* empty */                             { $$ = nullptr; }
        |       '(' ')'                                 { $$ = nullptr; }
        //                      // .* expanded from module_declaration
        //UNSUP '(' yP_DOTSTAR ')'                              { UNSUP }
        |       '('                                     { VARRESET_LIST(PORT);
                                                          GRAMMARP->m_pinAnsi = true; }
        /*cont*/    list_of_ports ')'                   { $$ = $3; VARRESET_NONLIST(UNKNOWN);
                                                          GRAMMARP->m_pinAnsi = false; }
        ;

list_of_portsE<nodep>:          // IEEE: list_of_ports + list_of_port_declarations
                portAndTagE                     { $$ = $1; }
        |       list_of_portsE ',' portAndTagE          { $$ = addNextNull($1, $3); }
        ;

list_of_ports<nodep>:           // IEEE: list_of_ports + list_of_port_declarations
                portAndTag                      { $$ = $1; }
        |       list_of_portsE ',' portAndTagE  { $$ = addNextNull($1, $3); }
        ;

portAndTagE<nodep>:
                /* empty */
                        { int p = PINNUMINC();
                          const string name = "__pinNumber" + cvtToStr(p);
                          $$ = new AstPort{CRELINE(), p, name};
                          AstVar* varp = new AstVar{CRELINE(), VVarType::PORT, name, VFlagChildDType{},
                                                    new AstBasicDType{CRELINE(), LOGIC_IMPLICIT}};
                          varp->declDirection(VDirection::INPUT);
                          varp->direction(VDirection::INPUT);
                          varp->ansi(false);
                          varp->declTyped(true);
                          varp->trace(false);
                          $$ = $$->addNext(varp);
                          $$->v3warn(NULLPORT, "Null port on module (perhaps extraneous comma)"); }
        |       portAndTag                              { $$ = $1; }
        |       portAndTag sigAttrScope                 { $$ = $1; }
        ;

portAndTag<nodep>:
                port                                    { $$ = $1; }
        |       vlTag port                              { $$ = $2; }  // Tag will associate with previous port
        |       sigAttrScope portAndTag                 { $$ = $2; }
        ;

port<nodep>:                    // ==IEEE: port
        //                      // SEE ALSO port_declaration, tf_port_declaration,
        //                      // data_declarationVarFront
        //
        //                      // Though not type for interfaces, we factor out the port direction and type
        //                      // so we can handle it in one place
        //
        //                      // IEEE: interface_port_header port_identifier { unpacked_dimension }
        //                      // Expanded interface_port_header
        //                      // We use instantCb here because the non-port form looks just like a module instantiation
                portDirNetE id/*interface*/                      portSig variable_dimensionListE sigAttrListE
                        { $$ = $3; VARDECL(IFACEREF); VARIO(NONE);
                          AstNodeDType* const dtp = new AstIfaceRefDType{$<fl>2, "", *$2};
                          VARDTYPE(dtp);
                          addNextNull($$, VARDONEP($$, $4, $5)); }
        |       portDirNetE id/*interface*/ '.' idAny/*modport*/ portSig variable_dimensionListE sigAttrListE
                        { $$ = $5; VARDECL(IFACEREF); VARIO(NONE);
                          AstNodeDType* const dtp = new AstIfaceRefDType{$<fl>2, $<fl>4, "", *$2, *$4};
                          VARDTYPE(dtp);
                          addNextNull($$, VARDONEP($$, $6, $7)); }
        |       portDirNetE yINTERFACE                           portSig rangeListE sigAttrListE
                        { $$ = nullptr; BBUNSUP($<fl>2, "Unsupported: generic interfaces"); }
        |       portDirNetE yINTERFACE      '.' idAny/*modport*/ portSig rangeListE sigAttrListE
                        { $$ = nullptr; BBUNSUP($<fl>2, "Unsupported: generic interfaces"); }
        //
        |       portDirNetE yINTERCONNECT signingE rangeListE portSig variable_dimensionListE sigAttrListE
                        { $$ = $5;
                          BBUNSUP($<fl>2, "Unsupported: interconnect");
                          AstNodeDType* const dtp = GRAMMARP->addRange(
                                    new AstBasicDType{$2, LOGIC_IMPLICIT, $3}, $4, true);
                          VARDTYPE(dtp);
                          addNextNull($$, VARDONEP($$, $6, $7)); }
        //
        //                      // IEEE: ansi_port_declaration, with [port_direction] removed
        //                      //   IEEE: [ net_port_header | interface_port_header ]
        //                      //         port_identifier { unpacked_dimension } [ '=' constant_expression ]
        //                      //   IEEE: [ net_port_header | variable_port_header ] '.' port_identifier '(' [ expression ] ')'
        //                      //   IEEE: [ variable_port_header ] port_identifier
        //                      //              { variable_dimension } [ '=' constant_expression ]
        //                      //   Substitute net_port_header = [ port_direction ] net_port_type
        //                      //   Substitute variable_port_header = [ port_direction ] variable_port_type
        //                      //   Substitute net_port_type = [ net_type ] data_type_or_implicit
        //                      //   Substitute variable_port_type = var_data_type
        //                      //   Substitute var_data_type = data_type | yVAR data_type_or_implicit
        //                      //     [ [ port_direction ] net_port_type | interface_port_header]
        //                      //              port_identifier { unpacked_dimension }
        //                      //     [ [ port_direction ] var_data_type ]
        //                      //              port_identifier variable_dimensionListE [ '=' constant_expression ]
        //                      //     [ [ port_direction ] net_port_type | [ port_direction ] var_data_type ]
        //                      //              '.' port_identifier '(' [ expression ] ')'
        //
        //                      // Remove optional '[...] id' is in portAssignment
        //                      // Remove optional '[port_direction]' is in port
        //                      //     net_port_type | interface_port_header
        //                      //            port_identifier { unpacked_dimension }
        //                      //     net_port_type | interface_port_header
        //                      //            port_identifier { unpacked_dimension }
        //                      //     var_data_type
        //                      //            port_identifier variable_dimensionListE [ '=' constExpr ]
        //                      //     net_port_type | [ port_direction ] var_data_type '.' port_identifier '(' [ expr ] ')'
        //                      // Expand implicit_type
        //
        //                      // variable_dimensionListE instead of rangeListE to avoid conflicts
        //
        //                      // Note implicit rules looks just line declaring additional followon port
        //                      // No VARDECL("port") for implicit, as we don't want to declare variables for them
        //                      // IEEE: portDirNetE data_type '.' portSig -> handled with AstDot in expr.
        //
        |       portDirNetE data_type           portSig variable_dimensionListE sigAttrListE
                        { $$ = $3; VARDTYPE($2); addNextNull($$, VARDONEP($$, $4, $5)); }
        |       portDirNetE yVAR data_type      portSig variable_dimensionListE sigAttrListE
                        { $$ = $4; VARDTYPE($3); addNextNull($$, VARDONEP($$, $5, $6)); }
        |       portDirNetE yVAR implicit_typeE portSig variable_dimensionListE sigAttrListE
                        { $$ = $4; VARDTYPE($3); addNextNull($$, VARDONEP($$, $5, $6)); }
        |       portDirNetE signing             portSig variable_dimensionListE sigAttrListE
                        { $$ = $3;
                          AstNodeDType* const dtp = new AstBasicDType{$3->fileline(), LOGIC_IMPLICIT, $2};
                          VARDTYPE_NDECL(dtp);
                          addNextNull($$, VARDONEP($$, $4, $5)); }
        |       portDirNetE signingE rangeList  portSig variable_dimensionListE sigAttrListE
                        { $$ = $4;
                          AstNodeDType* const dtp = GRAMMARP->addRange(
                                    new AstBasicDType{$3->fileline(), LOGIC_IMPLICIT, $2}, $3, true);
                          VARDTYPE_NDECL(dtp);
                          addNextNull($$, VARDONEP($$, $5, $6)); }
        |       portDirNetE /*implicit*/        portSig variable_dimensionListE sigAttrListE
                        { $$ = $2; /*VARDTYPE-same*/ addNextNull($$, VARDONEP($$, $3, $4)); }
        //
        |       portDirNetE data_type           portSig variable_dimensionListE sigAttrListE '=' constExpr
                        { $$ = $3; VARDTYPE($2);
                          if (AstVar* vp = VARDONEP($$, $4, $5)) { addNextNull($$, vp); vp->valuep($7); } }
        |       portDirNetE yVAR data_type      portSig variable_dimensionListE sigAttrListE '=' constExpr
                        { $$ = $4; VARDTYPE($3);
                          if (AstVar* vp = VARDONEP($$, $5, $6)) { addNextNull($$, vp); vp->valuep($8); } }
        |       portDirNetE yVAR implicit_typeE portSig variable_dimensionListE sigAttrListE '=' constExpr
                        { $$ = $4; VARDTYPE($3);
                          if (AstVar* vp = VARDONEP($$, $5, $6)) { addNextNull($$, vp); vp->valuep($8); } }
        |       portDirNetE /*implicit*/        portSig variable_dimensionListE sigAttrListE '=' constExpr
                        { $$ = $2; /*VARDTYPE-same*/
                          if (AstVar* vp = VARDONEP($$, $3, $4)) { addNextNull($$, vp); vp->valuep($6); } }
        ;

portDirNetE:                    // IEEE: part of port, optional net type and/or direction
                /* empty */                             { }
        //                      // Per spec, if direction given default the nettype.
        //                      // The higher level rule may override this VARDTYPE with one later in the parse.
        |       port_direction                                  { VARDECL(PORT); VARDTYPE_NDECL(nullptr); }
        |       port_direction { VARDECL(PORT); } net_type      { VARDTYPE_NDECL(nullptr); }  // net_type calls VARDECL
        |       net_type                                        { VARDTYPE_NDECL(nullptr); }  // net_type calls VARDECL
        ;

port_declNetE:                  // IEEE: part of port_declaration, optional net type
                /* empty */                             { }
        |       net_type                                { } // net_type calls VARDECL
        ;

portSig<nodep>:
                id/*port*/
                        { $$ = new AstPort{$<fl>1, PINNUMINC(), *$1}; SYMP->reinsert($$); }
        |       idSVKwd
                        { $$ = new AstPort{$<fl>1, PINNUMINC(), *$1}; SYMP->reinsert($$); }
        ;

//**********************************************************************
// Interface headers

interface_declaration:          // IEEE: interface_declaration + interface_nonansi_header + interface_ansi_header:
        //                      // timeunits_declarationE is instead in interface_item
                intFront importsAndParametersE portsStarE ';'
                        interface_itemListE yENDINTERFACE endLabelE
                        { if ($2) $1->addStmtsp($2);
                          if ($3) $1->addStmtsp($3);
                          if ($5) $1->addStmtsp($5);
                          SYMP->popScope($1); }
        |       yEXTERN intFront parameter_port_listE portsStarE ';'
                        { BBUNSUP($<fl>1, "Unsupported: extern interface"); }
        ;

intFront<nodeModulep>:
                yINTERFACE lifetimeE idAny/*new_interface*/
                        { $$ = new AstIface{$<fl>3, *$3};
                          $$->inLibrary(true);
                          $$->lifetime($2);
                          PARSEP->rootp()->addModulesp($$);
                          SYMP->pushNew($$); }
        |       intFront sigAttrScope                   { $$ = $1; }
        ;

interface_itemListE<nodep>:
                /* empty */                             { $$ = nullptr; }
        |       interface_itemList                      { $$ = $1; }
        ;

interface_itemList<nodep>:
                interface_item                          { $$ = $1; }
        |       interface_itemList interface_item       { $$ = addNextNull($1, $2); }
        ;

interface_item<nodep>:          // IEEE: interface_item + non_port_interface_item
                port_declaration ';'                    { $$ = $1; }
        //                      // IEEE: non_port_interface_item
        //                      // IEEE: generate_region
        |       i_generate_region                       { $$ = $1; }
        |       interface_or_generate_item              { $$ = $1; }
        |       program_declaration
                        { $$ = nullptr; BBUNSUP(CRELINE(), "Unsupported: program decls within interface decls"); }
        //                      // IEEE 1800-2017: modport_item
        //                      // See instead old 2012 position in interface_or_generate_item
        |       interface_declaration
                        { $$ = nullptr; BBUNSUP(CRELINE(), "Unsupported: interface decls within interface decls"); }
        |       timeunits_declaration                   { $$ = $1; }
        //                      // See note in interface_or_generate item
        |       module_common_item                      { $$ = $1; }
        ;

interface_or_generate_item<nodep>:  // ==IEEE: interface_or_generate_item
        //                          // module_common_item in interface_item, as otherwise duplicated
        //                          // with module_or_generate_item's module_common_item
                modport_declaration                     { $$ = $1; }
        |       extern_tf_declaration                   { $$ = $1; }
        ;

//**********************************************************************
// Program headers

anonymous_program<nodep>:       // ==IEEE: anonymous_program
        //                      // See the spec - this doesn't change the scope, items still go up "top"
                yPROGRAM ';' anonymous_program_itemListE yENDPROGRAM
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: Anonymous programs"); }
        ;

anonymous_program_itemListE<nodep>:     // IEEE: { anonymous_program_item }
                /* empty */                             { $$ = nullptr; }
        |       anonymous_program_itemList              { $$ = $1; }
        ;

anonymous_program_itemList<nodep>:      // IEEE: { anonymous_program_item }
                anonymous_program_item                  { $$ = $1; }
        |       anonymous_program_itemList anonymous_program_item       { $$ = addNextNull($1, $2); }
        ;

anonymous_program_item<nodep>:  // ==IEEE: anonymous_program_item
                task_declaration                        { $$ = $1; }
        |       function_declaration                    { $$ = $1; }
        |       class_declaration                       { $$ = $1; }
        |       covergroup_declaration                  { $$ = $1; }
        //                      // class_constructor_declaration is part of function_declaration
        |       ';'                                     { $$ = nullptr; }
        ;

program_declaration:            // IEEE: program_declaration + program_nonansi_header + program_ansi_header:
        //                      // timeunits_declarationE is instead in program_item
                pgmFront parameter_port_listE portsStarE ';'
        /*cont*/    program_itemListE yENDPROGRAM endLabelE
                        { $1->modTrace(GRAMMARP->allTracingOn($1->fileline()));  // Stash for implicit wires, etc
                          if ($2) $1->addStmtsp($2);
                          if ($3) $1->addStmtsp($3);
                          if ($5) $1->addStmtsp($5);
                          SYMP->popScope($1);
                          GRAMMARP->endLabel($<fl>7, $1, $7); }
        |       yEXTERN pgmFront parameter_port_listE portsStarE ';'
                        { BBUNSUP($<fl>1, "Unsupported: extern program");
                          SYMP->popScope($2); }
        ;

pgmFront<nodeModulep>:
                yPROGRAM lifetimeE idAny/*new_program*/
                        { $$ = new AstModule{$<fl>3, *$3, true};
                          $$->lifetime($2);
                          $$->inLibrary(PARSEP->inLibrary() || $$->fileline()->celldefineOn());
                          $$->modTrace(GRAMMARP->allTracingOn($$->fileline()));
                          $$->timeunit(PARSEP->timeLastUnit());
                          PARSEP->rootp()->addModulesp($$);
                          SYMP->pushNew($$); }
        ;

program_itemListE<nodep>:       // ==IEEE: [{ program_item }]
                /* empty */                             { $$ = nullptr; }
        |       program_itemList                        { $$ = $1; }
        ;

program_itemList<nodep>:        // ==IEEE: { program_item }
                program_item                            { $$ = $1; }
        |       program_itemList program_item           { $$ = addNextNull($1, $2); }
        ;

program_item<nodep>:            // ==IEEE: program_item
                port_declaration ';'                    { $$ = $1; }
        |       non_port_program_item                   { $$ = $1; }
        ;

non_port_program_item<nodep>:   // ==IEEE: non_port_program_item
                continuous_assign                       { $$ = $1; }
        |       module_or_generate_item_declaration     { $$ = $1; }
        |       initial_construct                       { $$ = $1; }
        |       final_construct                         { $$ = $1; }
        |       concurrent_assertion_item               { $$ = $1; }
        |       timeunits_declaration                   { $$ = $1; }
        |       program_generate_item                   { $$ = $1; }
        ;

program_generate_item<nodep>:           // ==IEEE: program_generate_item
                loop_generate_construct                 { $$ = $1; }
        |       conditional_generate_construct          { $$ = $1; }
        |       generate_region                         { $$ = $1; }
                                // not in IEEE, but presumed so can do yBEGIN ... yEND
        |       genItemBegin                            { $$ = $1; }
        |       elaboration_system_task                 { $$ = $1; }
        ;

extern_tf_declaration<nodep>:           // ==IEEE: extern_tf_declaration
                yEXTERN task_prototype ';'
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: extern task"); }
        |       yEXTERN function_prototype ';'
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: extern function"); }
        |       yEXTERN yFORKJOIN task_prototype ';'
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: extern forkjoin"); }
        ;

modport_declaration<nodep>:             // ==IEEE: modport_declaration
                yMODPORT modport_itemList ';'           { $$ = $2; }
        ;

modport_itemList<nodep>:                // IEEE: part of modport_declaration
                modport_item                            { $$ = $1; }
        |       modport_itemList ',' modport_item       { $$ = addNextNull($1, $3); }
        ;

modport_item<nodep>:                    // ==IEEE: modport_item
                id/*new-modport*/ '('
        /*mid*/         { VARRESET_NONLIST(UNKNOWN); VARIO(INOUT); }
        /*cont*/    modportPortsDeclList ')'            { $$ = new AstModport{$<fl>1, *$1, $4}; }
        ;

modportPortsDeclList<nodep>:
                modportPortsDecl                            { $$ = $1; }
        |       modportPortsDeclList ',' modportPortsDecl   { $$ = addNextNull($1, $3); }
        ;

// IEEE: modport_ports_declaration  + modport_simple_ports_declaration
//      + (modport_tf_ports_declaration+import_export) + modport_clocking_declaration
// We've expanded the lists each take to instead just have standalone ID ports.
// We track the type as with the V2k series of defines, then create as each ID is seen.
modportPortsDecl<nodep>:
        //                      // IEEE: modport_simple_ports_declaration
                port_direction modportSimplePortOrTFPort { $$ = new AstModportVarRef{$<fl>2, *$2, GRAMMARP->m_varIO};
                                                           GRAMMARP->m_modportImpExpActive = false;}
        //                      // IEEE: modport_clocking_declaration
        |       yCLOCKING idAny/*clocking_identifier*/
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: Modport clocking"); }
        //                      // IEEE: yIMPORT modport_tf_port
        //                      // IEEE: yEXPORT modport_tf_port
        //                      // modport_tf_port expanded here
        |       yIMPORT id/*tf_identifier*/              { $$ = new AstModportFTaskRef{$<fl>2, *$2, false};
                                                           GRAMMARP->m_modportImpExpActive = true;
                                                           GRAMMARP->m_modportImpExpLastIsExport = false; }
        |       yEXPORT id/*tf_identifier*/              { $$ = new AstModportFTaskRef{$<fl>2, *$2, true};
                                                           GRAMMARP->m_modportImpExpActive = true;
                                                           GRAMMARP->m_modportImpExpLastIsExport = true; }
        |       yIMPORT method_prototype
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: Modport import with prototype"); }
        |       yEXPORT method_prototype
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: Modport export with prototype"); }
        // Continuations of above after a comma.
        //                      // IEEE: modport_simple_ports_declaration
        |       modportSimplePortOrTFPort                { $$ = GRAMMARP->m_modportImpExpActive ?
                                                                static_cast<AstNode*>(
                                                                  new AstModportFTaskRef{
                                                                    $<fl>1, *$1, GRAMMARP->m_modportImpExpLastIsExport} ) :
                                                                static_cast<AstNode*>(
                                                                  new AstModportVarRef{
                                                                    $<fl>1, *$1, GRAMMARP->m_varIO} ); }
        ;

modportSimplePortOrTFPort<strp>:// IEEE: modport_simple_port or modport_tf_port, depending what keyword was earlier
                id                                      { $$ = $1; }
        |       '.' idAny '(' ')'                       { $$ = $2; BBUNSUP($<fl>1, "Unsupported: Modport dotted port name"); }
        |       '.' idAny '(' expr ')'                  { $$ = $2; BBUNSUP($<fl>1, "Unsupported: Modport dotted port name"); }
        ;

//************************************************
// Variable Declarations

genvar_declaration<nodep>:      // ==IEEE: genvar_declaration
                yGENVAR list_of_genvar_identifiers ';'  { $$ = $2; }
        ;

list_of_genvar_identifiers<nodep>:      // IEEE: list_of_genvar_identifiers (for declaration)
                genvar_identifierDecl                   { $$ = $1; }
        |       list_of_genvar_identifiers ',' genvar_identifierDecl    { $$ = $1->addNext($3); }
        ;

genvar_identifierDecl<varp>:            // IEEE: genvar_identifier (for declaration)
                id/*new-genvar_identifier*/ sigAttrListE
                        { VARRESET_NONLIST(GENVAR);
                          AstNodeDType* const dtp = new AstBasicDType{$<fl>1, VBasicDTypeKwd::INTEGER};
                          VARDTYPE(dtp);
                          $$ = VARDONEA($<fl>1, *$1, nullptr, $2); }
        ;

parameter_declaration<nodep>:   // IEEE: local_ or parameter_declaration
        //                      // IEEE: yPARAMETER yTYPE list_of_type_assignments ';'
        //                      // Instead of list_of_type_assignments
        //                      // we use list_of_param_assignments because for port handling
        //                      // it already must accept types, so simpler to have code only one place
        //                      // Front must execute first so VARDTYPE is ready before list of vars
                parameter_declarationFront list_of_param_assignments            { $$ = $2; }
        |       parameter_declarationTypeFront list_of_type_assignments         { $$ = $2; }
        ;

parameter_declarationFront:     // IEEE: local_ or parameter_declaration w/o assignment
        //                      // Front must execute first so VARDTYPE is ready before list of vars
                varParamReset implicit_typeE            { /*VARRESET-in-varParam*/ VARDTYPE($2); }
        |       varParamReset data_type                 { /*VARRESET-in-varParam*/ VARDTYPE($2); }
        ;

parameter_declarationTypeFront: // IEEE: local_ or parameter_declaration w/o assignment
        //                      // Front must execute first so VARDTYPE is ready before list of vars
                varParamReset yTYPE__ETC                { /*VARRESET-in-varParam*/ VARDTYPE(new AstParseTypeDType{$2}); }
        ;

parameter_port_declarationFrontE: // IEEE: local_ or parameter_port_declaration w/o assignment
        //                      // IEEE: parameter_declaration (minus assignment)
        //                      // IEEE: local_parameter_declaration (minus assignment)
        //                      // Front must execute first so VARDTYPE is ready before list of vars
                varParamReset implicit_typeE            { /*VARRESET-in-varParam*/ VARDTYPE($2); }
        |       varParamReset data_type                 { /*VARRESET-in-varParam*/ VARDTYPE($2); }
        |       implicit_typeE
                        { /*VARRESET-in-varParam*/
                          // Keep previous type to handle subsequent declarations.
                          // This rule is also used when the previous parameter is a type parameter
                        }
        |       data_type                               { /*VARRESET-in-varParam*/ VARDTYPE($1); }
        ;

parameter_port_declarationTypeFrontE: // IEEE: parameter_port_declaration w/o assignment
        //                      // IEEE: parameter_declaration (minus assignment)
        //                      // IEEE: local_parameter_declaration (minus assignment)
        //                      // Front must execute first so VARDTYPE is ready before list of vars
                varParamReset yTYPE__ETC                { /*VARRESET-in-varParam*/ VARDTYPE(new AstParseTypeDType{$2}); }
        |       yTYPE__ETC                              { /*VARRESET-in-varParam*/ VARDTYPE(new AstParseTypeDType{$1}); }
        ;

net_declaration<nodep>:         // IEEE: net_declaration - excluding implict
                net_declarationFront netSigList ';'
                        { $$ = $2;
                          if (GRAMMARP->m_netStrengthp) {
                              VL_DO_CLEAR(delete GRAMMARP->m_netStrengthp, GRAMMARP->m_netStrengthp = nullptr);
                          }}
        ;

net_declarationFront:           // IEEE: beginning of net_declaration
                net_declRESET net_type driveStrengthE net_scalaredE net_dataTypeE
                        { VARDTYPE_NDECL($5);
                          GRAMMARP->setNetStrength(VN_CAST($3, StrengthSpec));
                        }
        |       net_declRESET yINTERCONNECT signingE rangeListE
                        { BBUNSUP($<fl>2, "Unsupported: interconnect");
                          VARDECL(WIRE);
                          AstNodeDType* const dtp = GRAMMARP->addRange(
                                    new AstBasicDType{$2, LOGIC_IMPLICIT, $3}, $4, true);
                          VARDTYPE_NDECL(dtp); }
        ;

net_declRESET:
                /* empty */                             { VARRESET_NONLIST(UNKNOWN); }
        ;

net_scalaredE:
                /* empty */                             { }
        //                      //UNSUP: ySCALARED/yVECTORED ignored
        |       ySCALARED                               { }
        |       yVECTORED                               { }
        ;

net_dataTypeE<nodeDTypep>:
        //                      // If there's a SV data type there shouldn't be a delay on this wire
        //                      // Otherwise #(...) can't be determined to be a delay or parameters
        //                      // Submit this as a footnote to the committee
                var_data_type                           { $$ = $1; }
        |       signingE rangeList delay_controlE
                        { $$ = GRAMMARP->addRange(new AstBasicDType{$2->fileline(), LOGIC, $1},
                                                                    $2, true);
                          GRAMMARP->setNetDelay($3); }  // not implicit
        |       signing
                        { $$ = new AstBasicDType{$<fl>1, LOGIC, $1}; }  // not implicit
        |       /*implicit*/ delay_controlE
                        { $$ = new AstBasicDType{CRELINE(), LOGIC};
                          GRAMMARP->setNetDelay($1); }  // not implicit
        ;

net_type:                       // ==IEEE: net_type
                ySUPPLY0                                { VARDECL(SUPPLY0); }
        |       ySUPPLY1                                { VARDECL(SUPPLY1); }
        |       yTRI                                    { VARDECL(TRIWIRE); }
        |       yTRI0                                   { VARDECL(TRI0); }
        |       yTRI1                                   { VARDECL(TRI1); }
        |       yTRIAND                                 { VARDECL(WIRE); BBUNSUP($1, "Unsupported: triand"); }
        |       yTRIOR                                  { VARDECL(WIRE); BBUNSUP($1, "Unsupported: trior"); }
        |       yTRIREG                                 { VARDECL(WIRE); BBUNSUP($1, "Unsupported: trireg"); }
        |       yWAND                                   { VARDECL(WIRE); BBUNSUP($1, "Unsupported: wand"); }
        |       yWIRE                                   { VARDECL(WIRE); }
        |       yWOR                                    { VARDECL(WIRE); BBUNSUP($1, "Unsupported: wor"); }
        //                      // VAMS - somewhat hackish
        |       yWREAL                                  { VARDECL(WREAL); }
        ;

varParamReset:
                yPARAMETER                              { VARRESET_NONLIST(GPARAM); }
        |       yLOCALPARAM                             { VARRESET_NONLIST(LPARAM); }
        // Note that the type of these params could be modified later according to context (see V3LinkParse)
        ;

port_direction:                 // ==IEEE: port_direction + tf_port_direction
        //                      // IEEE 19.8 just "input" FIRST forces type to wire - we'll ignore that here
        //                      // Only used for ANSI declarations
                yINPUT                                  { VARIO(INPUT); }
        |       yOUTPUT                                 { VARIO(OUTPUT); }
        |       yINOUT                                  { VARIO(INOUT); }
        |       yREF                                    { VARIO(REF); }
        |       yCONST__REF yREF                        { VARIO(CONSTREF); }
        ;

port_directionReset:            // IEEE: port_direction that starts a port_declaraiton
        //                      // Used only for declarations outside the port list
                yINPUT                                  { VARRESET_NONLIST(UNKNOWN); VARIO(INPUT); }
        |       yOUTPUT                                 { VARRESET_NONLIST(UNKNOWN); VARIO(OUTPUT); }
        |       yINOUT                                  { VARRESET_NONLIST(UNKNOWN); VARIO(INOUT); }
        |       yREF                                    { VARRESET_NONLIST(UNKNOWN); VARIO(REF); }
        |       yCONST__REF yREF                        { VARRESET_NONLIST(UNKNOWN); VARIO(CONSTREF); }
        ;

port_declaration<nodep>:        // ==IEEE: port_declaration
        //                      // Non-ANSI; used inside block followed by ';'
        //                      // SEE ALSO port, tf_port_declaration, data_declarationVarFront
        //
        //                      // IEEE: inout_declaration
        //                      // IEEE: input_declaration
        //                      // IEEE: output_declaration
        //                      // IEEE: ref_declaration
                port_directionReset port_declNetE data_type
        /*mid*/         { VARDTYPE($3); }
        /*cont*/    list_of_variable_decl_assignments                   { $$ = $5; }
        |       port_directionReset port_declNetE yVAR data_type
        /*mid*/         { VARDTYPE($4); }
        /*cont*/    list_of_variable_decl_assignments                   { $$ = $6; }
        |       port_directionReset port_declNetE yVAR implicit_typeE
        /*mid*/         { VARDTYPE($4); }
        /*cont*/    list_of_variable_decl_assignments                   { $$ = $6; }
        |       port_directionReset port_declNetE signingE rangeList
        /*mid*/         { AstNodeDType* const dtp = GRAMMARP->addRange(
                              new AstBasicDType{$4->fileline(), LOGIC_IMPLICIT, $3}, $4, true);
                          VARDTYPE_NDECL(dtp); }
        /*cont*/    list_of_variable_decl_assignments                   { $$ = $6; }
        |       port_directionReset port_declNetE signing
        /*mid*/         { AstNodeDType* const dtp = new AstBasicDType{$<fl>3, LOGIC_IMPLICIT, $3};
                          VARDTYPE_NDECL(dtp); }
        /*cont*/    list_of_variable_decl_assignments                   { $$ = $5; }
        |       port_directionReset port_declNetE /*implicit*/
        /*mid*/         { VARDTYPE_NDECL(nullptr); /*default_nettype*/ }
        /*cont*/    list_of_variable_decl_assignments                   { $$ = $4; }
        //                      // IEEE: interface_declaration
        //                      // Looks just like variable declaration unless has a period
        //                      // See etcInst
        ;

tf_port_declaration<nodep>:     // ==IEEE: tf_port_declaration
        //                      // Used inside function; followed by ';'
        //                      // SEE ALSO port_declaration, port, data_declarationVarFront
        //
                port_directionReset      data_type      { VARDTYPE($2); }  list_of_tf_variable_identifiers ';'  { $$ = $4; }
        |       port_directionReset      implicit_typeE { VARDTYPE_NDECL($2); }  list_of_tf_variable_identifiers ';'    { $$ = $4; }
        |       port_directionReset yVAR data_type      { VARDTYPE($3); }  list_of_tf_variable_identifiers ';'  { $$ = $5; }
        |       port_directionReset yVAR implicit_typeE { VARDTYPE($3); }  list_of_tf_variable_identifiers ';'  { $$ = $5; }
        ;

integer_atom_type<basicDTypep>: // ==IEEE: integer_atom_type
                yBYTE                                   { $$ = new AstBasicDType{$1, VBasicDTypeKwd::BYTE}; }
        |       ySHORTINT                               { $$ = new AstBasicDType{$1, VBasicDTypeKwd::SHORTINT}; }
        |       yINT                                    { $$ = new AstBasicDType{$1, VBasicDTypeKwd::INT}; }
        |       yLONGINT                                { $$ = new AstBasicDType{$1, VBasicDTypeKwd::LONGINT}; }
        |       yINTEGER                                { $$ = new AstBasicDType{$1, VBasicDTypeKwd::INTEGER}; }
        |       yTIME                                   { $$ = new AstBasicDType{$1, VBasicDTypeKwd::TIME}; }
        ;

integer_vector_type<basicDTypep>:       // ==IEEE: integer_atom_type
                yBIT                                    { $$ = new AstBasicDType{$1, VBasicDTypeKwd::BIT}; }
        |       yLOGIC                                  { $$ = new AstBasicDType{$1, VBasicDTypeKwd::LOGIC}; }
        |       yREG                                    { $$ = new AstBasicDType{$1, VBasicDTypeKwd::LOGIC}; } // logic==reg
        ;

non_integer_type<basicDTypep>:  // ==IEEE: non_integer_type
                yREAL                                   { $$ = new AstBasicDType{$1, VBasicDTypeKwd::DOUBLE}; }
        |       yREALTIME                               { $$ = new AstBasicDType{$1, VBasicDTypeKwd::DOUBLE}; }
        |       ySHORTREAL                              { $$ = new AstBasicDType{$1, VBasicDTypeKwd::DOUBLE}; UNSUPREAL($1); }
        ;

signingE<signstate>:            // IEEE: signing - plus empty
                /*empty*/                               { $$ = VSigning::NOSIGN; }
        |       signing                                 { $$ = $1; }
        ;

signing<signstate>:             // ==IEEE: signing
                ySIGNED                                 { $<fl>$ = $<fl>1; $$ = VSigning::SIGNED; }
        |       yUNSIGNED                               { $<fl>$ = $<fl>1; $$ = VSigning::UNSIGNED; }
        ;

//************************************************
// Data Types

simple_type<nodeDTypep>:                // ==IEEE: simple_type
        //                      // IEEE: integer_type
                integer_atom_type                       { $$ = $1; }
        |       integer_vector_type                     { $$ = $1; }
        |       non_integer_type                        { $$ = $1; }
        //                      // IEEE: ps_type_identifier
        //                      // IEEE: ps_parameter_identifier (presumably a PARAMETER TYPE)
        //                      // Even though we looked up the type and have a AstNode* to it,
        //                      // we can't fully resolve it because it may have been just a forward definition.
        |       packageClassScopeE idType
                        { AstRefDType* const refp = new AstRefDType{$<fl>2, *$2, $1, nullptr};
                          $$ = refp; }
        //
        //                      // { generate_block_identifer ... } '.'
        //                      // Need to determine if generate_block_identifier can be lex-detected
        ;

data_type<nodeDTypep>:          // ==IEEE: data_type
        //                      // This expansion also replicated elsewhere, IE data_type__AndID
                data_typeNoRef                          { $$ = $1; }
        //
        //                      // REFERENCES
        //
        //                      // IEEE: [ class_scope | package_scope ] type_identifier { packed_dimension }
        //                      // IEEE: class_type
        //                      // IEEE: ps_covergroup_identifier
        //                      // Don't distinguish between types and classes so all these combined
        |       packageClassScopeE idType packed_dimensionListE
                        { AstRefDType* const refp = new AstRefDType{$<fl>2, *$2, $1, nullptr};
                          $$ = GRAMMARP->createArray(refp, $3, true); }
        |       packageClassScopeE idType parameter_value_assignmentClass packed_dimensionListE
                        { AstRefDType* const refp = new AstRefDType{$<fl>2, *$2, $1, $3};
                          $$ = GRAMMARP->createArray(refp, $4, true); }
        ;

data_typeBasic<nodeDTypep>:             // IEEE: part of data_type
                integer_vector_type signingE rangeListE { $1->setSignedState($2); $$ = GRAMMARP->addRange($1, $3, true); }
        |       integer_atom_type signingE              { $1->setSignedState($2); $$ = $1; }
        |       non_integer_type                        { $$ = $1; }
        ;

data_typeNoRef<nodeDTypep>:             // ==IEEE: data_type, excluding class_type etc references
                data_typeBasic                          { $$ = $1; }
        |       struct_unionDecl packed_dimensionListE
                        { $$ = GRAMMARP->createArray(
                                   new AstDefImplicitDType{$1->fileline(),
                                                           "__typeimpsu" + cvtToStr(GRAMMARP->s_modTypeImpNum++),
                                                           SYMP, VFlagChildDType{}, $1}, $2, true); }
        |       enumDecl
                        { $$ = new AstDefImplicitDType{$1->fileline(),
                                                       "__typeimpenum" + cvtToStr(GRAMMARP->s_modTypeImpNum++),
                                                       SYMP, VFlagChildDType{}, $1}; }
        |       ySTRING
                        { $$ = new AstBasicDType{$1, VBasicDTypeKwd::STRING}; }
        |       yCHANDLE
                        { $$ = new AstBasicDType{$1, VBasicDTypeKwd::CHANDLE}; }
        |       yEVENT
                        { $$ = new AstBasicDType{$1, VBasicDTypeKwd::EVENT}; v3Global.setHasEvents(); }
        |       type_referenceDecl                      { $$ = $1; }
        //                      // IEEE: class_scope: see data_type above
        //                      // IEEE: class_type: see data_type above
        //                      // IEEE: ps_covergroup: see data_type above
        //                      // Rules overlap virtual_interface_declaration
        |       yVIRTUAL__INTERFACE yINTERFACE data_typeVirtual
                        { $$ = $3; }
        |       yVIRTUAL__anyID                data_typeVirtual
                        { $$ = $2; }
        ;

data_typeVirtual<nodeDTypep>:           // ==IEEE: data_type after yVIRTUAL [ yINTERFACE ]
        //                      // Parameters here are SV2009
                id/*interface*/                         { $$ = new AstIfaceRefDType{$<fl>1, "", *$1}; }
        |       id/*interface*/ '.' id/*modport*/       { $$ = new AstIfaceRefDType{$<fl>1, $<fl>3, "", *$1, *$3}; }
        |       id/*interface*/ parameter_value_assignmentClass
                        { $$ = new AstIfaceRefDType{$<fl>1, nullptr, "", *$1, "", $2}; }
        |       id/*interface*/ parameter_value_assignmentClass '.' id/*modport*/
                        { $$ = new AstIfaceRefDType{$<fl>1, $<fl>4, "", *$1, *$4, $2}; }
        ;

data_type_or_void<nodeDTypep>:  // ==IEEE: data_type_or_void
                data_type                               { $$ = $1; }
        |       yVOID
                        { $$ = new AstBasicDType{$1, LOGIC_IMPLICIT};
                          BBUNSUP($1, "Unsupported: void (for tagged unions)"); }
        ;

var_data_type<nodeDTypep>:              // ==IEEE: var_data_type
                data_type                               { $$ = $1; }
        |       yVAR data_type                          { $$ = $2; }
        |       yVAR implicit_typeE                     { $$ = $2; }
        ;

type_referenceBoth<nodeExprp>:          // IEEE: type_reference
                yTYPE__ETC '(' exprOrDataType ')'
                        { $$ = new AstAttrOf{$1, VAttrType::TYPEID, $3}; }
        ;

type_referenceDecl<nodeDTypep>:         // IEEE: type_reference (as a data type for declaration)
                yTYPE__ETC '(' exprOrDataType ')'
                        { $$ = new AstRefDType{$1, AstRefDType::FlagTypeOfExpr{}, $3}; }
        ;

type_referenceEq<nodeExprp>:            // IEEE: type_reference (as an ==/!== expression)
                yTYPE__EQ '(' exprOrDataType ')'
                        { $$ = new AstAttrOf{$1, VAttrType::TYPEID, $3}; }
        ;

struct_unionDecl<nodeUOrStructDTypep>:  // IEEE: part of data_type
        //                      // packedSigningE is NOP for unpacked
                ySTRUCT        packedSigningE '{'
        /*mid*/         { $<nodeUOrStructDTypep>$ = new AstStructDType{$1, $2}; SYMP->pushNew($<nodeUOrStructDTypep>$); }
        /*cont*/    struct_union_memberList '}'
                        { $$ = $<nodeUOrStructDTypep>4; $$->addMembersp($5); SYMP->popScope($$); }
        |       yUNION taggedE packedSigningE '{'
        /*mid*/         { $<nodeUOrStructDTypep>$ = new AstUnionDType{$1, $3}; SYMP->pushNew($<nodeUOrStructDTypep>$); }
        /*cont*/    struct_union_memberList '}'
                        { $$ = $<nodeUOrStructDTypep>5; $$->addMembersp($6); SYMP->popScope($$); }
        ;

struct_union_memberList<memberDTypep>: // IEEE: { struct_union_member }
                struct_union_member                             { $$ = $1; }

        |       struct_union_memberList struct_union_member     { $$ = addNextNull($1, $2); }
        ;

struct_union_member<memberDTypep>:     // ==IEEE: struct_union_member
        //                      // UNSUP random_qualifer not propagagted until have randomize support
                random_qualifierE data_type_or_void
        /*mid*/         { GRAMMARP->m_memDTypep = $2; }  // As a list follows, need to attach this dtype to each member.
        /*cont*/    list_of_member_decl_assignments ';'
                        { $$ = $4; DEL(GRAMMARP->m_memDTypep); GRAMMARP->m_memDTypep = nullptr; }
        |       vlTag                                   { $$ = nullptr; }
        ;

list_of_member_decl_assignments<memberDTypep>: // Derived from IEEE: list_of_variable_decl_assignments
                member_decl_assignment                  { $$ = $1; }
        |       list_of_member_decl_assignments ',' member_decl_assignment      { $$ = addNextNull($1, $3); }
        ;

member_decl_assignment<memberDTypep>:   // Derived from IEEE: variable_decl_assignment
        //                      // At present we allow only packed structures/unions.
        //                      // So this is different from variable_decl_assignment
                id variable_dimensionListE
                        { $$ = new AstMemberDType{$<fl>1, *$1, VFlagChildDType{},
                                                  GRAMMARP->createArray((GRAMMARP->m_memDTypep
                                                                         ? GRAMMARP->m_memDTypep->cloneTree(true) : nullptr),
                                                                        $2, false),
                                                  nullptr};
                          PARSEP->tagNodep($$);
                        }
        |       id variable_dimensionListE '=' variable_declExpr
                        { $$ = new AstMemberDType{$<fl>1, *$1, VFlagChildDType{},
                                                  GRAMMARP->createArray((GRAMMARP->m_memDTypep
                                                                         ? GRAMMARP->m_memDTypep->cloneTree(true) : nullptr),
                                                                        $2, false),
                                                  $4};
                          PARSEP->tagNodep($$);
                        }
        |       idSVKwd                                 { $$ = nullptr; }
        //
        //                      // IEEE: "dynamic_array_variable_identifier '[' ']' [ '=' dynamic_array_new ]"
        //                      // Matches above with variable_dimensionE = "[]"
        //                      // IEEE: "class_variable_identifier [ '=' class_new ]"
        //                      // variable_dimensionE must be empty
        //                      // Pushed into variable_declExpr:dynamic_array_new
        //
        //                      // IEEE: "[ covergroup_variable_identifier ] '=' class_new
        //                      // Pushed into variable_declExpr:class_new
        |       '=' class_new
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: member declaration assignment with new()"); }
        ;

list_of_variable_decl_assignments<varp>:        // ==IEEE: list_of_variable_decl_assignments
                variable_decl_assignment                { $$ = $1; }
        |       list_of_variable_decl_assignments ',' variable_decl_assignment  { $$ = addNextNull($1, $3); }
        ;

variable_decl_assignment<varp>: // ==IEEE: variable_decl_assignment
                id variable_dimensionListE sigAttrListE
                        { $$ = VARDONEA($<fl>1, *$1, $2, $3); }
        |       id variable_dimensionListE sigAttrListE '=' variable_declExpr
                        { $$ = VARDONEA($<fl>1, *$1, $2, $3); $$->valuep($5); }
        |       idSVKwd                                 { $$ = nullptr; }
        //
        //                      // IEEE: "dynamic_array_variable_identifier '[' ']' [ '=' dynamic_array_new ]"
        //                      // Matches above with variable_dimensionE = "[]"
        //                      // IEEE: "class_variable_identifier [ '=' class_new ]"
        //                      // variable_dimensionE must be empty
        //                      // Pushed into variable_declExpr:dynamic_array_new
        //
        //                      // IEEE: "[ covergroup_variable_identifier ] '=' class_new
        //                      // Pushed into variable_declExpr:class_new
        |       '=' class_new
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: declaration assignment with new()"); }
        ;

list_of_tf_variable_identifiers<nodep>: // ==IEEE: list_of_tf_variable_identifiers
                tf_variable_identifier                  { $$ = $1; }
        |       list_of_tf_variable_identifiers ',' tf_variable_identifier      { $$ = $1->addNext($3); }
        ;

tf_variable_identifier<varp>:           // IEEE: part of list_of_tf_variable_identifiers
                id variable_dimensionListE sigAttrListE exprEqE
                        { $$ = VARDONEA($<fl>1, *$1, $2, $3);
                          if ($4) AstNode::addNext<AstNode, AstNode>(
                                      $$, new AstAssign{$4->fileline(), new AstParseRef{$<fl>1, VParseRefExp::PX_TEXT, *$1}, $4}); }
        ;

variable_declExpr<nodep>:               // IEEE: part of variable_decl_assignment - rhs of expr
                expr                                    { $$ = $1; }
        |       dynamic_array_new                       { $$ = $1; }
        |       class_new                               { $$ = $1; }
        ;

variable_dimensionListE<nodeRangep>:    // IEEE: variable_dimension + empty
                /*empty*/                               { $$ = nullptr; }
        |       variable_dimensionList                  { $$ = $1; }
        ;

variable_dimensionList<nodeRangep>:     // IEEE: variable_dimension + empty
                variable_dimension                      { $$ = $1; }
        |       variable_dimensionList variable_dimension       { $$ = $1->addNext($2); }
        ;

variable_dimension<nodeRangep>: // ==IEEE: variable_dimension
        //                      // IEEE: unsized_dimension
                '[' ']'                                 { $$ = new AstUnsizedRange{$1}; }
        //                      // IEEE: unpacked_dimension
        |       anyrange                                { $$ = $1; }
        //                      // IEEE: unpacked_dimension (if const_expr)
        //                      // IEEE: associative_dimension (if data_type)
        //                      // Can't tell which until see if expr is data type or not
        |       '[' exprOrDataType ']'                  { $$ = new AstBracketRange{$1, $2}; }
        |       yP_BRASTAR ']'                          { $$ = new AstWildcardRange{$1}; }
        |       '[' '*' ']'                             { $$ = new AstWildcardRange{$1}; }
        //                      // IEEE: queue_dimension
        //                      // '[' '$' ']' -- $ is part of expr, see '[' constExpr ']'
        //                      // '[' '$' ':' expr ']' -- anyrange:expr:$
        ;

random_qualifierE<qualifiers>:  // IEEE: random_qualifier + empty
                /*empty*/                               { $$ = VMemberQualifiers::none(); }
        |       random_qualifier                        { $$ = $1; }
        ;

random_qualifier<qualifiers>:   // ==IEEE: random_qualifier
                yRAND                                   { $$ = VMemberQualifiers::none(); $$.m_rand = true; }
        |       yRANDC                                  { $$ = VMemberQualifiers::none(); $$.m_randc = true; }
        ;

taggedE:
                /*empty*/                               { }
        //UNSUP yTAGGED                                 { UNSUP }
        ;

packedSigningE<signstate>:
        //                      // VSigning::NOSIGN overloaded to indicate not packed
                /*empty*/                               { $$ = VSigning::NOSIGN; }
        |       yPACKED signingE                        { $$ = $2; if ($$ == VSigning::NOSIGN) $$ = VSigning::UNSIGNED; }
        ;

//************************************************
// enum

// IEEE: part of data_type
enumDecl<nodeDTypep>:
                yENUM enum_base_typeE '{' enum_nameList '}'
                        { $$ = new AstEnumDType{$1, VFlagChildDType{}, $2, $4}; }
        ;

enum_base_typeE<nodeDTypep>:    // IEEE: enum_base_type
                /* empty */
                        { $$ = new AstBasicDType{CRELINE(), VBasicDTypeKwd::INT}; }
        //                      // Not in spec, but obviously "enum [1:0]" should work
        //                      // implicit_type expanded, without empty
        //                      // Note enum base types are always packed data types
        |       signingE rangeList
                        { $$ = GRAMMARP->addRange(new AstBasicDType{$2->fileline(), LOGIC_IMPLICIT, $1}, $2, true); }
        |       signing
                        { $$ = new AstBasicDType{$<fl>1, LOGIC_IMPLICIT, $1}; }
        //
        |       integer_atom_type signingE
                        { $1->setSignedState($2); $$ = $1; }
        |       integer_vector_type signingE rangeListE
                        { $1->setSignedState($2); $$ = GRAMMARP->addRange($1, $3, true); }
        //                      // below can be idAny or yaID__aTYPE
        //                      // IEEE requires a type, though no shift conflict if idAny
        //                      // IEEE: type_identifier [ packed_dimension ]
        //                      // however other simulators allow [ class_scope | package_scope ] type_identifier
        |       idAny rangeListE
                        { $$ = GRAMMARP->createArray(new AstRefDType{$<fl>1, *$1}, $2, true); }
        |       packageClassScope idAny rangeListE
                        { AstRefDType* refp = new AstRefDType{$<fl>2, *$2, $1, nullptr};
                          $$ = GRAMMARP->createArray(refp, $3, true); }
        ;

enum_nameList<enumItemp>:
                enum_name_declaration                   { $$ = $1; }
        |       enum_nameList ',' enum_name_declaration { $$ = addNextNull($1, $3); }
        ;

enum_name_declaration<enumItemp>:   // ==IEEE: enum_name_declaration
                idAny/*enum_identifier*/ enumNameRangeE enumNameStartE
                        { $$ = new AstEnumItem{$<fl>1, *$1, $2, $3}; }
        ;

enumNameRangeE<rangep>:          // IEEE: second part of enum_name_declaration
                /* empty */
                        { $$ = nullptr; }
        |       '[' intnumAsConst ']'
                        { $$ = new AstRange{$1, new AstConst{$1, 0}, new AstConst($1, $2->toSInt() - 1)}; }
        |       '[' intnumAsConst ':' intnumAsConst ']'
                        { $$ = new AstRange{$1, $2, $4}; }
        ;

enumNameStartE<nodeExprp>:      // IEEE: third part of enum_name_declaration
                /* empty */                             { $$ = nullptr; }
        |       '=' constExpr                           { $$ = $2; }
        ;

intnumAsConst<constp>:
                yaINTNUM                                { $$ = new AstConst{$<fl>1, *$1}; }
        ;

//************************************************
// Typedef

data_declaration<nodep>:        // ==IEEE: data_declaration
        //                      // VARRESET can't be called here - conflicts
                data_declarationVar                     { $$ = $1; }
        |       type_declaration                        { $$ = $1; }
        |       package_import_declaration              { $$ = $1; }
        //                      // IEEE: virtual_interface_declaration
        //                      // "yVIRTUAL yID yID" looks just like a data_declaration
        //                      // Therefore the virtual_interface_declaration term isn't used
        //                      // 1800-2009:
        |       net_type_declaration                    { $$ = $1; }
        |       vlTag                                   { $$ = nullptr; }
        ;

class_property<nodep>:          // ==IEEE: class_property, which is {property_qualifier} data_declaration
                memberQualListE data_declarationVarClass                { $$ = $2; $1.applyToNodes($2); }
        //                      // UNSUP: Import needs to apply local/protected from memberQualList, and error on others
        |       memberQualListE type_declaration                        { $$ = $2; }
        //                      // UNSUP: Import needs to apply local/protected from memberQualList, and error on others
        |       memberQualListE package_import_declaration              { $$ = $2; }
        //                      // IEEE: virtual_interface_declaration
        //                      // "yVIRTUAL yID yID" looks just like a data_declaration
        //                      // Therefore the virtual_interface_declaration term isn't used
        ;

data_declarationVar<varp>:      // IEEE: part of data_declaration
        //                      // The first declaration has complications between assuming what's
        //                      // the type vs ID declaring
                data_declarationVarFront list_of_variable_decl_assignments ';'  { $$ = $2; }
        ;

data_declarationVarClass<varp>: // IEEE: part of data_declaration (for class_property)
        //                      // The first declaration has complications between assuming what's
        //                      // the type vs ID declaring
                data_declarationVarFrontClass list_of_variable_decl_assignments ';'     { $$ = $2; }
        ;

data_declarationVarFront:       // IEEE: part of data_declaration
        //                      // Non-ANSI; used inside block followed by ';'
        //                      // SEE ALSO port_declaration, tf_port_declaration, port
        //
        //                      // Expanded: "constE yVAR lifetimeE data_type"
        //                      // implicit_type expanded into /*empty*/ or "signingE rangeList"
                yVAR lifetimeE data_type
                        { VARRESET_NONLIST(VAR); VARLIFE($2); VARDTYPE($3); }
        |       yVAR lifetimeE
                        { VARRESET_NONLIST(VAR); VARLIFE($2);
                          AstNodeDType* const dtp = new AstBasicDType{$<fl>1, LOGIC_IMPLICIT};
                          VARDTYPE(dtp); }
        |       yVAR lifetimeE signingE rangeList
                        { /*VARRESET-in-ddVar*/ VARLIFE($2);
                          AstNodeDType* const dtp = GRAMMARP->addRange(
                              new AstBasicDType{$<fl>1, LOGIC_IMPLICIT, $3}, $4, true);
                          VARDTYPE(dtp); }
        //
        //                      // implicit_type expanded into /*empty*/ or "signingE rangeList"
        |       yCONST__ETC yVAR lifetimeE data_type
                        { VARRESET_NONLIST(VAR); VARLIFE($3);
                          AstNodeDType* const dtp = new AstConstDType{$<fl>2, VFlagChildDType{}, $4};
                          VARDTYPE(dtp); }
        |       yCONST__ETC yVAR lifetimeE
                        { VARRESET_NONLIST(VAR); VARLIFE($3);
                          AstNodeDType* const dtp = new AstConstDType{$<fl>2, VFlagChildDType{},
                                                          new AstBasicDType{$<fl>2, LOGIC_IMPLICIT}};
                          VARDTYPE(dtp); }
        |       yCONST__ETC yVAR lifetimeE signingE rangeList
                        { VARRESET_NONLIST(VAR); VARLIFE($3);
                          AstNodeDType* const dtp = new AstConstDType{$<fl>2, VFlagChildDType{},
                                  GRAMMARP->addRange(new AstBasicDType{$<fl>2, LOGIC_IMPLICIT, $4}, $5, true)};
                          VARDTYPE(dtp); }
        //
        //                      // Expanded: "constE lifetimeE data_type"
        |       /**/                  data_type
                        { VARRESET_NONLIST(VAR); VARDTYPE($1); }
        |       /**/        lifetime  data_type
                        { VARRESET_NONLIST(VAR); VARLIFE($1); VARDTYPE($2); }
        |       yCONST__ETC lifetimeE data_type
                        { VARRESET_NONLIST(VAR); VARLIFE($2);
                          AstNodeDType* const dtp = new AstConstDType{$<fl>1, VFlagChildDType{}, $3};
                          VARDTYPE(dtp); }
        //                      // = class_new is in variable_decl_assignment
        ;

data_declarationVarFrontClass:  // IEEE: part of data_declaration (for class_property)
        //                      // VARRESET called before this rule
        //                      // yCONST is removed, added to memberQual rules
        //                      // implicit_type expanded into /*empty*/ or "signingE rangeList"
                yVAR lifetimeE data_type        { VARRESET_NONLIST(VAR); VARLIFE($2); VARDTYPE($3); }
        |       yVAR lifetimeE                  { VARRESET_NONLIST(VAR); VARLIFE($2); }
        |       yVAR lifetimeE signingE rangeList
                        { /*VARRESET-in-ddVar*/
                          AstNodeDType* const dtp = GRAMMARP->addRange(new AstBasicDType{$<fl>1, LOGIC_IMPLICIT, $3}, $4, true);
                          VARDTYPE(dtp);
                          VARLIFE($2); }
        //
        //                      // Expanded: "constE lifetimeE data_type"
        |       data_type                       { VARRESET_NONLIST(VAR); VARDTYPE($1); }
        //                      // lifetime is removed, added to memberQual rules to avoid conflict
        //                      // yCONST is removed, added to memberQual rules to avoid conflict
        //                      // = class_new is in variable_decl_assignment
        ;

net_type_declaration<nodep>:  // IEEE: net_type_declaration
                yNETTYPE data_type idAny/*net_type_identifier*/ ';'
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: nettype"); }
        //                      // package_scope part of data_type
        |       yNETTYPE data_type idAny yWITH__ETC packageClassScopeE id/*tf_identifier*/ ';'
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: nettype"); }
        |       yNETTYPE packageClassScopeE id/*net_type_identifier*/ idAny/*net_type_identifier*/ ';'
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: nettype"); }
        |       yNETTYPE packageClassScopeE id/*net_type_identifier*/ idAny/*net_type_identifier*/
        /*cont*/   yWITH__ETC packageClassScopeE id/*tf_identifier*/ ';'
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: nettype"); }
        ;

implicit_typeE<nodeDTypep>:             // IEEE: part of *data_type_or_implicit
        //                      // Also expanded in data_declaration
                /* empty */
                        { $$ = nullptr; }
        |       signingE rangeList
                        { $$ = GRAMMARP->addRange(new AstBasicDType{$2->fileline(), LOGIC_IMPLICIT, $1}, $2, true); }
        |       signing
                        { $$ = new AstBasicDType{$<fl>1, LOGIC_IMPLICIT, $1}; }
        ;

assertion_variable_declaration<nodep>:  // IEEE: assertion_variable_declaration
        //                      // IEEE: var_data_type expanded
                var_data_type                        { VARRESET_NONLIST(VAR); VARDTYPE_NDECL($1); }
        /*cont*/    list_of_variable_decl_assignments ';'     { $$ = $3; }
        ;

type_declaration<nodep>:        // ==IEEE: type_declaration
                                // Data_type expanded
                yTYPEDEF data_typeNoRef
        /*cont*/    idAny variable_dimensionListE dtypeAttrListE ';'
                        { AstNodeDType* const dtp = $2;
                          $$ = GRAMMARP->createTypedef($<fl>3, *$3, $5, dtp, $4); }
        |       yTYPEDEF packageClassScope idType packed_dimensionListE
        /*cont*/    idAny variable_dimensionListE dtypeAttrListE ';'
                        { AstRefDType* const refp = new AstRefDType{$<fl>3, *$3, $2, nullptr};
                          AstNodeDType* const dtp = GRAMMARP->createArray(refp, $4, true);
                          $$ = GRAMMARP->createTypedef($<fl>5, *$5, $7, dtp, $6); }
        |       yTYPEDEF packageClassScope idType parameter_value_assignmentClass packed_dimensionListE
        /*cont*/    idAny variable_dimensionListE dtypeAttrListE ';'
                        { AstRefDType* const refp = new AstRefDType{$<fl>3, *$3, $2, $4};
                          AstNodeDType* const dtp = GRAMMARP->createArray(refp, $5, true);
                          $$ = GRAMMARP->createTypedef($<fl>6, *$6, $8, dtp, $7); }
        |       yTYPEDEF idType packed_dimensionListE
        /*cont*/    idAny variable_dimensionListE dtypeAttrListE ';'
                        { AstRefDType* const refp = new AstRefDType{$<fl>2, *$2, nullptr, nullptr};
                          AstNodeDType* const dtp = GRAMMARP->createArray(refp, $3, true);
                          $$ = GRAMMARP->createTypedef($<fl>4, *$4, $6, dtp, $5); }
        |       yTYPEDEF idType parameter_value_assignmentClass packed_dimensionListE
        /*cont*/    idAny variable_dimensionListE dtypeAttrListE ';'
                        { AstRefDType* const refp = new AstRefDType{$<fl>2, *$2, nullptr, $3};
                          AstNodeDType* const dtp = GRAMMARP->createArray(refp, $4, true);
                          $$ = GRAMMARP->createTypedef($<fl>5, *$5, $7, dtp, $6); }
        //                      //
        |       yTYPEDEF id/*interface*/ '.' idAny/*type*/ idAny/*type*/ dtypeAttrListE ';'
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: SystemVerilog 2005 typedef in this context"); }
        //                      // Allow redeclaring same typedef again
        //                      // Alternative is use of idAny below, but this will cause conflicts with ablve
        |       yTYPEDEF idType ';'                     { $$ = GRAMMARP->createTypedefFwd($<fl>2, *$2); }
        //                      // Combines into above "data_type id" rule
        //                      // Verilator: Not important what it is in the AST, just need
        //                      // to make sure the yaID__aTYPE gets returned
        |       yTYPEDEF id ';'                         { $$ = GRAMMARP->createTypedefFwd($<fl>2, *$2); }
        |       yTYPEDEF yENUM idAny ';'                { $$ = GRAMMARP->createTypedefFwd($<fl>3, *$3); }
        |       yTYPEDEF ySTRUCT idAny ';'              { $$ = GRAMMARP->createTypedefFwd($<fl>3, *$3); }
        |       yTYPEDEF yUNION idAny ';'               { $$ = GRAMMARP->createTypedefFwd($<fl>3, *$3); }
        |       yTYPEDEF yCLASS idAny ';'               { $$ = GRAMMARP->createTypedefFwd($<fl>3, *$3); }
        |       yTYPEDEF yINTERFACE yCLASS idAny ';'    { $$ = GRAMMARP->createTypedefFwd($<fl>4, *$4); }
        ;

dtypeAttrListE<nodep>:
                /* empty */                             { $$ = nullptr; }
        |       dtypeAttrList                           { $$ = $1; }
        ;

dtypeAttrList<nodep>:
                dtypeAttr                               { $$ = $1; }
        |       dtypeAttrList dtypeAttr                 { $$ = addNextNull($1, $2); }
        ;

dtypeAttr<nodep>:
                yVL_PUBLIC                              { $$ = new AstAttrOf{$1, VAttrType::DT_PUBLIC}; }
        ;

vlTag:                          // verilator tag handling
                yVL_TAG                                 { if (PARSEP->tagNodep()) PARSEP->tagNodep()->tag(*$1); }
        ;

//************************************************
// Module Items

module_itemListE<nodep>:        // IEEE: Part of module_declaration
                /* empty */                             { $$ = nullptr; }
        |       module_itemList                         { $$ = $1; }
        ;

module_itemList<nodep>:         // IEEE: Part of module_declaration
                module_item                             { $$ = $1; }
        |       module_itemList module_item             { $$ = addNextNull($1, $2); }
        ;

module_item<nodep>:             // ==IEEE: module_item
                port_declaration ';'                    { $$ = $1; }
        |       non_port_module_item                    { $$ = $1; }
        ;

non_port_module_item<nodep>:    // ==IEEE: non_port_module_item
                generate_region                         { $$ = $1; }
                                // not in IEEE, but presumed so can do yBEGIN ... yEND
        |       genItemBegin                            { $$ = $1; }
        |       module_or_generate_item                 { $$ = $1; }
        |       specify_block                           { $$ = $1; }
        |       specparam_declaration                   { $$ = $1; }
        |       program_declaration
                        { $$ = nullptr; BBUNSUP(CRELINE(), "Unsupported: program decls within module decls"); }
        |       module_declaration
                        { $$ = nullptr; BBUNSUP(CRELINE(), "Unsupported: module decls within module decls"); }
        |       interface_declaration
                        { $$ = nullptr; BBUNSUP(CRELINE(), "Unsupported: interface decls within module decls"); }
        |       timeunits_declaration                   { $$ = $1; }
        //                      // Verilator specific
        |       yaSCHDR                                 { $$ = new AstScHdr{$<fl>1, *$1}; v3Global.setHasSCTextSections(); }
        |       yaSCINT                                 { $$ = new AstScInt{$<fl>1, *$1}; v3Global.setHasSCTextSections(); }
        |       yaSCIMP                                 { $$ = new AstScImp{$<fl>1, *$1}; v3Global.setHasSCTextSections(); }
        |       yaSCIMPH                                { $$ = new AstScImpHdr{$<fl>1, *$1}; v3Global.setHasSCTextSections(); }
        |       yaSCCTOR                                { $$ = new AstScCtor{$<fl>1, *$1}; v3Global.setHasSCTextSections(); }
        |       yaSCDTOR                                { $$ = new AstScDtor{$<fl>1, *$1}; v3Global.setHasSCTextSections(); }
        |       yVL_HIER_BLOCK                          { $$ = new AstPragma{$1, VPragmaType::HIER_BLOCK}; }
        |       yVL_INLINE_MODULE                       { $$ = new AstPragma{$1, VPragmaType::INLINE_MODULE}; }
        |       yVL_NO_INLINE_MODULE                    { $$ = new AstPragma{$1, VPragmaType::NO_INLINE_MODULE}; }
        |       yVL_PUBLIC_MODULE                       { $$ = new AstPragma{$1, VPragmaType::PUBLIC_MODULE}; v3Global.dpi(true); }
        ;

module_or_generate_item<nodep>: // ==IEEE: module_or_generate_item
        //                      // IEEE: parameter_override
                yDEFPARAM list_of_defparam_assignments ';'      { $$ = $2; }
        //                      // IEEE: gate_instantiation + udp_instantiation + module_instantiation
        //                      // not here, see etcInst in module_common_item
        //                      // We joined udp & module definitions, so this goes here
        |       combinational_body                      { $$ = $1; }
        //                      // This module_common_item shared with
        //                      // interface_or_generate_item:module_common_item
        |       module_common_item                      { $$ = $1; }
        ;

module_common_item<nodep>:      // ==IEEE: module_common_item
                module_or_generate_item_declaration     { $$ = $1; }
        //                      // IEEE: interface_instantiation
        //                      // + IEEE: program_instantiation
        //                      // + module_instantiation from module_or_generate_item
        |       etcInst                                 { $$ = $1; }
        |       assertion_item                          { $$ = $1; }
        |       bind_directive                          { $$ = $1; }
        |       continuous_assign                       { $$ = $1; }
        //                      // IEEE: net_alias
        |       yALIAS variable_lvalue aliasEqList ';'
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: alias statements"); }
        |       initial_construct                       { $$ = $1; }
        |       final_construct                         { $$ = $1; }
        |       always_construct                        { $$ = $1; }
        |       loop_generate_construct                 { $$ = $1; }
        |       conditional_generate_construct          { $$ = $1; }
        |       elaboration_system_task                 { $$ = $1; }
        |       sigAttrScope                            { $$ = nullptr; }
        //
        |       error ';'                               { $$ = nullptr; }
        ;

always_construct<nodep>:        // IEEE: == always_construct
        //                      // Verilator only - event_control attached to always
                yALWAYS       stmtBlock                 { $$ = new AstAlways{$1, VAlwaysKwd::ALWAYS, nullptr, $2}; }
        |       yALWAYS_FF    stmtBlock                 { $$ = new AstAlways{$1, VAlwaysKwd::ALWAYS_FF, nullptr, $2}; }
        |       yALWAYS_LATCH stmtBlock                 { $$ = new AstAlways{$1, VAlwaysKwd::ALWAYS_LATCH, nullptr, $2}; }
        |       yALWAYS_COMB  stmtBlock                 { $$ = new AstAlways{$1, VAlwaysKwd::ALWAYS_COMB, nullptr, $2}; }
        ;

continuous_assign<nodep>:       // IEEE: continuous_assign
                yASSIGN driveStrengthE delay_controlE assignList ';'
                {
                    $$ = $4;
                    STRENGTH_LIST($4, $2, AssignW);
                    DELAY_LIST($3, $4);
                }
        ;

initial_construct<nodep>:       // IEEE: initial_construct
                yINITIAL stmtBlock                      { $$ = new AstInitial{$1, $2}; }
        ;

final_construct<nodep>:         // IEEE: final_construct
                yFINAL stmtBlock                        { $$ = new AstFinal{$1, $2}; }
        ;

module_or_generate_item_declaration<nodep>:     // ==IEEE: module_or_generate_item_declaration
                package_or_generate_item_declaration    { $$ = $1; }
        |       genvar_declaration                      { $$ = $1; }
        |       clocking_declaration                    { $$ = $1; }
        |       yDEFAULT yCLOCKING idAny/*new-clocking_identifier*/ ';'
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: default clocking identifier"); }
        |       yDEFAULT yDISABLE yIFF expr/*expression_or_dist*/ ';'
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: default disable iff"); }
        ;

aliasEqList:                    // IEEE: part of net_alias
                '=' variable_lvalue                     { }
        |       aliasEqList '=' variable_lvalue         { }
        ;

bind_directive<nodep>:          // ==IEEE: bind_directive + bind_target_scope
        //                      // ';' - Note IEEE grammar is wrong, includes extra ';'
        //                      // - it's already in module_instantiation
        //                      // We merged the rules - id may be a bind_target_instance or
        //                      // module_identifier or interface_identifier
                yBIND bind_target_instance bind_instantiation   { $$ = new AstBind{$<fl>2, *$2, $3}; }
        |       yBIND bind_target_instance ':' bind_target_instance_list bind_instantiation
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: Bind with instance list"); }
        ;

bind_target_instance_list:      // ==IEEE: bind_target_instance_list
                bind_target_instance                    { }
        |       bind_target_instance_list ',' bind_target_instance      { }
        ;

bind_target_instance<strp>:     // ==IEEE: bind_target_instance
        //UNSUP hierarchical_identifierBit              { }
                idAny                                   { $$ = $1; }
        ;

bind_instantiation<nodep>:      // ==IEEE: bind_instantiation
        //                      // IEEE: program_instantiation
        //                      // IEEE: + module_instantiation
        //                      // IEEE: + interface_instantiation
        //                      // Need to get an AstBind instead of AstCell, so have special rules
                instDecl                                { $$ = $1; }
        ;

//************************************************
// Generates
//
// Way down in generate_item is speced a difference between module,
// interface and checker generates.  modules and interfaces are almost
// identical (minus DEFPARAMs) so we overlap them.  Checkers are too
// different, so we copy all rules for checkers.

generate_region<nodep>:         // ==IEEE: generate_region
                yGENERATE ~c~genItemList yENDGENERATE   { $$ = $2; }
        |       yGENERATE yENDGENERATE                  { $$ = nullptr; }
        ;

c_generate_region<nodep>:  // IEEE: generate_region (for checkers)
                BISONPRE_COPY(generate_region,{s/~c~/c_/g})     // {copied}
        ;

i_generate_region<nodep>:  // IEEE: generate_region (for interface)
                BISONPRE_COPY(generate_region,{s/~c~/i_/g})     // {copied}
        ;

generate_block_or_null<nodep>:  // IEEE: generate_block_or_null (called from gencase/genif/genfor)
        //      ';'             // is included in
        //                      // IEEE: generate_block
        //                      // Must always return a BEGIN node, or nullptr - see GenFor construction
                ~c~generate_item
                        { $$ = $1 ? (new AstBegin{$1->fileline(), "", $1, true, true}) : nullptr; }
        |       ~c~genItemBegin                         { $$ = $1; }
        ;

c_generate_block_or_null<nodep>:  // IEEE: generate_block_or_null (for checkers)
                BISONPRE_COPY(generate_block_or_null,{s/~c~/c_/g})      // {copied}
        ;

genItemBegin<nodep>:            // IEEE: part of generate_block
                yBEGIN ~c~genItemList yEND              { $$ = new AstBegin{$1, "", $2, true, false}; }
        |       yBEGIN yEND                             { $$ = nullptr; }
        |       id yP_COLON__BEGIN yBEGIN ~c~genItemList yEND endLabelE
                        { $$ = new AstBegin{$<fl>1, *$1, $4, true, false};
                          GRAMMARP->endLabel($<fl>6, *$1, $6); }
        |       id yP_COLON__BEGIN yBEGIN yEND endLabelE
                        { $$ = new AstBegin{$<fl>1, *$1, nullptr, true, false};
                          GRAMMARP->endLabel($<fl>5, *$1, $5); }
        |       yBEGIN ':' idAny ~c~genItemList yEND endLabelE
                        { $$ = new AstBegin{$<fl>3, *$3, $4, true, false};
                          GRAMMARP->endLabel($<fl>6, *$3, $6); }
        |       yBEGIN ':' idAny yEND endLabelE
                        { $$ = new AstBegin{$<fl>3, *$3, nullptr, true, false};
                          GRAMMARP->endLabel($<fl>5, *$3, $5); }
        ;

c_genItemBegin<nodep>:  // IEEE: part of generate_block (for checkers)
                BISONPRE_COPY(genItemBegin,{s/~c~/c_/g})                // {copied}
        ;

i_genItemBegin<nodep>:  // IEEE: part of generate_block (for interfaces)
                BISONPRE_COPY(genItemBegin,{s/~c~/i_/g})                // {copied}
        ;

genItemOrBegin<nodep>:          // Not in IEEE, but our begin isn't under generate_item
                ~c~generate_item                        { $$ = $1; }
        |       ~c~genItemBegin                         { $$ = $1; }
        ;

c_genItemOrBegin<nodep>:  // (for checkers)
                BISONPRE_COPY(genItemOrBegin,{s/~c~/c_/g})      // {copied}
        ;

i_genItemOrBegin<nodep>:  // (for interfaces)
                interface_item                          { $$ = $1; }
        |       i_genItemBegin                          { $$ = $1; }
        ;

genItemList<nodep>:
                ~c~genItemOrBegin                       { $$ = $1; }
        |       ~c~genItemList ~c~genItemOrBegin        { $$ = addNextNull($1, $2); }
        ;

c_genItemList<nodep>:  // (for checkers)
                BISONPRE_COPY(genItemList,{s/~c~/c_/g})         // {copied}
        ;

i_genItemList<nodep>:  // (for interfaces)
                BISONPRE_COPY(genItemList,{s/~c~/i_/g})         // {copied}
        ;

generate_item<nodep>:           // IEEE: module_or_interface_or_generate_item
        //                      // Only legal when in a generate under a module (or interface under a module)
                module_or_generate_item                 { $$ = $1; }
        //                      // Only legal when in a generate under an interface
        //UNSUP interface_or_generate_item              { $$ = $1; }
        //                      // IEEE: checker_or_generate_item
        //                      // Only legal when in a generate under a checker
        //                      // so below in c_generate_item
        ;

c_generate_item<nodep>:  // IEEE: generate_item (for checkers)
                checker_or_generate_item                { $$ = $1; }
        ;

conditional_generate_construct<nodep>:  // ==IEEE: conditional_generate_construct
                yCASE '(' exprTypeCompare ')' ~c~case_generate_itemListE yENDCASE
                        { $$ = new AstGenCase{$1, $3, $5}; }
        |       yIF '(' exprTypeCompare ')' ~c~generate_block_or_null %prec prLOWER_THAN_ELSE
                        { $$ = new AstGenIf{$1, $3, $5, nullptr}; }
        |       yIF '(' exprTypeCompare ')' ~c~generate_block_or_null yELSE ~c~generate_block_or_null
                        { $$ = new AstGenIf{$1, $3, $5, $7}; }
        ;

c_conditional_generate_construct<nodep>:  // IEEE: conditional_generate_construct (for checkers)
                BISONPRE_COPY(conditional_generate_construct,{s/~c~/c_/g})      // {copied}
        ;

loop_generate_construct<nodep>: // ==IEEE: loop_generate_construct
                yFOR '(' genvar_initialization ';' expr ';' genvar_iteration ')' ~c~generate_block_or_null
                        { // Convert BEGIN(...) to BEGIN(GENFOR(...)), as we need the BEGIN to hide the local genvar
                          AstBegin* lowerBegp = VN_CAST($9, Begin);
                          UASSERT_OBJ(!($9 && !lowerBegp), $9, "Child of GENFOR should have been begin");

                          if (!lowerBegp) lowerBegp = new AstBegin{$1, "", nullptr, true, false};  // Empty body
                          AstNode* const lowerNoBegp = lowerBegp->stmtsp();
                          if (lowerNoBegp) lowerNoBegp->unlinkFrBackWithNext();
                          //
                          AstBegin* const blkp = new AstBegin{$1, lowerBegp->name(), nullptr, true, true};
                          // V3LinkDot detects BEGIN(GENFOR(...)) as a special case
                          AstNode* initp = $3;
                          AstNode* const varp = $3;
                          if (VN_IS(varp, Var)) {  // Genvar
                                initp = varp->nextp();
                                initp->unlinkFrBackWithNext();  // Detach 2nd from varp, make 1st init
                                blkp->addStmtsp(varp);
                          }
                          // Statements are under 'genforp' as cells under this
                          // for loop won't get an extra layer of hierarchy tacked on
                          blkp->genforp(new AstGenFor{$1, initp, $5, $7, lowerNoBegp});
                          $$ = blkp;
                          VL_DO_DANGLING(lowerBegp->deleteTree(), lowerBegp);
                        }
        ;

c_loop_generate_construct<nodep>:  // IEEE: loop_generate_construct (for checkers)
                BISONPRE_COPY(loop_generate_construct,{s/~c~/c_/g})     // {copied}
        ;

genvar_initialization<nodep>:   // ==IEEE: genvar_initialization
                varRefBase '=' expr                     { $$ = new AstAssign{$2, $1, $3}; }
        |       yGENVAR genvar_identifierDecl '=' constExpr
                        { $$ = $2; AstNode::addNext<AstNode, AstNode>($$,
                                       new AstAssign{$3, new AstVarRef{$2->fileline(), $2, VAccess::WRITE}, $4}); }
        ;

genvar_iteration<nodep>:        // ==IEEE: genvar_iteration
                varRefBase '='          expr
                        { $$ = new AstAssign{$2, $1, $3}; }
        |       varRefBase yP_PLUSEQ    expr
                        { $$ = new AstAssign{$2, $1, new AstAdd{$2, $1->cloneTreePure(true), $3}}; }
        |       varRefBase yP_MINUSEQ   expr
                        { $$ = new AstAssign{$2, $1, new AstSub{$2, $1->cloneTreePure(true), $3}}; }
        |       varRefBase yP_TIMESEQ   expr
                        { $$ = new AstAssign{$2, $1, new AstMul{$2, $1->cloneTreePure(true), $3}}; }
        |       varRefBase yP_DIVEQ     expr
                        { $$ = new AstAssign{$2, $1, new AstDiv{$2, $1->cloneTreePure(true), $3}}; }
        |       varRefBase yP_MODEQ     expr
                        { $$ = new AstAssign{$2, $1, new AstModDiv{$2, $1->cloneTreePure(true), $3}}; }
        |       varRefBase yP_ANDEQ     expr
                        { $$ = new AstAssign{$2, $1, new AstAnd{$2, $1->cloneTreePure(true), $3}}; }
        |       varRefBase yP_OREQ      expr
                        { $$ = new AstAssign{$2, $1, new AstOr{$2, $1->cloneTreePure(true), $3}}; }
        |       varRefBase yP_XOREQ     expr
                        { $$ = new AstAssign{$2, $1, new AstXor{$2, $1->cloneTreePure(true), $3}}; }
        |       varRefBase yP_SLEFTEQ   expr
                        { $$ = new AstAssign{$2, $1, new AstShiftL{$2, $1->cloneTreePure(true), $3}}; }
        |       varRefBase yP_SRIGHTEQ  expr
                        { $$ = new AstAssign{$2, $1, new AstShiftR{$2, $1->cloneTreePure(true), $3}}; }
        |       varRefBase yP_SSRIGHTEQ expr
                        { $$ = new AstAssign{$2, $1, new AstShiftRS{$2, $1->cloneTreePure(true), $3}}; }
        //                      // inc_or_dec_operator
        // When support ++ as a real AST type, maybe AstWhile::precondsp() becomes generic AstNodeExprStmt?
        |       yP_PLUSPLUS   varRefBase
                        { $$ = new AstAssign{$1, $2, new AstAdd{$1, $2->cloneTreePure(true),
                                                                new AstConst{$1, AstConst::StringToParse{}, "'b1"}}}; }
        |       yP_MINUSMINUS varRefBase
                        { $$ = new AstAssign{$1, $2, new AstSub{$1, $2->cloneTreePure(true),
                                                                new AstConst{$1, AstConst::StringToParse{}, "'b1"}}}; }
        |       varRefBase yP_PLUSPLUS
                        { $$ = new AstAssign{$2, $1, new AstAdd{$2, $1->cloneTreePure(true),
                                                                new AstConst{$2, AstConst::StringToParse{}, "'b1"}}}; }
        |       varRefBase yP_MINUSMINUS
                        { $$ = new AstAssign{$2, $1, new AstSub{$2, $1->cloneTreePure(true),
                                                                new AstConst{$2, AstConst::StringToParse{}, "'b1"}}}; }
        ;

case_generate_itemListE<caseItemp>: // IEEE: [{ case_generate_itemList }]
                /* empty */                             { $$ = nullptr; }
        |       ~c~case_generate_itemList               { $$ = $1; }
        ;

c_case_generate_itemListE<caseItemp>:  // IEEE: { case_generate_item } (for checkers)
                BISONPRE_COPY(case_generate_itemListE,{s/~c~/c_/g})      // {copied}
        ;

case_generate_itemList<caseItemp>:  // IEEE: { case_generate_itemList }
                ~c~case_generate_item                   { $$ = $1; }
        |       ~c~case_generate_itemList ~c~case_generate_item         { $$ = $1; $1->addNext($2); }
        ;

c_case_generate_itemList<caseItemp>:  // IEEE: { case_generate_item } (for checkers)
                BISONPRE_COPY(case_generate_itemList,{s/~c~/c_/g})      // {copied}
        ;

case_generate_item<caseItemp>:      // ==IEEE: case_generate_item
                caseCondList colon ~c~generate_block_or_null    { $$ = new AstCaseItem{$2, $1, $3}; }
        |       yDEFAULT colon ~c~generate_block_or_null        { $$ = new AstCaseItem{$1, nullptr, $3}; }
        |       yDEFAULT ~c~generate_block_or_null              { $$ = new AstCaseItem{$1, nullptr, $2}; }
        ;

c_case_generate_item<caseItemp>:  // IEEE: case_generate_item (for checkers)
                BISONPRE_COPY(case_generate_item,{s/~c~/c_/g})  // {copied}
        ;

//************************************************
// Assignments and register declarations

assignList<nodep>:
                assignOne                               { $$ = $1; }
        |       assignList ',' assignOne                { $$ = $1->addNext($3); }
        ;

assignOne<nodep>:
                variable_lvalue '=' expr                { $$ = new AstAssignW{$2, $1, $3}; }
        ;

delay_or_event_controlE<nodep>:  // IEEE: delay_or_event_control plus empty
                /* empty */                             { $$ = nullptr; }
        |        delay_control                          { $$ = $1; }
        |        event_control                          { $$ = $1; }
        |        yREPEAT '(' expr ')' event_control
                        { $$ = $5; BBUNSUP($1, "Unsupported: repeat event control"); }
        ;

delay_controlE<delayp>:
                /* empty */                             { $$ = nullptr; }
        |       delay_control                           { $$ = $1; }
        ;

delay_control<delayp>:   //== IEEE: delay_control
                '#' delay_value
                        { $$ = new AstDelay{$<fl>1, $2, false}; }
        |       '#' '(' minTypMax ')'
                        { $$ = new AstDelay{$<fl>1, $3, false}; }
        |       '#' '(' minTypMax ',' minTypMax ')'
                        { $$ = new AstDelay{$<fl>1, $3, false}; RISEFALLDLYUNSUP($3); DEL($5); }
        |       '#' '(' minTypMax ',' minTypMax ',' minTypMax ')'
                        { $$ = new AstDelay{$<fl>1, $5, false}; RISEFALLDLYUNSUP($5); DEL($3); DEL($7); }
        ;

delay_value<nodeExprp>:         // ==IEEE:delay_value
        //                      // IEEE: ps_identifier
                packageClassScopeE varRefBase           { $$ = AstDot::newIfPkg($<fl>2, $1, $2); }
        |       yaINTNUM                                { $$ = new AstConst{$<fl>1, *$1}; }
        |       yaFLOATNUM                              { $$ = new AstConst{$<fl>1, AstConst::RealDouble{}, $1}; }
        |       timeNumAdjusted                         { $$ = $1; }
        ;

delayExpr<nodeExprp>:
                expr                                    { $$ = $1; }
        ;

minTypMax<nodeExprp>:           // IEEE: mintypmax_expression and constant_mintypmax_expression
                delayExpr                               { $$ = $1; }
        |       delayExpr ':' delayExpr ':' delayExpr   { $$ = $3; MINTYPMAXDLYUNSUP($3); DEL($1); DEL($5); }
        ;

netSigList<varp>:               // IEEE: list_of_port_identifiers
                netSig                                  { $$ = $1; }
        |       netSigList ',' netSig                   { $$ = $1; $1->addNext($3); }
        ;

netSig<varp>:                   // IEEE: net_decl_assignment -  one element from list_of_port_identifiers
                netId sigAttrListE
                        { $$ = VARDONEA($<fl>1, *$1, nullptr, $2); }
        |       netId sigAttrListE '=' expr
                        { $$ = VARDONEA($<fl>1, *$1, nullptr, $2);
                          auto* const assignp = new AstAssignW{$3, new AstParseRef{$<fl>1, VParseRefExp::PX_TEXT, *$1}, $4};
                          if (GRAMMARP->m_netStrengthp) assignp->strengthSpecp(GRAMMARP->m_netStrengthp->cloneTree(false));
                          AstNode::addNext<AstNode, AstNode>($$, assignp); }
        |       netId variable_dimensionList sigAttrListE
                        { $$ = VARDONEA($<fl>1, *$1, $2, $3); }
        ;

netId<strp>:
                id/*new-net*/                           { $$ = $1; $<fl>$ = $<fl>1; }
        |       idSVKwd                                 { $$ = $1; $<fl>$ = $<fl>1; }
        ;

sigAttrScope:
                yVL_PUBLIC_FLAT_RW_ON_SNS attr_event_control
                                                        { AstNode* sigAttrsp = new AstAttrOf{$1, VAttrType::VAR_PUBLIC_FLAT_RW};
                                                          sigAttrsp->addNext(new AstAlwaysPublic{$1, $2, nullptr});
                                                          GRAMMARP->setScopedSigAttr(sigAttrsp);
                                                          v3Global.dpi(true); }
        |       yVL_PUBLIC_ON                           { GRAMMARP->createScopedSigAttr(VAttrType::VAR_PUBLIC); }
        |       yVL_PUBLIC_FLAT_ON                      { GRAMMARP->createScopedSigAttr(VAttrType::VAR_PUBLIC_FLAT); }
        |       yVL_PUBLIC_FLAT_RD_ON                   { GRAMMARP->createScopedSigAttr(VAttrType::VAR_PUBLIC_FLAT_RD); }
        |       yVL_PUBLIC_FLAT_RW_ON                   { GRAMMARP->createScopedSigAttr(VAttrType::VAR_PUBLIC_FLAT_RW); }
        |       yVL_PUBLIC_OFF                          { GRAMMARP->setScopedSigAttr(nullptr); }
        ;

sigAttrListE<nodep>: // Scoped Attributes are added to explicit attributes
                /* empty */                             { $$ = nullptr; }
        |       sigAttrList                             { $$ = $1; }
        ;

sigAttrList<nodep>:
                sigAttr                                 { $$ = $1; }
        |       sigAttrList sigAttr                     { $$ = addNextNull($1, $2); }
        ;

sigAttr<nodep>:
                yVL_CLOCKER                             { $$ = new AstAttrOf{$1, VAttrType::VAR_CLOCKER}; }
        |       yVL_NO_CLOCKER                          { $$ = new AstAttrOf{$1, VAttrType::VAR_NO_CLOCKER}; }
        |       yVL_CLOCK_ENABLE                        { $$ = new AstAttrOf{$1, VAttrType::VAR_CLOCK_ENABLE}; }
        |       yVL_FORCEABLE                           { $$ = new AstAttrOf{$1, VAttrType::VAR_FORCEABLE}; }
        |       yVL_PUBLIC                              { $$ = new AstAttrOf{$1, VAttrType::VAR_PUBLIC}; v3Global.dpi(true); }
        |       yVL_PUBLIC_FLAT                         { $$ = new AstAttrOf{$1, VAttrType::VAR_PUBLIC_FLAT}; v3Global.dpi(true); }
        |       yVL_PUBLIC_FLAT_RD                      { $$ = new AstAttrOf{$1, VAttrType::VAR_PUBLIC_FLAT_RD}; v3Global.dpi(true); }
        |       yVL_PUBLIC_FLAT_RW                      { $$ = new AstAttrOf{$1, VAttrType::VAR_PUBLIC_FLAT_RW}; v3Global.dpi(true); }
        |       yVL_PUBLIC_FLAT_RW attr_event_control   { $$ = new AstAttrOf{$1, VAttrType::VAR_PUBLIC_FLAT_RW}; v3Global.dpi(true);
                                                          $$ = $$->addNext(new AstAlwaysPublic{$1, $2, nullptr}); }
        |       yVL_ISOLATE_ASSIGNMENTS                 { $$ = new AstAttrOf{$1, VAttrType::VAR_ISOLATE_ASSIGNMENTS}; }
        |       yVL_SC_BV                               { $$ = new AstAttrOf{$1, VAttrType::VAR_SC_BV}; }
        |       yVL_SFORMAT                             { $$ = new AstAttrOf{$1, VAttrType::VAR_SFORMAT}; }
        |       yVL_SPLIT_VAR                           { $$ = new AstAttrOf{$1, VAttrType::VAR_SPLIT_VAR}; }
        ;

rangeListE<nodeRangep>:         // IEEE: [{packed_dimension}]
                /* empty */                             { $$ = nullptr; }
        |       rangeList                               { $$ = $1; }
        ;

rangeList<nodeRangep>:          // IEEE: {packed_dimension}
                anyrange                                { $$ = $1; }
        |       rangeList anyrange                      { $$ = $1->addNext($2); }
        ;

// IEEE: select
// Merged into more general idArray

anyrange<nodeRangep>:
                '[' constExpr ':' constExpr ']'         { $$ = new AstRange{$1, $2, $4}; }
        ;

packed_dimensionListE<nodeRangep>:      // IEEE: [{ packed_dimension }]
                /* empty */                             { $$ = nullptr; }
        |       packed_dimensionList                    { $$ = $1; }
        ;

packed_dimensionList<nodeRangep>:       // IEEE: { packed_dimension }
                packed_dimension                        { $$ = $1; }
        |       packed_dimensionList packed_dimension   { $$ = $1->addNext($2); }
        ;

packed_dimension<nodeRangep>:   // ==IEEE: packed_dimension
                anyrange                                { $$ = $1; }
        |       '[' ']'
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: [] dimensions"); }
        ;

//************************************************
// Parameters

param_assignment<varp>:         // ==IEEE: param_assignment
        //                      // IEEE: constant_param_expression
        //                      // constant_param_expression: '$' is in expr
                id/*new-parameter*/ variable_dimensionListE sigAttrListE exprOrDataTypeEqE
                        { $$ = VARDONEA($<fl>1, *$1, $2, $3);
                          if ($4) $$->valuep($4); }
        ;

list_of_param_assignments<varp>:        // ==IEEE: list_of_param_assignments
                param_assignment                        { $$ = $1; }
        |       list_of_param_assignments ',' param_assignment  { $$ = $1->addNext($3); }
        ;

type_assignment<varp>:          // ==IEEE: type_assignment
        //                      // note exptOrDataType being a data_type is only for yPARAMETER yTYPE
                idAny/*new-parameter*/ sigAttrListE
                        { $$ = VARDONEA($<fl>1, *$1, nullptr, $2); }
        |       idAny/*new-parameter*/ sigAttrListE '=' data_type
                        { $$ = VARDONEA($<fl>1, *$1, nullptr, $2); $$->valuep($4); }
        ;

list_of_type_assignments<varp>:         // ==IEEE: list_of_type_assignments
                type_assignment                         { $$ = $1; }
        |       list_of_type_assignments ',' type_assignment    { $$ = $1->addNext($3); }
        ;

list_of_defparam_assignments<nodep>:    //== IEEE: list_of_defparam_assignments
                defparam_assignment                     { $$ = $1; }
        |       list_of_defparam_assignments ',' defparam_assignment    { $$ = $1->addNext($3); }
        ;

defparam_assignment<nodep>:     // ==IEEE: defparam_assignment
                idAny '.' idAny '=' expr                { $$ = new AstDefParam{$4, *$1, *$3, $5}; }
        |       idAny '=' expr
                        { $$ = nullptr; BBUNSUP($2, "Unsupported: defparam with no dot"); }
        |       idAny '.' idAny '.'
                        { $$ = nullptr; BBUNSUP($4, "Unsupported: defparam with more than one dot"); }
        ;

//************************************************
// Instances
// We don't know identifier types, so this matches all module,udp,etc instantiation
//   module_id      [#(params)]   name  (pins) [, name ...] ;   // module_instantiation
//   gate (strong0) [#(delay)]   [name] (pins) [, (pins)...] ;  // gate_instantiation
//   program_id     [#(params}]   name ;                        // program_instantiation
//   interface_id   [#(params}]   name ;                        // interface_instantiation
//   checker_id                   name  (pins) ;                // checker_instantiation

etcInst<nodep>:                 // IEEE: module_instantiation + gate_instantiation + udp_instantiation
                instDecl                                { $$ = $1; }
        |       gateDecl                                { $$ = $1; }
        ;

instDecl<nodep>:
        //                      // Currently disambiguated from data_declaration based on
        //                      // VARs being type, and cells non-type.
        //                      // IEEE requires a '(' to disambiguate, we need TODO force this
                id parameter_value_assignmentE {INSTPREP($<fl>1, *$1, $2);} instnameList ';'
                        { $$ = $4;
                          GRAMMARP->m_impliedDecl = false;
                          if (GRAMMARP->m_instParamp) {
                              VL_DO_CLEAR(GRAMMARP->m_instParamp->deleteTree(),
                                          GRAMMARP->m_instParamp = nullptr);
                          } }
        //                      // IEEE: interface_identifier' .' modport_identifier list_of_interface_identifiers
        |       id/*interface*/ '.' id/*modport*/
        /*mid*/         { VARRESET_NONLIST(VVarType::IFACEREF);
                          AstNodeDType* const dtp = new AstIfaceRefDType{$<fl>1, $<fl>3, "", *$1, *$3};
                          VARDTYPE(dtp); }
        /*cont*/    mpInstnameList ';'
                        { $$ = VARDONEP($5, nullptr, nullptr); }
        //UNSUP: strengthSpecE for udp_instantiations
        ;

mpInstnameList<nodep>:          // Similar to instnameList, but for modport instantiations which have no parenthesis
                mpInstnameParen                         { $$ = $1; }
        |       mpInstnameList ',' mpInstnameParen      { $$ = $1->addNext($3); }
        ;

mpInstnameParen<nodep>:         // Similar to instnameParen, but for modport instantiations which have no parenthesis
                id instRangeListE sigAttrListE          { $$ = VARDONEA($<fl>1, *$1, $2, $3); }
        ;

instnameList<nodep>:
                instnameParen                           { $$ = $1; }
        |       instnameList ',' instnameParen          { $$ = $1->addNext($3); }
        ;

instnameParen<nodep>:
                id instRangeListE '(' cellpinListE ')'
                        { $$ = GRAMMARP->createCellOrIfaceRef($<fl>1, *$1, $4, $2, true); }
        |       id instRangeListE
                        { $$ = GRAMMARP->createCellOrIfaceRef($<fl>1, *$1, nullptr, $2, false); }
        //UNSUP instRangeListE '(' cellpinListE ')'      { UNSUP } // UDP
        //                      // Adding above and switching to the Verilog-Perl syntax
        //                      // causes a shift conflict due to use of idClassSel inside exprScope.
        //                      // It also breaks allowing "id foo;" instantiation syntax.
        ;

instRangeListE<nodeRangep>:
                /* empty */                             { $$ = nullptr; }
        |       instRangeList                           { $$ = $1; }
        ;

instRangeList<nodeRangep>:
                instRange                               { $$ = $1; }
        |       instRangeList instRange                 { $$ = addNextNull($1, $2); }
        ;

instRange<nodeRangep>:
                '[' constExpr ']'
                        { $$ = new AstRange{$1, new AstConst{$1, 0}, new AstSub{$1, $2, new AstConst{$1, 1}}}; }
        |       '[' constExpr ':' constExpr ']'
                        { $$ = new AstRange{$1, $2, $4}; }
        ;

cellparamListE<pinp>:
                { GRAMMARP->pinPush(); } cellparamItListE   { $$ = $2; GRAMMARP->pinPop(CRELINE()); }
        ;

cellpinListE<pinp>:
                { VARRESET_LIST(UNKNOWN); } cellpinItListE   { $$ = $2; VARRESET_NONLIST(UNKNOWN); }
        ;

cellparamItListE<pinp>:         // IEEE: list_of_parameter_assignmente
                cellparamItemE                          { $$ = $1; }
        |       cellparamItListE ',' cellparamItemE     { $$ = addNextNull($1, $3); }
        ;

cellpinItListE<pinp>:           // IEEE: list_of_port_connections
                cellpinItemE                            { $$ = $1; }
        |       cellpinItListE ',' cellpinItemE         { $$ = addNextNull($1, $3); }
        ;

cellparamItemE<pinp>:           // IEEE: named_parameter_assignment + empty
        //                      // Note empty can match either () or (,); V3LinkCells cleans up ()
                /* empty: ',,' is legal */              { $$ = new AstPin{CRELINE(), PINNUMINC(), "", nullptr}; }
        |       yP_DOTSTAR                              { $$ = new AstPin{$1, PINNUMINC(), ".*", nullptr}; }
        |       '.' idAny '(' ')'
                        { $$ = new AstPin{$<fl>2, PINNUMINC(), *$2, nullptr};
                          $$->svDotName(true); }
        |       '.' idSVKwd
                        { $$ = new AstPin{$<fl>2, PINNUMINC(), *$2,
                                          new AstParseRef{$<fl>2, VParseRefExp::PX_TEXT, *$2, nullptr, nullptr}};
                          $$->svDotName(true); $$->svImplicit(true); }
        |       '.' idAny
                        { $$ = new AstPin{$<fl>2, PINNUMINC(), *$2,
                                          new AstParseRef{$<fl>2, VParseRefExp::PX_TEXT, *$2, nullptr, nullptr}};
                          $$->svDotName(true); $$->svImplicit(true); }
        //                      // mintypmax is expanded here, as it might be a UDP or gate primitive
        //                      // data_type for 'parameter type' hookups
        |       '.' idAny '(' exprOrDataType ')'
                        { $$ = new AstPin{$<fl>2, PINNUMINC(), *$2, $4};
                          $$->svDotName(true); }
        //UNSUP | '.' idAny '(' exprOrDataType/*expr*/ ':' expr ')'
        //UNSUP          { MINTYPMAXDLYUNSUP($4); DEL($4);
        //UNSUP            $$ = new AstPin{$<fl>2, PINNUMINC(), *$2, $6};
        //UNSUP            $$->svDotName(true); }
        //UNSUP | '.' idAny '(' exprOrDataType/*expr*/ ':' expr ':' expr ')'
        //UNSUP          { MINTYPMAXDLYUNSUP($4); DEL($4); DEL($8);
        //UNSUP            $$ = new AstPin{$<fl>2, PINNUMINC(), *$2, $6};
        //UNSUP            $$->svDotName(true); }
        //                      // data_type for 'parameter type' hookups
        |       exprOrDataType
                        { $$ = new AstPin{FILELINE_OR_CRE($1), PINNUMINC(), "", $1}; }
        //UNSUP | exprOrDataType/*expr*/ ':' expr
        //UNSUP          { MINTYPMAXDLYUNSUP($1); DEL($1);
        //UNSUP            $$ = new AstPin{FILELINE_OR_CRE($3), PINNUMINC(), "", $3}; }
        //UNSUP | exprOrDataType/*expr*/ ':' expr ':' expr
        //UNSUP          { MINTYPMAXDLYUNSUP($1); DEL($1); DEL($5);
        //UNSUP            $$ = new AstPin{FILELINE_OR_CRE($3), PINNUMINC(), "", $3}; }
        ;

cellpinItemE<pinp>:             // IEEE: named_port_connection + empty
        //                      // Note empty can match either () or (,); V3LinkCells cleans up ()
                /* empty: ',,' is legal */              { $$ = new AstPin{CRELINE(), PINNUMINC(), "", nullptr}; }
        |       yP_DOTSTAR                              { $$ = new AstPin{$1, PINNUMINC(), ".*", nullptr}; }
        |       '.' idAny '(' ')'
                        { $$ = new AstPin{$<fl>2, PINNUMINC(), *$2, nullptr};
                          $$->svDotName(true); }
        |       '.' idSVKwd
                        { $$ = new AstPin{$<fl>2, PINNUMINC(), *$2,
                                          new AstParseRef{$<fl>2, VParseRefExp::PX_TEXT, *$2, nullptr, nullptr}};
                          $$->svDotName(true); $$->svImplicit(true); }
        |       '.' idAny
                        { $$ = new AstPin{$<fl>2, PINNUMINC(), *$2,
                                          new AstParseRef{$<fl>2, VParseRefExp::PX_TEXT, *$2, nullptr, nullptr}};
                          $$->svDotName(true); $$->svImplicit(true); }
        //                      // mintypmax is expanded here, as it might be a UDP or gate primitive
        //UNSUP               pev_expr below
        |       '.' idAny '(' expr ')'
                        { $$ = new AstPin{$<fl>2, PINNUMINC(), *$2, $4};
                          $$->svDotName(true); }
        //UNSUP '.' idAny '(' pev_expr ':' expr ')'     { }
        //UNSUP '.' idAny '(' pev_expr ':' expr ':' expr ')' { }
        //
        |       expr                                    { $$ = new AstPin{FILELINE_OR_CRE($1), PINNUMINC(), "", $1}; }
        //UNSUP expr ':' expr                           { }
        //UNSUP expr ':' expr ':' expr                  { }
        ;

//************************************************
// EventControl lists

attr_event_controlE<senTreep>:
                /* empty */                             { $$ = nullptr; }
        |       attr_event_control                      { $$ = $1; }
        ;

attr_event_control<senTreep>:   // ==IEEE: event_control
                '@' '(' event_expression ')'            { $$ = new AstSenTree{$1, $3}; }
        |       '@' '(' '*' ')'                         { $$ = nullptr; }
        |       '@' '*'                                 { $$ = nullptr; }
        ;

event_control<senTreep>:        // ==IEEE: event_control
                '@' '(' event_expression ')'            { $$ = new AstSenTree{$1, $3}; }
        |       '@' '(' '*' ')'                         { $$ = nullptr; }
        |       '@' '*'                                 { $$ = nullptr; }
        //                      // IEEE: hierarchical_event_identifier
        //                      // UNSUP below should be idClassSel
        |       '@' senitemVar                          { $$ = new AstSenTree{$1, $2}; } /* For events only */
        //                      // IEEE: sequence_instance
        //                      // sequence_instance without parens matches idClassSel above.
        //                      // Ambiguity: "'@' sequence (-for-sequence" versus
        //                      // expr:delay_or_event_controlE "'@' id (-for-expr
        //                      // For now we avoid this, as it's very unlikely someone would mix
        //                      // 1995 delay with a sequence with parameters.
        //                      // Alternatively split this out of event_control, and delay_or_event_controlE
        //                      // and anywhere delay_or_event_controlE is called allow two expressions
        //UNSUP '@' idClassSel '(' list_of_argumentsE ')'       { }
        ;

event_expression<senItemp>:     // IEEE: event_expression - split over several
        //UNSUP                 // Below are all removed
                senitem                                 { $$ = $1; }
        |       event_expression yOR senitem            { $$ = addNextNull($1, $3); }
        |       event_expression ',' senitem            { $$ = addNextNull($1, $3); } /* Verilog 2001 */
        //UNSUP                 // Above are all removed, replace with:
        //UNSUP ev_expr                                 { $$ = $1; }
        //UNSUP event_expression ',' ev_expr %prec yOR  { $$ = addNextNull($1, $3); }
        ;

senitem<senItemp>:              // IEEE: part of event_expression, non-'OR' ',' terms
                senitemEdge                             { $$ = $1; }
        |       expr
                        { $$ = new AstSenItem{$<fl>1, VEdgeType::ET_CHANGED, $1}; }
        |       expr yIFF expr
                        { $$ = new AstSenItem{$<fl>1, VEdgeType::ET_CHANGED, $1};
                          if ($2) BBUNSUP($2, "Unsupported: event expression 'iff'"); }
        ;

senitemVar<senItemp>:
                idClassSel                              { $$ = new AstSenItem{$1->fileline(), VEdgeType::ET_CHANGED, $1}; }
        ;

senitemEdge<senItemp>:          // IEEE: part of event_expression
                yPOSEDGE expr
                        { $$ = new AstSenItem{$1, VEdgeType::ET_POSEDGE, $2}; }
        |       yNEGEDGE expr
                        { $$ = new AstSenItem{$1, VEdgeType::ET_NEGEDGE, $2}; }
        |       yEDGE expr
                        { $$ = new AstSenItem{$1, VEdgeType::ET_BOTHEDGE, $2}; }
        |       yPOSEDGE expr yIFF expr
                        { $$ = new AstSenItem{$1, VEdgeType::ET_POSEDGE, $2};
                          BBUNSUP($3, "Unsupported: event expression 'iff'"); }
        |       yNEGEDGE expr yIFF expr
                        { $$ = new AstSenItem{$1, VEdgeType::ET_NEGEDGE, $2};
                          BBUNSUP($3, "Unsupported: event expression 'iff'"); }
        |       yEDGE expr yIFF expr
                        { $$ = new AstSenItem{$1, VEdgeType::ET_BOTHEDGE, $2};
                          BBUNSUP($3, "Unsupported: event expression 'iff'"); }
        ;

//************************************************
// Statements

stmtBlock<nodep>:               // IEEE: statement + seq_block + par_block
                stmt                                    { $$ = $1; }
        ;

seq_block<nodep>:               // ==IEEE: seq_block
        //                      // IEEE doesn't allow declarations in unnamed blocks, but several simulators do.
        //                      // So need AstBegin's even if unnamed to scope variables down
                seq_blockFront blockDeclStmtListE yEND endLabelE
                        { $$ = $1; $1->addStmtsp($2);
                          SYMP->popScope($1); GRAMMARP->endLabel($<fl>4, $1, $4); }
        ;

seq_blockPreId<nodep>:          // IEEE: seq_block, but called with leading ID
                seq_blockFrontPreId blockDeclStmtListE yEND endLabelE
                        { $$ = $1; $1->addStmtsp($2);
                          SYMP->popScope($1); GRAMMARP->endLabel($<fl>4, $1, $4); }
        ;

par_block<nodep>:               // ==IEEE: par_block
                par_blockFront blockDeclStmtListE yJOIN endLabelE
                        { $$ = $1; $1->joinType(VJoinType::JOIN);
                          V3ParseGrammar::addForkStmtsp($1, $2);
                          SYMP->popScope($1); GRAMMARP->endLabel($<fl>4, $1, $4); }
        |       par_blockFront blockDeclStmtListE yJOIN_ANY endLabelE
                        { $$ = $1; $1->joinType(VJoinType::JOIN_ANY);
                          V3ParseGrammar::addForkStmtsp($1, $2);
                          SYMP->popScope($1); GRAMMARP->endLabel($<fl>4, $1, $4); }
        |       par_blockFront blockDeclStmtListE yJOIN_NONE endLabelE
                        { $$ = $1; $1->joinType(VJoinType::JOIN_NONE);
                          V3ParseGrammar::addForkStmtsp($1, $2);
                          SYMP->popScope($1); GRAMMARP->endLabel($<fl>4, $1, $4); }
        ;

par_blockPreId<nodep>:          // ==IEEE: par_block but called with leading ID
                par_blockFrontPreId blockDeclStmtListE yJOIN endLabelE
                        { $$ = $1; $1->joinType(VJoinType::JOIN);
                          V3ParseGrammar::addForkStmtsp($1, $2);
                          SYMP->popScope($1); GRAMMARP->endLabel($<fl>4, $1, $4); }
        |       par_blockFrontPreId blockDeclStmtListE yJOIN_ANY endLabelE
                        { $$ = $1; $1->joinType(VJoinType::JOIN_ANY);
                          V3ParseGrammar::addForkStmtsp($1, $2);
                          SYMP->popScope($1); GRAMMARP->endLabel($<fl>4, $1, $4); }
        |       par_blockFrontPreId blockDeclStmtListE yJOIN_NONE endLabelE
                        { $$ = $1; $1->joinType(VJoinType::JOIN_NONE);
                          V3ParseGrammar::addForkStmtsp($1, $2);
                          SYMP->popScope($1); GRAMMARP->endLabel($<fl>4, $1, $4); }
        ;

seq_blockFront<beginp>:         // IEEE: part of seq_block
                yBEGIN
                        { $$ = new AstBegin{$1, "", nullptr};  SYMP->pushNew($$); }
        |       yBEGIN ':' idAny/*new-block_identifier*/
                        { $$ = new AstBegin{$<fl>3, *$3, nullptr}; SYMP->pushNew($$); }
        ;

par_blockFront<forkp>:          // IEEE: part of par_block
                yFORK
                        { $$ = new AstFork{$1, "", nullptr};  SYMP->pushNew($$); }
        |       yFORK ':' idAny/*new-block_identifier*/
                        { $$ = new AstFork{$<fl>3, *$3, nullptr}; SYMP->pushNew($$); }
        ;

seq_blockFrontPreId<beginp>:    // IEEE: part of seq_block/stmt with leading id
                id/*block_identifier*/ yP_COLON__BEGIN yBEGIN
                        { $$ = new AstBegin{$3, *$1, nullptr}; SYMP->pushNew($$); }
        ;

par_blockFrontPreId<forkp>:     // IEEE: part of par_block/stmt with leading id
                id/*block_identifier*/ yP_COLON__FORK yFORK
                        { $$ = new AstFork{$3, *$1, nullptr}; SYMP->pushNew($$); }
        ;


blockDeclStmtList<nodep>:       // IEEE: { block_item_declaration } { statement or null }
        //                      // The spec seems to suggest a empty declaration isn't ok, but most simulators take it
                block_item_declarationList              { $$ = $1; }
        |       block_item_declarationList stmtList     { $$ = addNextNull($1, $2); }
        |       stmtList                                { $$ = $1; }
        ;

blockDeclStmtListE<nodep>:      // IEEE: [ { block_item_declaration } { statement or null } ]
                /*empty*/                               { $$ = nullptr; }
        |       blockDeclStmtList                       { $$ = $1; }
        ;

block_item_declarationList<nodep>:      // IEEE: [ block_item_declaration ]
                block_item_declaration                  { $$ = $1; }
        |       block_item_declarationList block_item_declaration       { $$ = addNextNull($1, $2); }
        ;

block_item_declaration<nodep>:  // ==IEEE: block_item_declaration
                data_declaration                        { $$ = $1; }
        |       parameter_declaration ';'               { $$ = $1; }
        |       let_declaration                         { $$ = $1; }
        ;

stmtList<nodep>:
                stmtBlock                               { $$ = $1; }
        |       stmtList stmtBlock                      { $$ = addNextNull($1, $2); }
        ;

stmt<nodep>:                    // IEEE: statement_or_null == function_statement_or_null
                statement_item                          { $$ = $1; }
        //                      // S05 block creation rule
        |       id/*block_identifier*/ ':' statement_item       { $$ = new AstBegin{$<fl>1, *$1, $3}; }
        //                      // from _or_null
        |       ';'                                     { $$ = nullptr; }
        //                      // labeled par_block/seq_block with leading ':'
        |       seq_blockPreId                          { $$ = $1; }
        |       par_blockPreId                          { $$ = $1; }
        ;

statement_item<nodep>:          // IEEE: statement_item
        //                      // IEEE: operator_assignment
                foperator_assignment ';'                { $$ = $1; }
        //
        //                      // IEEE: blocking_assignment
        //                      // 1800-2009 restricts LHS of assignment to new to not have a range
        //                      // This is ignored to avoid conflicts
        |       fexprLvalue '=' class_new ';'           { $$ = new AstAssign{$2, $1, $3}; }
        |       fexprLvalue '=' dynamic_array_new ';'   { $$ = new AstAssign{$2, $1, $3}; }
        //
        //                      // IEEE: nonblocking_assignment
        |       fexprLvalue yP_LTE delay_or_event_controlE expr ';'
                        { $$ = new AstAssignDly{$2, $1, $4, $3}; }
        //                      // IEEE: clocking_drive ';'
        |       fexprLvalue yP_LTE cycle_delay expr ';'
                        { $$ = new AstAssignDly{$2, $1, $4, $3}; }
        //UNSUP cycle_delay fexprLvalue yP_LTE ';'      { UNSUP }
        |       yASSIGN idClassSel '=' delay_or_event_controlE expr ';'
                        { $$ = new AstAssign{$1, $2, $5, $4}; }
        |       yDEASSIGN variable_lvalue ';'
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: Verilog 1995 deassign"); }
        |       yFORCE variable_lvalue '=' expr ';'
                        { $$ = new AstAssignForce{$1, $2, $4}; v3Global.setHasForceableSignals(); }
        |       yRELEASE variable_lvalue ';'
                        { $$ = new AstRelease{$1, $2}; v3Global.setHasForceableSignals(); }
        //
        //                      // IEEE: case_statement
        |       unique_priorityE caseStart caseAttrE case_itemListE yENDCASE
                        { $$ = $2; if ($4) $2->addItemsp($4);
                          if ($1 == uniq_UNIQUE) $2->uniquePragma(true);
                          if ($1 == uniq_UNIQUE0) $2->unique0Pragma(true);
                          if ($1 == uniq_PRIORITY) $2->priorityPragma(true); }
        // &&& is part of expr so case_patternListE aliases to case_itemListE
        |       unique_priorityE caseStart caseAttrE yMATCHES case_patternListE yENDCASE
                        { $$ = nullptr; BBUNSUP($4, "Unsupported: matches (for tagged union)"); }
        |       unique_priorityE caseStart caseAttrE yINSIDE case_insideListE yENDCASE
                        { $$ = $2; if ($5) $2->addItemsp($5);
                          if (!$2->caseSimple()) $4->v3error("Illegal to have inside on a casex/casez");
                          $2->caseInsideSet();
                          if ($1 == uniq_UNIQUE) $2->uniquePragma(true);
                          if ($1 == uniq_UNIQUE0) $2->unique0Pragma(true);
                          if ($1 == uniq_PRIORITY) $2->priorityPragma(true); }
        //
        //                      // IEEE: conditional_statement
        |       unique_priorityE yIF '(' expr ')' stmtBlock     %prec prLOWER_THAN_ELSE
                        { AstIf* const newp = new AstIf{$2, $4, $6};
                          $$ = newp;
                          if ($1 == uniq_UNIQUE) newp->uniquePragma(true);
                          if ($1 == uniq_UNIQUE0) newp->unique0Pragma(true);
                          if ($1 == uniq_PRIORITY) newp->priorityPragma(true); }
        |       unique_priorityE yIF '(' expr ')' stmtBlock yELSE stmtBlock
                        { AstIf* const newp = new AstIf{$2, $4, $6, $8};
                          $$ = newp;
                          if ($1 == uniq_UNIQUE) newp->uniquePragma(true);
                          if ($1 == uniq_UNIQUE0) newp->unique0Pragma(true);
                          if ($1 == uniq_PRIORITY) newp->priorityPragma(true); }
        //
        //                      // IEEE: inc_or_dec_expression
        |       finc_or_dec_expression ';'              { $$ = $1; }
        //
        //                      // IEEE: subroutine_call_statement
        //                      // IEEE says we then expect a function call
        //                      // (function_subroutine_callNoMethod), but rest of
        //                      // the code expects an AstTask when used as a statement,
        //                      // so parse as if task
        //                      // Alternative would be shim with new AstVoidStmt.
        |       yVOID yP_TICK '(' task_subroutine_callNoMethod ')' ';'
                        { $$ = $4;
                          AstNode* callp = $$;
                          while (AstDot* const dotp = VN_CAST(callp, Dot)) callp = dotp->rhsp();
                          FileLine* const newfl = new FileLine{callp->fileline()};
                          newfl->warnOff(V3ErrorCode::IGNOREDRETURN, true);
                          callp->fileline(newfl);
                          $$ = VN_AS($$, NodeExpr)->makeStmt(); }
        |       yVOID yP_TICK '(' expr '.' task_subroutine_callNoMethod ')' ';'
                        { $$ = new AstDot{$5, false, $4, $6};
                          FileLine* const newfl = new FileLine{$6->fileline()};
                          newfl->warnOff(V3ErrorCode::IGNOREDRETURN, true);
                          $6->fileline(newfl);
                          $$ = VN_AS($$, NodeExpr)->makeStmt(); }
        |       yVOID yP_TICK '(' system_t_call ')' ';'
                        { $$ = $4;
                          FileLine* const newfl = new FileLine{$$->fileline()};
                          newfl->warnOff(V3ErrorCode::IGNOREDRETURN, true);
                          $$->fileline(newfl); }
        //
        |       task_subroutine_callNoSemi ';'          { $$ = $1; }
        //
        |       statementVerilatorPragmas               { $$ = $1; }
        //
        //                      // IEEE: disable_statement
        |       yDISABLE yFORK ';'                      { $$ = new AstDisableFork{$1}; }
        |       yDISABLE idAny/*UNSUP: hierarchical_identifier-task_or_block*/ ';'
                        { $$ = new AstDisable{$1, *$2}; }
        |       yDISABLE idAny '.' idDotted ';'
                        { $$ = nullptr; BBUNSUP($4, "Unsupported: disable with '.'"); }
        //                      // IEEE: event_trigger
        |       yP_MINUSGT idDotted/*hierarchical_identifier-event*/ ';'
                        { $$ = new AstFireEvent{$1, $2, false}; }
        |       yP_MINUSGTGT delay_or_event_controlE idDotted/*hierarchical_identifier-event*/ ';'
                        { $$ = new AstFireEvent{$1, $3, true}; }
        //
        //                      // IEEE: loop_statement
        |       yFOREVER stmtBlock
                        { $$ = new AstWhile{$1, new AstConst{$1, AstConst::BitTrue{}}, $2}; }
        |       yREPEAT '(' expr ')' stmtBlock          { $$ = new AstRepeat{$1, $3, $5}; }
        |       yWHILE '(' expr ')' stmtBlock           { $$ = new AstWhile{$1, $3, $5}; }
        //                      // for's first ';' is in for_initialization
        |       statementFor                            { $$ = $1; }
        |       yDO stmtBlock yWHILE '(' expr ')' ';'   { $$ = new AstDoWhile{$1, $5, $2}; }
        //                      // IEEE says array_identifier here, but dotted accepted in VMM and 1800-2009
        |       yFOREACH '(' idClassSelForeach ')' stmtBlock    { $$ = new AstForeach{$1, $3, $5}; }
        //
        //                      // IEEE: jump_statement
        |       yRETURN ';'                             { $$ = new AstReturn{$1}; }
        |       yRETURN expr ';'                        { $$ = new AstReturn{$1, $2}; }
        |       yBREAK ';'                              { $$ = new AstBreak{$1}; }
        |       yCONTINUE ';'                           { $$ = new AstContinue{$1}; }
        //
        |       par_block                               { $$ = $1; }
        //                      // IEEE: procedural_timing_control_statement + procedural_timing_control
        |       delay_control stmtBlock                 { AstNode* nextp = nullptr;
                                                          if ($2) {
                                                              if ($2->nextp()) nextp = $2->nextp()->unlinkFrBackWithNext();
                                                              $1->addStmtsp($2);
                                                          }
                                                          $$ = $1;
                                                          addNextNull($$, nextp); }
        |       event_control stmtBlock                 { AstNode* nextp = nullptr;
                                                          if ($2 && $2->nextp()) nextp = $2->nextp()->unlinkFrBackWithNext();
                                                          $$ = new AstEventControl{FILELINE_OR_CRE($1), $1, $2};
                                                          addNextNull($$, nextp); }
        |       cycle_delay stmtBlock
                        { AstNode* nextp = nullptr;
                          if ($2) {
                              if ($2->nextp()) nextp = $2->nextp()->unlinkFrBackWithNext();
                              $1->addStmtsp($2);
                          }
                          $$ = $1;
                          addNextNull($$, nextp); }
        |       seq_block                               { $$ = $1; }
        //
        //                      // IEEE: wait_statement
        |       yWAIT '(' expr ')' stmtBlock            { $$ = new AstWait{$1, $3, $5}; }
        |       yWAIT yFORK ';'                         { $$ = new AstWaitFork{$1}; }
        //                      // action_block expanded here
        |       yWAIT_ORDER '(' vrdList ')' stmt %prec prLOWER_THAN_ELSE
                        { $$ = nullptr; BBUNSUP($4, "Unsupported: wait_order"); }
        |       yWAIT_ORDER '(' vrdList ')' stmt yELSE stmt
                        { $$ = nullptr; BBUNSUP($4, "Unsupported: wait_order"); }
        |       yWAIT_ORDER '(' vrdList ')' yELSE stmt
                        { $$ = nullptr; BBUNSUP($4, "Unsupported: wait_order"); }
        //
        //                      // IEEE: procedural_assertion_statement
        |       procedural_assertion_statement          { $$ = $1; }
        //
        |       randsequence_statement                  { $$ = $1; }
        //
        //                      // IEEE: randcase_statement
        |       yRANDCASE rand_case_itemList yENDCASE   { $$ = new AstRandCase{$1, $2}; }
        //
        //                      // IEEE: expect_property_statement
        //                      // action_block expanded here
        |       yEXPECT '(' property_spec ')' stmt %prec prLOWER_THAN_ELSE
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: expect"); }
        |       yEXPECT '(' property_spec ')' stmt yELSE stmt
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: expect"); }
        |       yEXPECT '(' property_spec ')' yELSE stmt
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: expect"); }
        //
        |       error ';'                               { $$ = nullptr; }
        ;

statementFor<beginp>:           // IEEE: part of statement
                yFOR '(' for_initialization expr ';' for_stepE ')' stmtBlock
                        { $$ = new AstBegin{$1, "", $3, false, true};
                          $$->addStmtsp(new AstWhile{$1, $4, $8, $6}); }
        |       yFOR '(' for_initialization ';' for_stepE ')' stmtBlock
                        { $$ = new AstBegin{$1, "", $3, false, true};
                          $$->addStmtsp(new AstWhile{$1, new AstConst{$1, AstConst::BitTrue{}}, $7, $5}); }
        ;

statementVerilatorPragmas<nodep>:
                yVL_COVERAGE_BLOCK_OFF
                        { $$ = new AstPragma{$1, VPragmaType::COVERAGE_BLOCK_OFF}; }
        ;

foperator_assignment<nodep>:    // IEEE: operator_assignment (for first part of expression)
                fexprLvalue '=' delay_or_event_controlE expr    { $$ = new AstAssign{$2, $1, $4, $3}; }
        //
        |       fexprLvalue yP_PLUSEQ    expr
                        { $$ = new AstAssign{$2, $1, new AstAdd{$2, $1->cloneTreePure(true), $3}}; }
        |       fexprLvalue yP_MINUSEQ   expr
                        { $$ = new AstAssign{$2, $1, new AstSub{$2, $1->cloneTreePure(true), $3}}; }
        |       fexprLvalue yP_TIMESEQ   expr
                        { $$ = new AstAssign{$2, $1, new AstMul{$2, $1->cloneTreePure(true), $3}}; }
        |       fexprLvalue yP_DIVEQ     expr
                        { $$ = new AstAssign{$2, $1, new AstDiv{$2, $1->cloneTreePure(true), $3}}; }
        |       fexprLvalue yP_MODEQ     expr
                        { $$ = new AstAssign{$2, $1, new AstModDiv{$2, $1->cloneTreePure(true), $3}}; }
        |       fexprLvalue yP_ANDEQ     expr
                        { $$ = new AstAssign{$2, $1, new AstAnd{$2, $1->cloneTreePure(true), $3}}; }
        |       fexprLvalue yP_OREQ      expr
                        { $$ = new AstAssign{$2, $1, new AstOr{$2, $1->cloneTreePure(true), $3}}; }
        |       fexprLvalue yP_XOREQ     expr
                        { $$ = new AstAssign{$2, $1, new AstXor{$2, $1->cloneTreePure(true), $3}}; }
        |       fexprLvalue yP_SLEFTEQ   expr
                        { $$ = new AstAssign{$2, $1, new AstShiftL{$2, $1->cloneTreePure(true), $3}}; }
        |       fexprLvalue yP_SRIGHTEQ  expr
                        { $$ = new AstAssign{$2, $1, new AstShiftR{$2, $1->cloneTreePure(true), $3}}; }
        |       fexprLvalue yP_SSRIGHTEQ expr
                        { $$ = new AstAssign{$2, $1, new AstShiftRS{$2, $1->cloneTreePure(true), $3}}; }
        ;

inc_or_dec_expression<nodeExprp>:   // ==IEEE: inc_or_dec_expression
        //                      // Need fexprScope instead of variable_lvalue to prevent conflict
                ~l~exprScope yP_PLUSPLUS
                        { $<fl>$ = $<fl>1; $$ = new AstPostAdd{$2, new AstConst{$2, AstConst::StringToParse{}, "'b1"},
                                                               $1, $1->cloneTreePure(true)}; }
        |       ~l~exprScope yP_MINUSMINUS
                        { $<fl>$ = $<fl>1; $$ = new AstPostSub{$2, new AstConst{$2, AstConst::StringToParse{}, "'b1"},
                                                               $1, $1->cloneTreePure(true)}; }
        //                      // Need expr instead of variable_lvalue to prevent conflict
        |       yP_PLUSPLUS     expr
                        { $<fl>$ = $<fl>1; $$ = new AstPreAdd{$1, new AstConst{$1, AstConst::StringToParse{}, "'b1"},
                                                              $2, $2->cloneTreePure(true)}; }
        |       yP_MINUSMINUS   expr
                        { $<fl>$ = $<fl>1; $$ = new AstPreSub{$1, new AstConst{$1, AstConst::StringToParse{}, "'b1"},
                                                              $2, $2->cloneTreePure(true)}; }
        ;

finc_or_dec_expression<nodeExprp>:  // ==IEEE: inc_or_dec_expression
                BISONPRE_COPY(inc_or_dec_expression,{s/~l~/f/g})        // {copied}
        ;

sinc_or_dec_expression<nodeExprp>:  // IEEE: inc_or_dec_expression (for sequence_expression)
                BISONPRE_COPY(inc_or_dec_expression,{s/~l~/s/g})        // {copied}
        ;

pinc_or_dec_expression<nodeExprp>:  // IEEE: inc_or_dec_expression (for property_expression)
                BISONPRE_COPY(inc_or_dec_expression,{s/~l~/p/g})        // {copied}
        ;

//UNSUPev_inc_or_dec_expression<nodeExprp>:  // IEEE: inc_or_dec_expression (for ev_expr)
//UNSUP         BISONPRE_COPY(inc_or_dec_expression,{s/~l~/ev_/g})      // {copied}
//UNSUP ;

//UNSUPpev_inc_or_dec_expression<nodeExprp>:  // IEEE: inc_or_dec_expression (for pev_expr)
//UNSUP         BISONPRE_COPY(inc_or_dec_expression,{s/~l~/pev_/g})     // {copied}
//UNSUP ;

class_new<nodeExprp>:           // ==IEEE: class_new
        //                      // Special precence so (...) doesn't match expr
                yNEW__ETC                               { $$ = new AstNew{$1,  nullptr}; }
        |       yNEW__ETC expr                          { $$ = new AstNewCopy{$1, $2}; }
        |       yNEW__PAREN '(' list_of_argumentsE ')'  { $$ = new AstNew{$1, $3}; }
        ;

dynamic_array_new<nodeExprp>:   // ==IEEE: dynamic_array_new
                yNEW__ETC '[' expr ']'                  { $$ = new AstNewDynamic{$1, $3, nullptr}; }
        |       yNEW__ETC '[' expr ']' '(' expr ')'     { $$ = new AstNewDynamic{$1, $3, $6}; }
        ;

//************************************************
// Case/If

unique_priorityE<uniqstate>:    // IEEE: unique_priority + empty
                /*empty*/                               { $$ = uniq_NONE; }
        |       yPRIORITY                               { $$ = uniq_PRIORITY; }
        |       yUNIQUE                                 { $$ = uniq_UNIQUE; }
        |       yUNIQUE0                                { $$ = uniq_UNIQUE0; }
        ;

caseStart<casep>:               // IEEE: part of case_statement
                yCASE  '(' exprTypeCompare ')'
                        { $$ = GRAMMARP->m_caseAttrp = new AstCase{$1, VCaseType::CT_CASE, $3, nullptr}; }
        |       yCASEX '(' exprTypeCompare ')'
                        { $$ = GRAMMARP->m_caseAttrp = new AstCase{$1, VCaseType::CT_CASEX, $3, nullptr}; }
        |       yCASEZ '(' exprTypeCompare ')'
                        { $$ = GRAMMARP->m_caseAttrp = new AstCase{$1, VCaseType::CT_CASEZ, $3, nullptr}; }
        ;

caseAttrE:
                /*empty*/                               { }
        |       caseAttrE yVL_FULL_CASE                 { GRAMMARP->m_caseAttrp->fullPragma(true); }
        |       caseAttrE yVL_PARALLEL_CASE             { GRAMMARP->m_caseAttrp->parallelPragma(true); }
        ;

case_patternListE<caseItemp>:  // IEEE: case_pattern_item
                case_itemListE                          { $$ = $1; }
        ;

case_itemListE<caseItemp>:      // IEEE: [ { case_item } ]
                /* empty */                             { $$ = nullptr; }
        |       case_itemList                           { $$ = $1; }
        ;

case_insideListE<caseItemp>:    // IEEE: [ { case_inside_item } ]
                /* empty */                             { $$ = nullptr; }
        |       case_inside_itemList                    { $$ = $1; }
        ;

case_itemList<caseItemp>:       // IEEE: { case_item + ... }
                caseCondList colon stmtBlock                    { $$ = new AstCaseItem{$2, $1, $3}; }
        |       yDEFAULT colon stmtBlock                        { $$ = new AstCaseItem{$1, nullptr, $3}; }
        |       yDEFAULT stmtBlock                              { $$ = new AstCaseItem{$1, nullptr, $2}; }
        |       case_itemList caseCondList colon stmtBlock      { $$ = $1->addNext(new AstCaseItem{$3, $2, $4}); }
        |       case_itemList yDEFAULT stmtBlock                { $$ = $1->addNext(new AstCaseItem{$2, nullptr, $3}); }
        |       case_itemList yDEFAULT colon stmtBlock          { $$ = $1->addNext(new AstCaseItem{$2, nullptr, $4}); }
        ;

case_inside_itemList<caseItemp>:        // IEEE: { case_inside_item + open_range_list ... }
                open_range_list colon stmtBlock                 { $$ = new AstCaseItem{$2, $1, $3}; }
        |       yDEFAULT colon stmtBlock                        { $$ = new AstCaseItem{$1, nullptr, $3}; }
        |       yDEFAULT stmtBlock                              { $$ = new AstCaseItem{$1, nullptr, $2}; }
        |       case_inside_itemList open_range_list colon stmtBlock { $$ = $1->addNext(new AstCaseItem{$3, $2, $4}); }
        |       case_inside_itemList yDEFAULT stmtBlock         { $$ = $1->addNext(new AstCaseItem{$2, nullptr, $3}); }
        |       case_inside_itemList yDEFAULT colon stmtBlock   { $$ = $1->addNext(new AstCaseItem{$2, nullptr, $4}); }
        ;

rand_case_itemList<caseItemp>:       // IEEE: { rand_case_item + ... }
        //                      // Randcase syntax doesn't have default, or expression lists
                expr colon stmtBlock                            { $$ = new AstCaseItem{$2, $1, $3}; }
        |       rand_case_itemList expr colon stmtBlock         { $$ = $1->addNext(new AstCaseItem{$3, $2, $4}); }
        ;

open_range_list<nodeExprp>:     // ==IEEE: open_range_list + open_value_range
                open_value_range                        { $$ = $1; }
        |       open_range_list ',' open_value_range    { $$ = $1->addNext($3); }
        ;

open_value_range<nodeExprp>:    // ==IEEE: open_value_range
                value_range                             { $$ = $1; }
        ;

value_range<nodeExprp>:         // ==IEEE: value_range
                expr                                    { $$ = $1; }
        |       '[' expr ':' expr ']'                   { $$ = new AstInsideRange{$1, $2, $4}; }
        ;

covergroup_value_range<nodeExprp>:  // ==IEEE-2012: covergroup_value_range
                cgexpr                                  { $$ = $1; }
        |       '[' cgexpr ':' cgexpr ']'
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: covergroup value range"); }
        ;

caseCondList<nodeExprp>:        // IEEE: part of case_item
                exprTypeCompare                         { $$ = $1; }
        |       caseCondList ',' exprTypeCompare        { $$ = $1->addNext($3); }
        ;

patternNoExpr<nodep>:           // IEEE: pattern **Excluding Expr*
                '.' id/*variable*/
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: '{} tagged patterns"); }
        |       yP_DOTSTAR
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: '{} tagged patterns"); }
        //                      // IEEE: "expr" excluded; expand in callers
        //                      // "yTAGGED id [expr]" Already part of expr
        //UNSUP yTAGGED id/*member_identifier*/ patternNoExpr
        //UNSUP         { $$ = nullptr; BBUNSUP($1, "Unsupported: '{} tagged patterns"); }
        //                      // "yP_TICKBRA patternList '}'" part of expr under assignment_pattern
        ;

patternList<nodep>:             // IEEE: part of pattern
                patternOne                              { $$ = $1; }
        |       patternList ',' patternOne              { $$ = addNextNull($1, $3); }
        ;

patternOne<nodep>:              // IEEE: part of pattern
                expr
                        { if ($1) $$ = new AstPatMember{$1->fileline(), $1, nullptr, nullptr}; else $$ = nullptr; }
        |       expr '{' argsExprList '}'               { $$ = new AstPatMember{$2, $3, nullptr, $1}; }
        |       patternNoExpr                           { $$ = $1; }
        ;

patternMemberList<nodep>:       // IEEE: part of pattern and assignment_pattern
                patternMemberOne                        { $$ = $1; }
        |       patternMemberList ',' patternMemberOne  { $$ = addNextNull($1, $3); }
        ;

patternMemberOne<patMemberp>:   // IEEE: part of pattern and assignment_pattern
                patternKey ':' expr                     { $$ = new AstPatMember{$1->fileline(), $3, $1, nullptr}; }
        |       patternKey ':' patternNoExpr            { $$ = nullptr; BBUNSUP($2, "Unsupported: '{} .* patterns"); }
        //                      // From assignment_pattern_key
        |       yDEFAULT ':' expr                       { $$ = new AstPatMember{$1, $3, nullptr, nullptr}; $$->isDefault(true); }
        |       yDEFAULT ':' patternNoExpr              { $$ = nullptr; BBUNSUP($2, "Unsupported: '{} .* patterns"); }
        ;

patternKey<nodep>:              // IEEE: merge structure_pattern_key, array_pattern_key, assignment_pattern_key
        //                      // IEEE: structure_pattern_key
        //                      // id/*member*/ is part of constExpr below
        //UNSUP constExpr                               { $$ = $1; }
        //                      // IEEE: assignment_pattern_key
        //                      // Verilator:
        //                      //   The above expressions cause problems because "foo" may be
        //                      //   a constant identifier (if array) or a reference to the
        //                      //   "foo"member (if structure)
        //                      //   So for now we only allow a true constant number, or an
        //                      //   identifier which we treat as a structure member name
                yaINTNUM                                { $$ = new AstConst{$<fl>1, *$1}; }
        |       yaFLOATNUM                              { $$ = new AstConst{$<fl>1, AstConst::RealDouble{}, $1}; }
        |       id                                      { $$ = new AstText{$<fl>1, *$1}; }
        |       strAsInt                                { $$ = $1; }
        |       simple_type                             { $$ = $1; }
        ;

assignment_pattern<patternp>:   // ==IEEE: assignment_pattern
        // This doesn't match the text of the spec.  I think a : is missing, or example code needed
        // yP_TICKBRA constExpr exprList '}'    { $$="'{"+$2+" "+$3"}"; }
        //                      // "'{ const_expression }" is same as patternList with one entry
        //                      // From patternNoExpr
        //                      // also IEEE: "''{' expression { ',' expression } '}'"
        //                      //      matches since patternList includes expr
                yP_TICKBRA patternList '}'              { $$ = new AstPattern{$1, $2}; }
        //                      // From patternNoExpr
        //                      // also IEEE "''{' structure_pattern_key ':' ...
        //                      // also IEEE "''{' array_pattern_key ':' ...
        |       yP_TICKBRA patternMemberList '}'        { $$ = new AstPattern{$1, $2}; }
        //                      // IEEE: Not in grammar, but in VMM
        |       yP_TICKBRA '}'                          { $$ = new AstPattern{$1, nullptr}; }
        ;

// "datatype id = x {, id = x }"  |  "yaId = x {, id=x}" is legal
for_initialization<nodep>:      // ==IEEE: for_initialization + for_variable_declaration + extra terminating ";"
        //                      // IEEE: for_variable_declaration
                for_initializationItemList ';'          { $$ = $1; }
        //                      // IEEE: 1800-2017 empty initialization
        |       ';'                                     { $$ = nullptr; }
        ;

for_initializationItemList<nodep>:      // IEEE: [for_variable_declaration...]
                for_initializationItem                  { $$ = $1; }
        |       for_initializationItemList ',' for_initializationItem   { $$ = addNextNull($1, $3); }
        ;

for_initializationItem<nodep>:          // IEEE: variable_assignment + for_variable_declaration
        //                      // IEEE: for_variable_declaration
                data_type idAny/*new*/ '=' expr
                        { VARRESET_NONLIST(VAR); VARDTYPE($1);
                          AstVar* const varp = VARDONEA($<fl>2, *$2, nullptr, nullptr);
                          varp->lifetime(VLifetime::AUTOMATIC);
                          $$ = varp;
                          $$->addNext(new AstAssign{$3, new AstParseRef{$<fl>2, VParseRefExp::PX_TEXT, *$2}, $4}); }
        //                      // IEEE-2012:
        |       yVAR data_type idAny/*new*/ '=' expr
                        { VARRESET_NONLIST(VAR); VARDTYPE($2);
                          AstVar* const varp = VARDONEA($<fl>3, *$3, nullptr, nullptr);
                          varp->lifetime(VLifetime::AUTOMATIC);
                          $$ = varp;
                          $$->addNext(new AstAssign{$4, new AstParseRef{$<fl>3, VParseRefExp::PX_TEXT, *$3}, $5}); }
        //                      // IEEE: variable_assignment
        //                      // UNSUP variable_lvalue below
        |       varRefBase '=' expr                     { $$ = new AstAssign{$2, $1, $3}; }
        ;

for_stepE<nodep>:               // IEEE: for_step + empty
                /* empty */                             { $$ = nullptr; }
        |       for_step                                { $$ = $1; }
        ;

for_step<nodep>:                // IEEE: for_step
                for_step_assignment                     { $$ = $1; }
        |       for_step ',' for_step_assignment        { $$ = addNextNull($1, $3); }
        ;

for_step_assignment<nodep>:     // ==IEEE: for_step_assignment
                foperator_assignment                    { $$ = $1; }
        |       finc_or_dec_expression                  { $$ = $1; }
        //                      // IEEE: function_subroutine_call
        |       task_subroutine_callNoSemi              { $$ = $1; }
        ;

loop_variables<nodep>:          // IEEE: loop_variables
                parseRefBase                            { $$ = $1; }
        |       loop_variables ',' parseRefBase         { $$ = $1->addNext($3); }
        |       ',' parseRefBase                        { $$ = new AstEmpty{$1}; $$->addNext($2); }
        ;

//************************************************
// Functions/tasks

taskRef<nodeExprp>:            // IEEE: part of tf_call
                id                                      { $$ = new AstTaskRef{$<fl>1, *$1, nullptr}; }
        |       id '(' list_of_argumentsE ')'           { $$ = new AstTaskRef{$<fl>1, *$1, $3}; }
        |       packageClassScope id '(' list_of_argumentsE ')'
                        { $$ = AstDot::newIfPkg($<fl>2, $1, new AstTaskRef{$<fl>2, *$2, $4}); }
        ;

funcRef<nodeExprp>:             // IEEE: part of tf_call
        //                      // package_scope/hierarchical_... is part of expr, so just need ID
        //                      //      making-a                id-is-a
        //                      //      -----------------       ------------------
        //                      //      tf_call                 tf_identifier           expr (list_of_arguments)
        //                      //      method_call(post .)     function_identifier     expr (list_of_arguments)
        //                      //      property_instance       property_identifier     property_actual_arg
        //                      //      sequence_instance       sequence_identifier     sequence_actual_arg
        //                      //      let_expression          let_identifier          let_actual_arg
        //
                id '(' list_of_argumentsE ')'
                        { $$ = new AstFuncRef{$<fl>1, *$1, $3}; }
        |       packageClassScope id '(' list_of_argumentsE ')'
                        { $$ = AstDot::newIfPkg($<fl>2, $1, new AstFuncRef{$<fl>2, *$2, $4}); }
        //UNSUP list_of_argumentE should be pev_list_of_argumentE
        //UNSUP: idDotted is really just id to allow dotted method calls
        ;

task_subroutine_callNoSemi<nodep>:  // similar to IEEE task_subroutine_call but without ';'
        //                      // Expr included here to resolve our not knowing what is a method call
        //                      // Expr here must result in a subroutine_call
                task_subroutine_callNoMethod           { $$ = $1->makeStmt(); }
        |       fexpr '.' task_subroutine_callNoMethod  { $$ = (new AstDot{$<fl>2, false, $1, $3})->makeStmt(); }
        |       system_t_call                          { $$ = $1; }
        //                      // Not here in IEEE; from class_constructor_declaration
        //                      // Because we've joined class_constructor_declaration into generic functions
        //                      // Way over-permissive;
        //                      // IEEE: [ ySUPER '.' yNEW [ '(' list_of_arguments ')' ] ';' ]
        |       fexpr '.' class_new                    { $$ = (new AstDot{$<fl>2, false, $1, $3})->makeStmt(); }
        ;

task_subroutine_callNoMethod<nodeExprp>:    // function_subroutine_callNoMethod (as task)
        //                      // IEEE: tf_call
                taskRef                                 { $$ = $1; }
        //                      // funcref below not task ref to avoid conflict, must later handle either
        |       funcRef yWITH__PAREN '(' expr ')'       { $$ = new AstWithParse{$2, $1, $4}; }
        //                      // can call as method and yWITH without parenthesis
        |       id yWITH__PAREN '(' expr ')'            { $$ = new AstWithParse{$2, new AstFuncRef{$<fl>1, *$1, nullptr}, $4}; }
        //                      // IEEE: method_call requires a "." so is in expr
        //                      // IEEE: ['std::'] not needed, as normal std package resolution will find it
        //                      // IEEE: randomize_call
        //                      // We implement randomize as a normal funcRef, since randomize isn't a keyword
        //                      // Note yNULL is already part of expressions, so they come for free
        //UNSUP funcRef yWITH__CUR constraint_block     { }
        ;

function_subroutine_callNoMethod<nodeExprp>:        // IEEE: function_subroutine_call (as function)
        //                      // IEEE: tf_call
                funcRef                                 { $$ = $1; }
        |       funcRef yWITH__PAREN '(' expr ')'       { $$ = new AstWithParse{$2, $1, $4}; }
        //                      // can call as method and yWITH without parenthesis
        |       id yWITH__PAREN '(' expr ')'            { $$ = new AstWithParse{$2, new AstFuncRef{$<fl>1, *$1, nullptr}, $4}; }
        |       system_f_call                           { $$ = $1; }
        //                      // IEEE: method_call requires a "." so is in expr
        //                      // IEEE: ['std::'] not needed, as normal std package resolution will find it
        //                      // IEEE: randomize_call
        //                      // We implement randomize as a normal funcRef, since randomize isn't a keyword
        //                      // Note yNULL is already part of expressions, so they come for free
        |       funcRef yWITH__CUR constraint_block
                        { $$ = $1; BBUNSUP($2, "Unsupported: randomize() 'with' constraint"); }
        |       funcRef yWITH__CUR '{' '}'              { $$ = new AstWithParse{$2, $1, nullptr}; }
        ;

system_t_call<nodeStmtp>:       // IEEE: system_tf_call (as task)
        //
                yaD_PLI systemDpiArgsE                  { AstTaskRef* const refp = new AstTaskRef{$<fl>1, *$1, $2};
                                                          refp->pli(true);
                                                          $$ = refp->makeStmt(); }
        //
        |       yD_DUMPPORTS '(' idDotted ',' expr ')'  { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::FILE, $5}; DEL($3);
                                                          $$->addNext(new AstDumpCtl{$<fl>1, VDumpCtlType::VARS,
                                                                                     new AstConst{$<fl>1, 1}}); }
        |       yD_DUMPPORTS '(' ',' expr ')'           { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::FILE, $4};
                                                          $$->addNext(new AstDumpCtl{$<fl>1, VDumpCtlType::VARS,
                                                                                     new AstConst{$<fl>1, 1}}); }
        |       yD_DUMPFILE '(' expr ')'                { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::FILE, $3}; }
        |       yD_DUMPVARS parenE                      { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::VARS,
                                                                              new AstConst{$<fl>1, 0}}; }
        |       yD_DUMPVARS '(' expr ')'                { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::VARS, $3}; }
        |       yD_DUMPVARS '(' expr ',' exprList ')'   { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::VARS, $3}; DEL($5); }
        |       yD_DUMPALL parenE                       { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::ALL}; }
        |       yD_DUMPALL '(' expr ')'                 { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::ALL}; DEL($3); }
        |       yD_DUMPFLUSH parenE                     { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::FLUSH}; }
        |       yD_DUMPFLUSH '(' expr ')'               { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::FLUSH}; DEL($3); }
        |       yD_DUMPLIMIT '(' expr ')'               { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::LIMIT, $3}; }
        |       yD_DUMPLIMIT '(' expr ',' expr ')'      { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::LIMIT, $3}; DEL($5); }
        |       yD_DUMPOFF parenE                       { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::OFF}; }
        |       yD_DUMPOFF '(' expr ')'                 { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::OFF}; DEL($3); }
        |       yD_DUMPON parenE                        { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::ON}; }
        |       yD_DUMPON '(' expr ')'                  { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::ON}; DEL($3); }
        //
        |       yD_C '(' cStrList ')'                   { $$ = (v3Global.opt.ignc() ? nullptr : new AstUCStmt{$1, $3}); }
        |       yD_STACKTRACE parenE                    { $$ = new AstStackTraceT{$1}; }
        |       yD_SYSTEM '(' expr ')'                  { $$ = new AstSystemT{$1, $3}; }
        //
        |       yD_EXIT parenE                          { $$ = new AstFinish{$1}; }
        //
        |       yD_FCLOSE '(' expr ')'                  { $$ = new AstFClose{$1, $3}; }
        |       yD_FFLUSH parenE                        { $$ = new AstFFlush{$1, nullptr}; }
        |       yD_FFLUSH '(' expr ')'                  { $$ = new AstFFlush{$1, $3}; }
        |       yD_FINISH parenE                        { $$ = new AstFinish{$1}; }
        |       yD_FINISH '(' expr ')'                  { $$ = new AstFinish{$1}; DEL($3); }
        |       yD_STOP parenE                          { $$ = new AstStop{$1, false}; }
        |       yD_STOP '(' expr ')'                    { $$ = new AstStop{$1, false}; DEL($3); }
        //
        |       yD_SFORMAT '(' expr ',' exprDispList ')'        { $$ = new AstSFormat{$1, $3, $5}; }
        |       yD_SWRITE  '(' expr ',' exprDispList ')'        { $$ = new AstSFormat{$1, $3, $5}; }
        |       yD_SWRITEB '(' expr ',' exprDispList ')'        { $$ = new AstSFormat{$1, $3, $5, 'b'}; }
        |       yD_SWRITEH '(' expr ',' exprDispList ')'        { $$ = new AstSFormat{$1, $3, $5, 'h'}; }
        |       yD_SWRITEO '(' expr ',' exprDispList ')'        { $$ = new AstSFormat{$1, $3, $5, 'o'}; }
        //
        |       yD_DISPLAY parenE                               { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, nullptr, nullptr}; }
        |       yD_DISPLAY '(' commasE exprDispList ')'         { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, nullptr, $4}; }
        |       yD_DISPLAYB parenE                              { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, nullptr, nullptr, 'b'}; }
        |       yD_DISPLAYB '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, nullptr, $4, 'b'}; }
        |       yD_DISPLAYH parenE                              { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, nullptr, nullptr, 'h'}; }
        |       yD_DISPLAYH '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, nullptr, $4, 'h'}; }
        |       yD_DISPLAYO parenE                              { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, nullptr, nullptr, 'o'}; }
        |       yD_DISPLAYO '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, nullptr, $4, 'o'}; }
        |       yD_MONITOR  '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_MONITOR, nullptr, $4}; }
        |       yD_MONITORB '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_MONITOR, nullptr, $4, 'b'}; }
        |       yD_MONITORH '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_MONITOR, nullptr, $4, 'h'}; }
        |       yD_MONITORO '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_MONITOR, nullptr, $4, 'o'}; }
        |       yD_STROBE   '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_STROBE, nullptr, $4}; }
        |       yD_STROBEB  '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_STROBE, nullptr, $4, 'b'}; }
        |       yD_STROBEH  '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_STROBE, nullptr, $4, 'h'}; }
        |       yD_STROBEO  '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_STROBE, nullptr, $4, 'o'}; }
        |       yD_WRITE    parenE                              { $$ = nullptr; }  // NOP
        |       yD_WRITE    '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_WRITE, nullptr, $4}; }
        |       yD_WRITEB   parenE                              { $$ = nullptr; }  // NOP
        |       yD_WRITEB   '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_WRITE, nullptr, $4, 'b'}; }
        |       yD_WRITEH   parenE                              { $$ = nullptr; }  // NOP
        |       yD_WRITEH   '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_WRITE, nullptr, $4, 'h'}; }
        |       yD_WRITEO   parenE                              { $$ = nullptr; }  // NOP
        |       yD_WRITEO   '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_WRITE, nullptr, $4, 'o'}; }
        |       yD_FDISPLAY '(' expr ')'                        { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, $3, nullptr}; }
        |       yD_FDISPLAY '(' expr ',' exprDispList ')'       { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, $3, $5}; }
        |       yD_FDISPLAYB '(' expr ')'                       { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, $3, nullptr, 'b'}; }
        |       yD_FDISPLAYB '(' expr ',' exprDispList ')'      { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, $3, $5, 'b'}; }
        |       yD_FDISPLAYH '(' expr ')'                       { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, $3, nullptr, 'h'}; }
        |       yD_FDISPLAYH '(' expr ',' exprDispList ')'      { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, $3, $5, 'h'}; }
        |       yD_FDISPLAYO '(' expr ')'                       { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, $3, nullptr, 'o'}; }
        |       yD_FDISPLAYO '(' expr ',' exprDispList ')'      { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, $3, $5, 'o'}; }
        |       yD_FMONITOR  '(' expr ',' exprDispList ')'      { $$ = new AstDisplay{$1, VDisplayType::DT_MONITOR, $3, $5}; }
        |       yD_FMONITORB '(' expr ',' exprDispList ')'      { $$ = new AstDisplay{$1, VDisplayType::DT_MONITOR, $3, $5, 'b'}; }
        |       yD_FMONITORH '(' expr ',' exprDispList ')'      { $$ = new AstDisplay{$1, VDisplayType::DT_MONITOR, $3, $5, 'h'}; }
        |       yD_FMONITORO '(' expr ',' exprDispList ')'      { $$ = new AstDisplay{$1, VDisplayType::DT_MONITOR, $3, $5, 'o'}; }
        |       yD_FSTROBE   '(' expr ')'                       { $$ = new AstDisplay{$1, VDisplayType::DT_STROBE, $3, nullptr}; }
        |       yD_FSTROBE   '(' expr ',' exprDispList ')'      { $$ = new AstDisplay{$1, VDisplayType::DT_STROBE, $3, $5}; }
        |       yD_FSTROBEB  '(' expr ',' exprDispList ')'      { $$ = new AstDisplay{$1, VDisplayType::DT_STROBE, $3, $5, 'b'}; }
        |       yD_FSTROBEH  '(' expr ',' exprDispList ')'      { $$ = new AstDisplay{$1, VDisplayType::DT_STROBE, $3, $5, 'h'}; }
        |       yD_FSTROBEO  '(' expr ',' exprDispList ')'      { $$ = new AstDisplay{$1, VDisplayType::DT_STROBE, $3, $5, 'o'}; }
        |       yD_FWRITE   '(' expr ')'                        { $$ = new AstDisplay{$1, VDisplayType::DT_WRITE, $3, nullptr}; }
        |       yD_FWRITE   '(' expr ',' exprDispList ')'       { $$ = new AstDisplay{$1, VDisplayType::DT_WRITE, $3, $5}; }
        |       yD_FWRITEB  '(' expr ',' exprDispList ')'       { $$ = new AstDisplay{$1, VDisplayType::DT_WRITE, $3, $5, 'b'}; }
        |       yD_FWRITEH  '(' expr ',' exprDispList ')'       { $$ = new AstDisplay{$1, VDisplayType::DT_WRITE, $3, $5, 'h'}; }
        |       yD_FWRITEO  '(' expr ',' exprDispList ')'       { $$ = new AstDisplay{$1, VDisplayType::DT_WRITE, $3, $5, 'o'}; }
        |       yD_INFO     parenE                              { $$ = new AstDisplay{$1, VDisplayType::DT_INFO, nullptr, nullptr}; }
        |       yD_INFO     '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_INFO, nullptr, $4}; }
        |       yD_WARNING  parenE                              { $$ = new AstDisplay{$1, VDisplayType::DT_WARNING, nullptr, nullptr}; }
        |       yD_WARNING  '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_WARNING, nullptr, $4}; }
        |       yD_ERROR    parenE                              { $$ = GRAMMARP->createDisplayError($1); }
        |       yD_ERROR    '(' commasE exprDispList ')'
                        { $$ = new AstDisplay{$1, VDisplayType::DT_ERROR, nullptr, $4};
                          $$->addNext(new AstStop{$1, true}); }
        |       yD_FATAL    parenE
                        { $$ = new AstDisplay{$1, VDisplayType::DT_FATAL, nullptr, nullptr};
                          $$->addNext(new AstStop{$1, false}); }
        |       yD_FATAL    '(' expr ')'
                        { $$ = new AstDisplay{$1, VDisplayType::DT_FATAL, nullptr, nullptr};
                          $$->addNext(new AstStop{$1, false}); DEL($3); }
        |       yD_FATAL    '(' expr ',' exprDispList ')'
                        { $$ = new AstDisplay{$1, VDisplayType::DT_FATAL, nullptr, $5};
                          $$->addNext(new AstStop{$1, false}); DEL($3); }
        //
        |       yD_MONITOROFF parenE                    { $$ = new AstMonitorOff{$1, true}; }
        |       yD_MONITORON parenE                     { $$ = new AstMonitorOff{$1, false}; }
        //
        |       yD_PRINTTIMESCALE                       { $$ = new AstPrintTimeScale{$1}; }
        |       yD_PRINTTIMESCALE '(' ')'               { $$ = new AstPrintTimeScale{$1}; }
        |       yD_PRINTTIMESCALE '(' idClassSel ')'    { $$ = new AstPrintTimeScale{$1}; DEL($3); }
        |       yD_TIMEFORMAT '(' expr ',' expr ',' expr ',' expr ')'
                        { $$ = new AstTimeFormat{$1, $3, $5, $7, $9}; }
        //
        |       yD_READMEMB '(' expr ',' idClassSel ')'                         { $$ = new AstReadMem{$1, false, $3, $5, nullptr, nullptr}; }
        |       yD_READMEMB '(' expr ',' idClassSel ',' expr ')'                { $$ = new AstReadMem{$1, false, $3, $5, $7, nullptr}; }
        |       yD_READMEMB '(' expr ',' idClassSel ',' expr ',' expr ')'       { $$ = new AstReadMem{$1, false, $3, $5, $7, $9}; }
        |       yD_READMEMH '(' expr ',' idClassSel ')'                         { $$ = new AstReadMem{$1, true,  $3, $5, nullptr, nullptr}; }
        |       yD_READMEMH '(' expr ',' idClassSel ',' expr ')'                { $$ = new AstReadMem{$1, true,  $3, $5, $7, nullptr}; }
        |       yD_READMEMH '(' expr ',' idClassSel ',' expr ',' expr ')'       { $$ = new AstReadMem{$1, true,  $3, $5, $7, $9}; }
        //
        |       yD_WRITEMEMB '(' expr ',' idClassSel ')'                        { $$ = new AstWriteMem{$1, false, $3, $5, nullptr, nullptr}; }
        |       yD_WRITEMEMB '(' expr ',' idClassSel ',' expr ')'               { $$ = new AstWriteMem{$1, false, $3, $5, $7, nullptr}; }
        |       yD_WRITEMEMB '(' expr ',' idClassSel ',' expr ',' expr ')'      { $$ = new AstWriteMem{$1, false, $3, $5, $7, $9}; }
        |       yD_WRITEMEMH '(' expr ',' idClassSel ')'                        { $$ = new AstWriteMem{$1, true,  $3, $5, nullptr, nullptr}; }
        |       yD_WRITEMEMH '(' expr ',' idClassSel ',' expr ')'               { $$ = new AstWriteMem{$1, true,  $3, $5, $7, nullptr}; }
        |       yD_WRITEMEMH '(' expr ',' idClassSel ',' expr ',' expr ')'      { $$ = new AstWriteMem{$1, true,  $3, $5, $7, $9}; }
        //
        |       yD_CAST '(' expr ',' expr ')'
                        { FileLine* const fl_nowarn = new FileLine{$1};
                          fl_nowarn->warnOff(V3ErrorCode::WIDTH, true);
                          $$ = new AstAssertIntrinsic{fl_nowarn, new AstCastDynamic{fl_nowarn, $5, $3},
                                                      nullptr, nullptr, true}; }
        //
        // Any system function as a task
        |       system_f_call_or_t                      { $$ = new AstSysFuncAsTask{$<fl>1, $1}; }
        ;

system_f_call<nodeExprp>:           // IEEE: system_tf_call (as func)
                yaD_PLI systemDpiArgsE                  { $$ = new AstFuncRef{$<fl>1, *$1, $2}; VN_CAST($$, FuncRef)->pli(true); }
        //
        |       yD_C '(' cStrList ')'                   { $$ = (v3Global.opt.ignc() ? nullptr : new AstUCFunc{$1, $3}); }
        |       yD_CAST '(' expr ',' expr ')'           { $$ = new AstCastDynamic{$1, $5, $3}; }
        |       yD_STACKTRACE parenE                    { $$ = new AstStackTraceF{$1}; }
        |       yD_SYSTEM  '(' expr ')'                 { $$ = new AstSystemF{$1, $3}; }
        //
        |       system_f_call_or_t                      { $$ = $1; }
        ;

systemDpiArgsE<argp>:           // IEEE: part of system_if_call for arguments of $dpi call
                parenE                                  { $$ = nullptr; }
        |       '(' exprList ')'                        { $$ = GRAMMARP->argWrapList($2); }
        ;

system_f_call_or_t<nodeExprp>:      // IEEE: part of system_tf_call (can be task or func)
                yD_ACOS '(' expr ')'                    { $$ = new AstAcosD{$1, $3}; }
        |       yD_ACOSH '(' expr ')'                   { $$ = new AstAcoshD{$1, $3}; }
        |       yD_ASIN '(' expr ')'                    { $$ = new AstAsinD{$1, $3}; }
        |       yD_ASINH '(' expr ')'                   { $$ = new AstAsinhD{$1, $3}; }
        |       yD_ATAN '(' expr ')'                    { $$ = new AstAtanD{$1, $3}; }
        |       yD_ATAN2 '(' expr ',' expr ')'          { $$ = new AstAtan2D{$1, $3, $5}; }
        |       yD_ATANH '(' expr ')'                   { $$ = new AstAtanhD{$1, $3}; }
        |       yD_BITS '(' exprOrDataType ')'          { $$ = new AstAttrOf{$1, VAttrType::DIM_BITS, $3}; }
        |       yD_BITS '(' exprOrDataType ',' expr ')' { $$ = new AstAttrOf{$1, VAttrType::DIM_BITS, $3, $5}; }
        |       yD_BITSTOREAL '(' expr ')'              { $$ = new AstBitsToRealD{$1, $3}; }
        |       yD_BITSTOSHORTREAL '(' expr ')'         { $$ = new AstBitsToRealD{$1, $3}; UNSUPREAL($1); }
        |       yD_CEIL '(' expr ')'                    { $$ = new AstCeilD{$1, $3}; }
        |       yD_CHANGED '(' expr ')'                 { $$ = new AstLogNot{$1, new AstStable{$1, $3, nullptr}}; }
        |       yD_CHANGED '(' expr ',' expr ')'
                        { $$ = new AstLogNot{$1, new AstStable{$1, $3, GRAMMARP->createClockSenTree($1, $5)}}; }
        |       yD_CHANGED_GCLK '(' expr ')'
                        { $$ = new AstLogNot{$1, new AstStable{$1, $3, GRAMMARP->createGlobalClockSenTree($1)}}; }
        |       yD_CLOG2 '(' expr ')'                   { $$ = new AstCLog2{$1, $3}; }
        |       yD_COS '(' expr ')'                     { $$ = new AstCosD{$1, $3}; }
        |       yD_COSH '(' expr ')'                    { $$ = new AstCoshD{$1, $3}; }
        |       yD_COUNTBITS '(' expr ',' expr ')'              { $$ = new AstCountBits{$1, $3, $5}; }
        |       yD_COUNTBITS '(' expr ',' expr ',' expr ')'             { $$ = new AstCountBits{$1, $3, $5, $7}; }
        |       yD_COUNTBITS '(' expr ',' expr ',' expr ',' expr ')'    { $$ = new AstCountBits{$1, $3, $5, $7, $9}; }
        |       yD_COUNTBITS '(' expr ',' expr ',' expr ',' expr ',' exprList ')'
                        { $$ = new AstCountBits{$1, $3, $5, $7, $9};
                          BBUNSUP($11, "Unsupported: $countbits with more than 3 control fields"); }
        |       yD_COUNTONES '(' expr ')'               { $$ = new AstCountOnes{$1, $3}; }
        |       yD_DIMENSIONS '(' exprOrDataType ')'    { $$ = new AstAttrOf{$1, VAttrType::DIM_DIMENSIONS, $3}; }
        |       yD_DIST_CHI_SQUARE '(' expr ',' expr ')'        { $$ = new AstDistChiSquare{$1, $3, $5}; }
        |       yD_DIST_ERLANG '(' expr ',' expr ',' expr ')'   { $$ = new AstDistErlang{$1, $3, $5, $7}; }
        |       yD_DIST_EXPONENTIAL '(' expr ',' expr ')'       { $$ = new AstDistExponential{$1, $3, $5}; }
        |       yD_DIST_NORMAL '(' expr ',' expr ',' expr ')'   { $$ = new AstDistNormal{$1, $3, $5, $7}; }
        |       yD_DIST_POISSON '(' expr ',' expr ')'   { $$ = new AstDistPoisson{$1, $3, $5}; }
        |       yD_DIST_T '(' expr ',' expr ')'         { $$ = new AstDistT{$1, $3, $5}; }
        |       yD_DIST_UNIFORM '(' expr ',' expr ',' expr ')'  { $$ = new AstDistUniform{$1, $3, $5, $7}; }
        |       yD_EXP '(' expr ')'                     { $$ = new AstExpD{$1, $3}; }
        |       yD_FELL '(' expr ')'                    { $$ = new AstFell{$1, $3, nullptr}; }
        |       yD_FELL '(' expr ',' expr ')'           { $$ = new AstFell{$1, $3, GRAMMARP->createClockSenTree($1, $5)}; }
        |       yD_FELL_GCLK '(' expr ')'               { $$ = new AstFell{$1, $3, GRAMMARP->createGlobalClockSenTree($1)}; }
        |       yD_FEOF '(' expr ')'                    { $$ = new AstFEof{$1, $3}; }
        |       yD_FERROR '(' expr ',' idClassSel ')'   { $$ = new AstFError{$1, $3, $5}; }
        |       yD_FGETC '(' expr ')'                   { $$ = new AstFGetC{$1, $3}; }
        |       yD_FGETS '(' expr ',' expr ')'          { $$ = new AstFGetS{$1, $3, $5}; }
        |       yD_FOPEN '(' expr ')'                   { $$ = new AstFOpenMcd{$1, $3}; }
        |       yD_FOPEN '(' expr ',' expr ')'          { $$ = new AstFOpen{$1, $3, $5}; }
        |       yD_FREAD '(' expr ',' expr ')'          { $$ = new AstFRead{$1, $3, $5, nullptr, nullptr}; }
        |       yD_FREAD '(' expr ',' expr ',' expr ')'  { $$ = new AstFRead{$1, $3, $5, $7, nullptr}; }
        |       yD_FREAD '(' expr ',' expr ',' expr ',' expr ')'  { $$ = new AstFRead{$1, $3, $5, $7, $9}; }
        |       yD_FREWIND '(' expr ')'                 { $$ = new AstFRewind{$1, $3}; }
        |       yD_FLOOR '(' expr ')'                   { $$ = new AstFloorD{$1, $3}; }
        |       yD_FSCANF '(' expr ',' str commaVRDListE ')'    { $$ = new AstFScanF{$1, *$5, $3, $6}; }
        |       yD_FSEEK '(' expr ',' expr ',' expr ')' { $$ = new AstFSeek{$1, $3, $5, $7}; }
        |       yD_FTELL '(' expr ')'                   { $$ = new AstFTell{$1, $3}; }
        |       yD_GLOBAL_CLOCK parenE                  { $$ = GRAMMARP->createGlobalClockParseRef($1); }
        |       yD_HIGH '(' exprOrDataType ')'          { $$ = new AstAttrOf{$1, VAttrType::DIM_HIGH, $3, nullptr}; }
        |       yD_HIGH '(' exprOrDataType ',' expr ')' { $$ = new AstAttrOf{$1, VAttrType::DIM_HIGH, $3, $5}; }
        |       yD_HYPOT '(' expr ',' expr ')'          { $$ = new AstHypotD{$1, $3, $5}; }
        |       yD_INCREMENT '(' exprOrDataType ')'     { $$ = new AstAttrOf{$1, VAttrType::DIM_INCREMENT, $3, nullptr}; }
        |       yD_INCREMENT '(' exprOrDataType ',' expr ')'    { $$ = new AstAttrOf{$1, VAttrType::DIM_INCREMENT, $3, $5}; }
        |       yD_ISUNBOUNDED '(' expr ')'             { $$ = new AstIsUnbounded{$1, $3}; }
        |       yD_ISUNKNOWN '(' expr ')'               { $$ = new AstIsUnknown{$1, $3}; }
        |       yD_ITOR '(' expr ')'                    { $$ = new AstIToRD{$1, $3}; }
        |       yD_LEFT '(' exprOrDataType ')'          { $$ = new AstAttrOf{$1, VAttrType::DIM_LEFT, $3, nullptr}; }
        |       yD_LEFT '(' exprOrDataType ',' expr ')' { $$ = new AstAttrOf{$1, VAttrType::DIM_LEFT, $3, $5}; }
        |       yD_LN '(' expr ')'                      { $$ = new AstLogD{$1, $3}; }
        |       yD_LOG10 '(' expr ')'                   { $$ = new AstLog10D{$1, $3}; }
        |       yD_LOW '(' exprOrDataType ')'           { $$ = new AstAttrOf{$1, VAttrType::DIM_LOW, $3, nullptr}; }
        |       yD_LOW '(' exprOrDataType ',' expr ')'  { $$ = new AstAttrOf{$1, VAttrType::DIM_LOW, $3, $5}; }
        |       yD_ONEHOT '(' expr ')'                  { $$ = new AstOneHot{$1, $3}; }
        |       yD_ONEHOT0 '(' expr ')'                 { $$ = new AstOneHot0{$1, $3}; }
        |       yD_PAST '(' expr ')'                    { $$ = new AstPast{$1, $3, nullptr}; }
        |       yD_PAST '(' expr ',' exprE ')'          { $$ = new AstPast{$1, $3, $5}; }
        |       yD_PAST '(' expr ',' exprE ',' exprE ')'
                        { if ($7) BBUNSUP($1, "Unsupported: $past expr2 and/or clock arguments");
                          $$ = new AstPast{$1, $3, $5}; }
        |       yD_PAST '(' expr ',' exprE ',' exprE ',' clocking_eventE ')'
                        { if ($7 || $9) BBUNSUP($1, "Unsupported: $past expr2 and/or clock arguments");
                          $$ = new AstPast{$1, $3, $5}; }
        |       yD_POW '(' expr ',' expr ')'            { $$ = new AstPowD{$1, $3, $5}; }
        |       yD_RANDOM '(' expr ')'                  { $$ = new AstRand{$1, $3, false}; }
        |       yD_RANDOM parenE                        { $$ = new AstRand{$1, nullptr, false}; }
        |       yD_REALTIME parenE                      { $$ = new AstTimeD{$1, VTimescale{VTimescale::NONE}}; }
        |       yD_REALTOBITS '(' expr ')'              { $$ = new AstRealToBits{$1, $3}; }
        |       yD_REWIND '(' expr ')'                  { $$ = new AstFSeek{$1, $3, new AstConst{$1, 0}, new AstConst{$1, 0}}; }
        |       yD_RIGHT '(' exprOrDataType ')'         { $$ = new AstAttrOf{$1, VAttrType::DIM_RIGHT, $3, nullptr}; }
        |       yD_RIGHT '(' exprOrDataType ',' expr ')'        { $$ = new AstAttrOf{$1, VAttrType::DIM_RIGHT, $3, $5}; }
        |       yD_ROSE '(' expr ')'                    { $$ = new AstRose{$1, $3, nullptr}; }
        |       yD_ROSE '(' expr ',' expr ')'           { $$ = new AstRose{$1, $3, GRAMMARP->createClockSenTree($1, $5)}; }
        |       yD_ROSE_GCLK '(' expr ')'               { $$ = new AstRose{$1, $3, GRAMMARP->createGlobalClockSenTree($1)}; }
        |       yD_RTOI '(' expr ')'                    { $$ = new AstRToIS{$1, $3}; }
        |       yD_SAMPLED '(' expr ')'                 { $$ = new AstSampled{$1, $3}; }
        |       yD_SFORMATF '(' exprDispList ')'        { $$ = new AstSFormatF{$1, AstSFormatF::NoFormat{}, $3, 'd', false}; }
        |       yD_SHORTREALTOBITS '(' expr ')'         { $$ = new AstRealToBits{$1, $3}; UNSUPREAL($1); }
        |       yD_SIGNED '(' expr ')'                  { $$ = new AstSigned{$1, $3}; }
        |       yD_SIN '(' expr ')'                     { $$ = new AstSinD{$1, $3}; }
        |       yD_SINH '(' expr ')'                    { $$ = new AstSinhD{$1, $3}; }
        |       yD_SIZE '(' exprOrDataType ')'          { $$ = new AstAttrOf{$1, VAttrType::DIM_SIZE, $3, nullptr}; }
        |       yD_SIZE '(' exprOrDataType ',' expr ')' { $$ = new AstAttrOf{$1, VAttrType::DIM_SIZE, $3, $5}; }
        |       yD_SQRT '(' expr ')'                    { $$ = new AstSqrtD{$1, $3}; }
        |       yD_SSCANF '(' expr ',' str commaVRDListE ')'    { $$ = new AstSScanF{$1, *$5, $3, $6}; }
        |       yD_STIME parenE
                        { $$ = new AstSel{$1, new AstTime{$1, VTimescale{VTimescale::NONE}}, 0, 32}; }
        |       yD_STABLE '(' expr ')'                  { $$ = new AstStable{$1, $3, nullptr}; }
        |       yD_STABLE '(' expr ',' expr ')'         { $$ = new AstStable{$1, $3, GRAMMARP->createClockSenTree($1, $5)}; }
        |       yD_STABLE_GCLK '(' expr ')'             { $$ = new AstStable{$1, $3, GRAMMARP->createGlobalClockSenTree($1)}; }
        |       yD_TAN '(' expr ')'                     { $$ = new AstTanD{$1, $3}; }
        |       yD_TANH '(' expr ')'                    { $$ = new AstTanhD{$1, $3}; }
        |       yD_TESTPLUSARGS '(' expr ')'            { $$ = new AstTestPlusArgs{$1, $3}; }
        |       yD_TIME parenE                          { $$ = new AstTime{$1, VTimescale{VTimescale::NONE}}; }
        |       yD_TIMEPRECISION                        { $$ = new AstTimePrecision{$1}; }
        |       yD_TIMEPRECISION '(' ')'                { $$ = new AstTimePrecision{$1}; }
        |       yD_TIMEPRECISION '(' idClassSel ')'     { $$ = new AstTimePrecision{$1}; DEL($3); }
        |       yD_TIMEUNIT                             { $$ = new AstTimeUnit{$1}; }
        |       yD_TIMEUNIT '(' ')'                     { $$ = new AstTimeUnit{$1}; }
        |       yD_TIMEUNIT '(' idClassSel ')'          { $$ = new AstTimeUnit{$1}; DEL($3); }
        |       yD_TYPENAME '(' exprOrDataType ')'      { $$ = new AstAttrOf{$1, VAttrType::TYPENAME, $3}; }
        |       yD_UNGETC '(' expr ',' expr ')'         { $$ = new AstFUngetC{$1, $5, $3}; }  // Arg swap to file first
        |       yD_UNPACKED_DIMENSIONS '(' exprOrDataType ')'   { $$ = new AstAttrOf{$1, VAttrType::DIM_UNPK_DIMENSIONS, $3}; }
        |       yD_UNSIGNED '(' expr ')'                { $$ = new AstUnsigned{$1, $3}; }
        |       yD_URANDOM '(' expr ')'                 { $$ = new AstRand{$1, $3, true}; }
        |       yD_URANDOM parenE                       { $$ = new AstRand{$1, nullptr, true}; }
        |       yD_URANDOM_RANGE '(' expr ')'           { $$ = new AstURandomRange{$1, $3, new AstConst{$1, 0}}; }
        |       yD_URANDOM_RANGE '(' expr ',' expr ')'  { $$ = new AstURandomRange{$1, $3, $5}; }
        |       yD_VALUEPLUSARGS '(' expr ',' expr ')'  { $$ = new AstValuePlusArgs{$1, $3, $5}; }
        ;

elaboration_system_task<nodep>: // IEEE: elaboration_system_task (1800-2009)
        //                      // TODO: These currently just make initial statements, should instead give runtime error
                elaboration_system_task_guts ';'        { $$ = new AstInitial{$<fl>1, $1}; }
        ;

elaboration_system_task_guts<nodep>:    // IEEE: part of elaboration_system_task (1800-2009)
        //                      // $fatal first argument is exit number, must be constant
                yD_INFO parenE                          { $$ = new AstElabDisplay{$1, VDisplayType::DT_INFO, nullptr}; }
        |       yD_INFO '(' exprList ')'                { $$ = new AstElabDisplay{$1, VDisplayType::DT_INFO, $3}; }
        |       yD_WARNING parenE                       { $$ = new AstElabDisplay{$1, VDisplayType::DT_WARNING, nullptr}; }
        |       yD_WARNING '(' exprList ')'             { $$ = new AstElabDisplay{$1, VDisplayType::DT_WARNING, $3}; }
        |       yD_ERROR parenE                         { $$ = new AstElabDisplay{$1, VDisplayType::DT_ERROR, nullptr}; }
        |       yD_ERROR '(' exprList ')'               { $$ = new AstElabDisplay{$1, VDisplayType::DT_ERROR, $3}; }
        |       yD_FATAL parenE                         { $$ = new AstElabDisplay{$1, VDisplayType::DT_FATAL, nullptr}; }
        |       yD_FATAL '(' expr ')'                   { $$ = new AstElabDisplay{$1, VDisplayType::DT_FATAL, nullptr}; DEL($3); }
        |       yD_FATAL '(' expr ',' exprListE ')'     { $$ = new AstElabDisplay{$1, VDisplayType::DT_FATAL, $5}; DEL($3); }
        ;

property_actual_arg<nodeExprp>:  // ==IEEE: property_actual_arg
        //                      // IEEE: property_expr
        //                      // IEEE: sequence_actual_arg
        //UNSUP pev_expr                                { $$ = $1; }
        //UNSUP remove below:
                pexpr                                   { $$ = $1; }
        //                      // IEEE: sequence_expr
        //                      // property_expr already includes sequence_expr
        ;

exprOrDataType<nodep>:          // expr | data_type: combined to prevent conflicts
                expr                                    { $$ = $1; }
        //                      // data_type includes id that overlaps expr, so special flavor
        |       data_type                               { $$ = $1; }
        //                      // not in spec, but needed for $past(sig,1,,@(posedge clk))
        //UNSUP event_control                           { }
        ;

//UNSUPexprOrDataTypeOrMinTypMax<nodep>:  // exprOrDataType or mintypmax_expression
//UNSUP         expr                                    { $$ = $1; }
//UNSUP |       expr ':' expr ':' expr                  { $$ = $3; }
//UNSUP //                      // data_type includes id that overlaps expr, so special flavor
//UNSUP |       data_type                               { $$ = $1; }
//UNSUP //                      // not in spec, but needed for $past(sig,1,,@(posedge clk))
//UNSUP |       event_control                           { $$ = $1; }
//UNSUP ;

//UNSUPexprOrDataTypeList<nodep>:
//UNSUP         exprOrDataType                          { $$ = $1; }
//UNSUP |       exprOrDataTypeList ',' exprOrDataType   { $$ = addNextNull($1, $3); }
//UNSUP ;

list_of_argumentsE<nodeExprp>:  // IEEE: [list_of_arguments]
                argsDottedList                          { $$ = $1; }
        |       argsExprListE
                        { if (VN_IS($1, Arg) && VN_CAST($1, Arg)->emptyConnectNoNext()) {
                              $1->deleteTree(); $$ = nullptr;  // Mis-created when have 'func()'
                          } else { $$ = $1; } }
        |       argsExprListE ',' argsDottedList        { $$ = addNextNull($1, $3); }
        ;

task_declaration<nodeFTaskp>:   // ==IEEE: task_declaration
                yTASK lifetimeE taskId tfGuts yENDTASK endLabelE
                        { $$ = $3; $$->addStmtsp($4); SYMP->popScope($$);
                          $$->lifetime($2);
                          GRAMMARP->endLabel($<fl>6, $$, $6); }
        ;

task_prototype<nodeFTaskp>:             // ==IEEE: task_prototype
                yTASK taskId '(' tf_port_listE ')'
                        { $$ = $2; $$->addStmtsp($4); $$->prototype(true); SYMP->popScope($$); }
        |       yTASK taskId
                        { $$ = $2; $$->prototype(true); SYMP->popScope($$); }
        ;

function_declaration<nodeFTaskp>:       // IEEE: function_declaration + function_body_declaration
                yFUNCTION lifetimeE funcId funcIsolateE tfGuts yENDFUNCTION endLabelE
                        { $$ = $3; $3->attrIsolateAssign($4); $$->addStmtsp($5);
                          $$->lifetime($2);
                          SYMP->popScope($$);
                          GRAMMARP->endLabel($<fl>7, $$, $7); }
        |       yFUNCTION lifetimeE funcIdNew funcIsolateE tfGuts yENDFUNCTION endLabelE
                        { $$ = $3; $3->attrIsolateAssign($4); $$->addStmtsp($5);
                          $$->lifetime($2);
                          SYMP->popScope($$);
                          GRAMMARP->endLabel($<fl>7, $$, $7); }
        ;

function_prototype<nodeFTaskp>: // IEEE: function_prototype
                yFUNCTION funcId '(' tf_port_listE ')'
                        { $$ = $2; $$->addStmtsp($4); $$->prototype(true); SYMP->popScope($$); }
        |       yFUNCTION funcId
                        { $$ = $2; $$->prototype(true); SYMP->popScope($$); }
        ;

class_constructor_prototype<nodeFTaskp>:        // ==IEEE: class_constructor_prototype
                yFUNCTION funcIdNew '(' tf_port_listE ')' ';'
                        { $$ = $2; $$->addStmtsp($4); $$->prototype(true); SYMP->popScope($$); }
        |       yFUNCTION funcIdNew ';'
                        { $$ = $2; $$->prototype(true); SYMP->popScope($$); }
        ;

funcIsolateE<cint>:
                /* empty */                             { $$ = 0; }
        |       yVL_ISOLATE_ASSIGNMENTS                 { $$ = 1; }
        ;

method_prototype<nodeFTaskp>:
                task_prototype                          { $$ = $1; }
        |       function_prototype                      { $$ = $1; }
        ;

lifetimeE<lifetime>:            // IEEE: [lifetime]
                /* empty */                             { $$ = VLifetime::NONE; }
        |       lifetime                                { $$ = $1; }
        ;

lifetime<lifetime>:             // ==IEEE: lifetime
        //                      // Note lifetime used by members is instead under memberQual
                ySTATIC__ETC                            { $$ = VLifetime::STATIC; }
        |       yAUTOMATIC                              { $$ = VLifetime::AUTOMATIC; }
        ;

taskId<nodeFTaskp>:
                id
                        { $$ = new AstTask{$<fl>$, *$1, nullptr};
                          SYMP->pushNewUnderNodeOrCurrent($$, nullptr); }
        //
        |       id/*interface_identifier*/ '.' id
                        { $$ = new AstTask{$<fl>$, *$3, nullptr};
                          BBUNSUP($2, "Unsupported: Out of block function declaration");
                          SYMP->pushNewUnderNodeOrCurrent($$, nullptr); }
        //
        |       packageClassScope id
                        { $$ = new AstTask{$<fl>$, *$2, nullptr};
                          $$->classOrPackagep($1);
                          SYMP->pushNewUnderNodeOrCurrent($$, $<scp>1); }
        ;

funcId<nodeFTaskp>:                     // IEEE: function_data_type_or_implicit + part of function_body_declaration
        //                      // IEEE: function_data_type_or_implicit must be expanded here to prevent conflict
        //                      // function_data_type expanded here to prevent conflicts with
        //                      // implicit_type:empty vs data_type:ID
                /**/ fIdScoped
                        { $$ = $1;
                          $$->fvarp(new AstBasicDType{$<fl>1, LOGIC_IMPLICIT});
                          SYMP->pushNewUnderNodeOrCurrent($$, $<scp>1); }
        |       signingE rangeList fIdScoped
                        { $$ = $3;
                          $$->fvarp(GRAMMARP->addRange(new AstBasicDType{$<fl>3, LOGIC_IMPLICIT, $1}, $2, true));
                          SYMP->pushNewUnderNodeOrCurrent($$, $<scp>3); }
        |       signing fIdScoped
                        { $$ = $2;
                          $$->fvarp(new AstBasicDType{$<fl>2, LOGIC_IMPLICIT, $1});
                          SYMP->pushNewUnderNodeOrCurrent($$, $<scp>2); }
        |       data_type fIdScoped
                        { $$ = $2;
                          $$->fvarp($1);
                          SYMP->pushNewUnderNodeOrCurrent($$, $<scp>2); }
        //                      // To verilator tasks are the same as void functions (we separately detect time passing)
        |       yVOID taskId
                        { $$ = $2; }
        ;

funcIdNew<nodeFTaskp>:          // IEEE: from class_constructor_declaration
                yNEW__ETC
                        { $$ = new AstFunc{$<fl>1, "new", nullptr, nullptr};
                          $$->isConstructor(true);
                          SYMP->pushNewUnder($$, nullptr); }
        |       yNEW__PAREN
                        { $$ = new AstFunc{$<fl>1, "new", nullptr, nullptr};
                          $$->isConstructor(true);
                          SYMP->pushNewUnder($$, nullptr); }
        |       packageClassScopeNoId yNEW__PAREN
                        { $$ = new AstFunc{$<fl>2, "new", nullptr, nullptr};
                          $$->classOrPackagep($1);
                          $$->isConstructor(true);
                          SYMP->pushNewUnderNodeOrCurrent($$, $<scp>1); }
        ;

fIdScoped<funcp>:               // IEEE: part of function_body_declaration/task_body_declaration
        //                      // IEEE: [ interface_identifier '.' | class_scope ] function_identifier
                id
                        { $<fl>$ = $<fl>1;
                          $<scp>$ = nullptr;
                          $$ = new AstFunc{$<fl>$, *$1, nullptr, nullptr}; }
        //
        |       id/*interface_identifier*/ '.' id
                        { $<fl>$ = $<fl>1;
                          $<scp>$ = nullptr;
                          $$ = new AstFunc{$<fl>$, *$1, nullptr, nullptr};
                          BBUNSUP($2, "Unsupported: Out of block function declaration"); }
        //
        |       packageClassScope id
                        { $<fl>$ = $<fl>1;
                          $<scp>$ = $<scp>1;
                          $$ = new AstFunc{$<fl>$, *$2, nullptr, nullptr};
                          $$->classOrPackagep($1); }
        ;

tfGuts<nodep>:
                '(' tf_port_listE ')' ';' tfBodyE       { $$ = addNextNull($2, $5); }
        |       ';' tfBodyE                             { $$ = $2; }
        ;

tfBodyE<nodep>:                 // IEEE: part of function_body_declaration/task_body_declaration
                /* empty */                             { $$ = nullptr; }
        |       tf_item_declarationList                 { $$ = $1; }
        |       tf_item_declarationList stmtList        { $$ = addNextNull($1, $2); }
        |       stmtList                                { $$ = $1; }
        ;

tf_item_declarationList<nodep>:
                tf_item_declaration                     { $$ = $1; }
        |       tf_item_declarationList tf_item_declaration     { $$ = addNextNull($1, $2); }
        ;

tf_item_declaration<nodep>:     // ==IEEE: tf_item_declaration
                block_item_declaration                  { $$ = $1; }
        |       tf_port_declaration                     { $$ = $1; }
        |       tf_item_declarationVerilator            { $$ = $1; }
        ;

tf_item_declarationVerilator<nodep>:    // Verilator extensions
                yVL_PUBLIC                              { $$ = new AstPragma{$1, VPragmaType::PUBLIC_TASK}; v3Global.dpi(true); }
        |       yVL_NO_INLINE_TASK                      { $$ = new AstPragma{$1, VPragmaType::NO_INLINE_TASK}; }
        ;

tf_port_listE<nodep>:           // IEEE: tf_port_list + empty
        //                      // Empty covered by tf_port_item
                /*empty*/
        /*mid*/         { VARRESET_LIST(UNKNOWN); VARIO(INPUT); }
        /*cont*/    tf_port_listList                    { $$ = $2; VARRESET_NONLIST(UNKNOWN); }
        ;

tf_port_listList<nodep>:        // IEEE: part of tf_port_list
                tf_port_item                            { $$ = $1; }
        |       tf_port_listList ',' tf_port_item       { $$ = addNextNull($1, $3); }
        ;

tf_port_item<nodep>:            // ==IEEE: tf_port_item
        //                      // We split tf_port_item into the type and assignment as don't know what follows a comma
                /* empty */                             { $$ = nullptr; PINNUMINC(); }  // For example a ",," port
        |       tf_port_itemFront tf_port_itemAssignment { $$ = $2; }
        |       tf_port_itemAssignment                  { $$ = $1; }
        ;

tf_port_itemFront:              // IEEE: part of tf_port_item, which has the data type
                data_type                               { VARDTYPE($1); }
        |       signingE rangeList
                        { AstNodeDType* const dtp = GRAMMARP->addRange(
                              new AstBasicDType{$2->fileline(), LOGIC_IMPLICIT, $1}, $2, true);
                          VARDTYPE(dtp); }
        |       signing
                        { AstNodeDType* const dtp = new AstBasicDType{$<fl>1, LOGIC_IMPLICIT, $1};
                          VARDTYPE(dtp); }
        |       yVAR data_type                          { VARDTYPE($2); }
        |       yVAR implicit_typeE                     { VARDTYPE($2); }
        //
        |       tf_port_itemDir /*implicit*/            { VARDTYPE(nullptr); /*default_nettype-see spec*/ }
        |       tf_port_itemDir data_type               { VARDTYPE($2); }
        |       tf_port_itemDir signingE rangeList
                        { AstNodeDType* const dtp = GRAMMARP->addRange(
                              new AstBasicDType{$3->fileline(), LOGIC_IMPLICIT, $2}, $3, true);
                          VARDTYPE(dtp); }
        |       tf_port_itemDir signing
                        { AstNodeDType* const dtp = new AstBasicDType{$<fl>2, LOGIC_IMPLICIT, $2};
                          VARDTYPE(dtp); }
        |       tf_port_itemDir yVAR data_type          { VARDTYPE($3); }
        |       tf_port_itemDir yVAR implicit_typeE     { VARDTYPE($3); }
        ;

tf_port_itemDir:                // IEEE: part of tf_port_item, direction
                port_direction                          { }  // port_direction sets VARIO
        ;

tf_port_itemAssignment<varp>:   // IEEE: part of tf_port_item, which has assignment
                id variable_dimensionListE sigAttrListE exprEqE
                        { $$ = VARDONEA($<fl>1, *$1, $2, $3); if ($4) $$->valuep($4); }
        ;

parenE:
                /* empty */                             { }
        |       '(' ')'                                 { }
        ;

//      method_call:            // ==IEEE: method_call + method_call_body
//                              // IEEE: method_call_root '.' method_identifier [ '(' list_of_arguments ')' ]
//                              //   "method_call_root '.' method_identifier" looks just like "expr '.' id"
//                              //   "method_call_root '.' method_identifier (...)" looks just like "expr '.' tf_call"
//                              // IEEE: built_in_method_call
//                              //   method_call_root not needed, part of expr resolution
//                              // What's left is below array_methodNoRoot
array_methodNoRoot<nodeFTaskRefp>:
                yOR                                     { $$ = new AstFuncRef{$1, "or", nullptr}; }
        |       yAND                                    { $$ = new AstFuncRef{$1, "and", nullptr}; }
        |       yXOR                                    { $$ = new AstFuncRef{$1, "xor", nullptr}; }
        |       yUNIQUE                                 { $$ = new AstFuncRef{$1, "unique", nullptr}; }
        ;

array_methodWith<nodeExprp>:
                array_methodNoRoot parenE               { $$ = $1; }
        |       array_methodNoRoot parenE yWITH__PAREN '(' expr ')'
                        { $$ = new AstWithParse{$3, $1, $5}; }
        |       array_methodNoRoot '(' expr ')' yWITH__PAREN '(' expr ')'
                        { $$ = new AstWithParse{$5, $1, $7}; $1->addPinsp(new AstArg{$<fl>3, "", $3}); }
        ;

dpi_import_export<nodep>:       // ==IEEE: dpi_import_export
                yIMPORT yaSTRING dpi_tf_import_propertyE dpi_importLabelE function_prototype dpi_tf_TraceInitE ';'
                        { $$ = $5;
                          if (*$4 != "") $5->cname(*$4);
                          $5->dpiContext($3 == iprop_CONTEXT);
                          $5->dpiPure($3 == iprop_PURE);
                          $5->dpiImport(true);
                          $5->dpiTraceInit($6);
                          GRAMMARP->checkDpiVer($1, *$2); v3Global.dpi(true);
                          if ($$->prettyName()[0]=='$') SYMP->reinsert($$, nullptr, $$->prettyName());  // For $SysTF overriding
                          SYMP->reinsert($$); }
        |       yIMPORT yaSTRING dpi_tf_import_propertyE dpi_importLabelE task_prototype ';'
                        { $$ = $5;
                          if (*$4 != "") $5->cname(*$4);
                          $5->dpiContext($3 == iprop_CONTEXT);
                          $5->dpiPure($3 == iprop_PURE);
                          $5->dpiImport(true);
                          $5->dpiTask(true);
                          GRAMMARP->checkDpiVer($1, *$2); v3Global.dpi(true);
                          if ($$->prettyName()[0]=='$') SYMP->reinsert($$, nullptr, $$->prettyName());  // For $SysTF overriding
                          SYMP->reinsert($$); }
        |       yEXPORT yaSTRING dpi_importLabelE yFUNCTION idAny ';'
                        { $$ = new AstDpiExport{$<fl>5, *$5, *$3};
                          GRAMMARP->checkDpiVer($1, *$2); v3Global.dpi(true); }
        |       yEXPORT yaSTRING dpi_importLabelE yTASK     idAny ';'
                        { $$ = new AstDpiExport{$<fl>5, *$5, *$3};
                          GRAMMARP->checkDpiVer($1, *$2); v3Global.dpi(true); }
        ;

dpi_importLabelE<strp>:         // IEEE: part of dpi_import_export
                /* empty */                             { static string s; $$ = &s; }
        |       idAny/*c_identifier*/ '='               { $$ = $1; $<fl>$ = $<fl>1; }
        ;

dpi_tf_import_propertyE<iprop>: // IEEE: [ dpi_function_import_property + dpi_task_import_property ]
                /* empty */                             { $$ = iprop_NONE; }
        |       yCONTEXT                                { $$ = iprop_CONTEXT; }
        |       yPURE                                   { $$ = iprop_PURE; }
        ;

dpi_tf_TraceInitE<cbool>:       // Verilator extension
                /* empty */                             { $$ = false; }
        |       yVL_TRACE_INIT_TASK                     { $$ = true; $<fl>$ = $<fl>1; }
        ;


//************************************************
// Expressions
//
// ~l~ means this is the (l)eft hand side of any operator
//     it will get replaced by "", "f" or "s"equence
// ~r~ means this is a (r)ight hand later expansion in the same statement,
//     not under parenthesis for <= disambiguation
//     it will get replaced by "", or "f"
// ~p~ means this is a (p)arenthetized expression
//     it will get replaced by "", or "s"equence

exprEqE<nodeExprp>:             // IEEE: optional '=' expression (part of param_assignment)
        //                      // constant_param_expression: '$' is in expr
                /*empty*/                               { $$ = nullptr; }
        |       '=' expr                                { $$ = $2; }
        ;

exprOrDataTypeEqE<nodep>:       // IEEE: optional '=' expression (part of param_assignment)
        //                      // constant_param_expression: '$' is in expr
                /*empty*/                               { $$ = nullptr; }
        |       '=' exprOrDataType                      { $$ = $2; }
        ;

constExpr<nodeExprp>:
                expr                                    { $$ = $1; }
        ;

exprE<nodep>:                   // IEEE: optional expression
                /*empty*/                               { $$ = nullptr; }
        |       expr                                    { $$ = $1; }
        ;

expr<nodeExprp>:                // IEEE: part of expression/constant_expression/primary
        // *SEE BELOW*          // IEEE: primary/constant_primary
        //
        //                      // IEEE: unary_operator primary
                '+' ~r~expr     %prec prUNARYARITH      { $$ = $2; }
        |       '-' ~r~expr     %prec prUNARYARITH      { $$ = new AstNegate{$1, $2}; }
        |       '!' ~r~expr     %prec prNEGATION        { $$ = new AstLogNot{$1, $2}; }
        |       '&' ~r~expr     %prec prREDUCTION       { $$ = new AstRedAnd{$1, $2}; }
        |       '~' ~r~expr     %prec prNEGATION        { $$ = new AstNot{$1, $2}; }
        |       '|' ~r~expr     %prec prREDUCTION       { $$ = new AstRedOr{$1, $2}; }
        |       '^' ~r~expr     %prec prREDUCTION       { $$ = new AstRedXor{$1, $2}; }
        |       yP_NAND ~r~expr %prec prREDUCTION       { $$ = new AstLogNot{$1, new AstRedAnd{$1, $2}}; }
        |       yP_NOR  ~r~expr %prec prREDUCTION       { $$ = new AstLogNot{$1, new AstRedOr{$1, $2}}; }
        |       yP_XNOR ~r~expr %prec prREDUCTION       { $$ = new AstLogNot{$1, new AstRedXor{$1, $2}}; }
        //
        //                      // IEEE: inc_or_dec_expression
        |       ~l~inc_or_dec_expression                { $<fl>$ = $<fl>1; $$ = $1; }
        //
        //                      // IEEE: '(' operator_assignment ')'
        //                      // Need exprScope of variable_lvalue to prevent conflict
        |       '(' ~p~exprScope '='          expr ')'
                        { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, $4},
                                               $2->cloneTreePure(true)}; }
        |       '(' ~p~exprScope yP_PLUSEQ    expr ')'
                        { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstAdd{$3, $2->cloneTreePure(true), $4}},
                                               $2->cloneTreePure(true)}; }
        |       '(' ~p~exprScope yP_MINUSEQ   expr ')'
                        { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstSub{$3, $2->cloneTreePure(true), $4}},
                                               $2->cloneTreePure(true)}; }
        |       '(' ~p~exprScope yP_TIMESEQ   expr ')'
                        { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstMul{$3, $2->cloneTreePure(true), $4}},
                                               $2->cloneTreePure(true)}; }
        |       '(' ~p~exprScope yP_DIVEQ     expr ')'
                        { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstDiv{$3, $2->cloneTreePure(true), $4}},
                                               $2->cloneTreePure(true)}; }
        |       '(' ~p~exprScope yP_MODEQ     expr ')'
                        { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstModDiv{$3, $2->cloneTreePure(true), $4}},
                                               $2->cloneTreePure(true)}; }
        |       '(' ~p~exprScope yP_ANDEQ     expr ')'
                        { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstAnd{$3, $2->cloneTreePure(true), $4}},
                                               $2->cloneTreePure(true)}; }
        |       '(' ~p~exprScope yP_OREQ      expr ')'
                        { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstOr{$3, $2->cloneTreePure(true), $4}},
                                               $2->cloneTreePure(true)}; }
        |       '(' ~p~exprScope yP_XOREQ     expr ')'
                        { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstXor{$3, $2->cloneTreePure(true), $4}},
                                               $2->cloneTreePure(true)}; }
        |       '(' ~p~exprScope yP_SLEFTEQ   expr ')'
                        { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstShiftL{$3, $2->cloneTreePure(true), $4}},
                                               $2->cloneTreePure(true)}; }
        |       '(' ~p~exprScope yP_SRIGHTEQ  expr ')'
                        { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstShiftR{$3, $2->cloneTreePure(true), $4}},
                                               $2->cloneTreePure(true)}; }
        |       '(' ~p~exprScope yP_SSRIGHTEQ expr ')'
                        { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstShiftRS{$3, $2->cloneTreePure(true), $4}},
                                               $2->cloneTreePure(true)}; }
        //
        //                      // IEEE: expression binary_operator expression
        |       ~l~expr '+' ~r~expr                     { $$ = new AstAdd{$2, $1, $3}; }
        |       ~l~expr '-' ~r~expr                     { $$ = new AstSub{$2, $1, $3}; }
        |       ~l~expr '*' ~r~expr                     { $$ = new AstMul{$2, $1, $3}; }
        |       ~l~expr '/' ~r~expr                     { $$ = new AstDiv{$2, $1, $3}; }
        |       ~l~expr '%' ~r~expr                     { $$ = new AstModDiv{$2, $1, $3}; }
        |       ~l~expr yP_EQUAL ~r~expr                { $$ = new AstEq{$2, $1, $3}; }
        |       ~l~expr yP_NOTEQUAL ~r~expr             { $$ = new AstNeq{$2, $1, $3}; }
        |       ~l~expr yP_CASEEQUAL ~r~expr            { $$ = new AstEqCase{$2, $1, $3}; }
        |       ~l~expr yP_CASENOTEQUAL ~r~expr         { $$ = new AstNeqCase{$2, $1, $3}; }
        |       ~l~expr yP_WILDEQUAL ~r~expr            { $$ = new AstEqWild{$2, $1, $3}; }
        |       ~l~expr yP_WILDNOTEQUAL ~r~expr         { $$ = new AstNeqWild{$2, $1, $3}; }
        |       ~l~expr yP_ANDAND ~r~expr               { $$ = new AstLogAnd{$2, $1, $3}; }
        |       ~l~expr yP_OROR ~r~expr                 { $$ = new AstLogOr{$2, $1, $3}; }
        |       ~l~expr yP_POW ~r~expr                  { $$ = new AstPow{$2, $1, $3}; }
        |       ~l~expr '<' ~r~expr                     { $$ = new AstLt{$2, $1, $3}; }
        |       ~l~expr '>' ~r~expr                     { $$ = new AstGt{$2, $1, $3}; }
        |       ~l~expr yP_GTE ~r~expr                  { $$ = new AstGte{$2, $1, $3}; }
        |       ~l~expr '&' ~r~expr                     { $$ = new AstAnd{$2, $1, $3}; }
        |       ~l~expr '|' ~r~expr                     { $$ = new AstOr{$2, $1, $3}; }
        |       ~l~expr '^' ~r~expr                     { $$ = new AstXor{$2, $1, $3}; }
        |       ~l~expr yP_XNOR ~r~expr                 { $$ = new AstNot{$2, new AstXor{$2, $1, $3}}; }
        |       ~l~expr yP_NOR ~r~expr                  { $$ = new AstNot{$2, new AstOr{$2, $1, $3}}; }
        |       ~l~expr yP_NAND ~r~expr                 { $$ = new AstNot{$2, new AstAnd{$2, $1, $3}}; }
        |       ~l~expr yP_SLEFT ~r~expr                { $$ = new AstShiftL{$2, $1, $3}; }
        |       ~l~expr yP_SRIGHT ~r~expr               { $$ = new AstShiftR{$2, $1, $3}; }
        |       ~l~expr yP_SSRIGHT ~r~expr              { $$ = new AstShiftRS{$2, $1, $3}; }
        |       ~l~expr yP_LTMINUSGT ~r~expr            { $$ = new AstLogEq{$2, $1, $3}; }
        //
        //                      // IEEE: expression binary_operator expression (type compare see IEEE footnote)
        |       type_referenceEq yP_CASEEQUAL type_referenceBoth     { $$ = new AstEqT{$2, $1, $3}; }
        |       type_referenceEq yP_CASENOTEQUAL type_referenceBoth  { $$ = new AstNeqT{$2, $1, $3}; }
        |       type_referenceEq yP_EQUAL type_referenceBoth         { $$ = new AstEqT{$2, $1, $3}; }
        |       type_referenceEq yP_NOTEQUAL type_referenceBoth      { $$ = new AstNeqT{$2, $1, $3}; }
        //                      // IEEE: expr yP_MINUSGT expr  (1800-2009)
        //                      // Conflicts with constraint_expression:"expr yP_MINUSGT constraint_set"
        //                      // To duplicating expr for constraints, just allow the more general form
        //                      // Later Ast processing must ignore constraint terms where inappropriate
        //UNSUP ~l~expr yP_MINUSGT constraint_set               { $<fl>$ = $<fl>1; $$ = $1 + $2 + $3; }
        //UNSUP remove line below
        |       ~l~expr yP_MINUSGT ~r~expr              { $$ = new AstLogIf{$2, $1, $3}; }
        //
        //                      // <= is special, as we need to disambiguate it with <= assignment
        //                      // We copy all of expr to fexpr and rename this token to a fake one.
        |       ~l~expr yP_LTE~f__IGNORE~ ~r~expr       { $$ = new AstLte{$2, $1, $3}; }
        //
        //                      // IEEE: conditional_expression
        |       ~l~expr '?' ~r~expr ':' ~r~expr         { $$ = new AstCond{$2, $1, $3, $5}; }
        //
        //                      // IEEE: inside_expression
        |       ~l~expr yINSIDE '{' open_range_list '}' { $$ = new AstInside{$2, $1, $4}; }
        //
        //                      // IEEE: tagged_union_expression
        //UNSUP yTAGGED id/*member*/ %prec prTAGGED             { UNSUP }
        //UNSUP yTAGGED id/*member*/ %prec prTAGGED expr        { UNSUP }
        //
        //======================// IEEE: primary/constant_primary
        //
        //                      // IEEE: primary_literal (minus string, which is handled specially)
        |       yaINTNUM                                { $$ = new AstConst{$<fl>1, *$1}; }
        |       yaFLOATNUM                              { $$ = new AstConst{$<fl>1, AstConst::RealDouble{}, $1}; }
        |       timeNumAdjusted                         { $$ = $1; }
        |       strAsInt~noStr__IGNORE~                 { $$ = $1; }
        //
        //                      // IEEE: "... hierarchical_identifier select"  see below
        //
        //                      // IEEE: empty_queue (IEEE 1800-2017 empty_unpacked_array_concatenation)
        |       '{' '}'                                 { $$ = new AstEmptyQueue{$1}; }
        //
        //                      // IEEE: concatenation/constant_concatenation
        //                      // Part of exprOkLvalue below
        //
        //                      // IEEE: multiple_concatenation/constant_multiple_concatenation
        |       '{' constExpr '{' cateList '}' '}'      { $$ = new AstReplicate{$3, $4, $2}; }
        //                      // UNSUP some other rules above
        //
        |       function_subroutine_callNoMethod        { $$ = $1; }
        //                      // method_call
        |       ~l~expr '.' function_subroutine_callNoMethod    { $$ = new AstDot{$2, false, $1, $3}; }
        //                      // method_call:array_method requires a '.'
        |       ~l~expr '.' array_methodWith            { $$ = new AstDot{$2, false, $1, $3}; }
        //
        //                      // IEEE: let_expression
        //                      // see funcRef
        //
        //                      // IEEE: '(' mintypmax_expression ')'
        |       ~noPar__IGNORE~'(' expr ')'             { $$ = $2; }
        |       ~noPar__IGNORE~'(' expr ':' expr ':' expr ')'
                        { $$ = $4; MINTYPMAXDLYUNSUP($4); DEL($2); DEL($6); }
        //                      // PSL rule
        |       '_' '(' expr ')'                        { $$ = $3; }    // Arbitrary Verilog inside PSL
        //
        //                      // IEEE: cast/constant_cast
        //                      // expanded from casting_type
        |       simple_type yP_TICK '(' expr ')'
                        { $$ = new AstCast{$1->fileline(), $4, VFlagChildDType{}, $1}; }
        |       yTYPE__ETC '(' exprOrDataType ')' yP_TICK '(' expr ')'
                        { $$ = new AstCast{$1, $7, VFlagChildDType{},
                                           new AstRefDType{$1, AstRefDType::FlagTypeOfExpr{}, $3}}; }
        |       ySIGNED yP_TICK '(' expr ')'            { $$ = new AstSigned{$1, $4}; }
        |       yUNSIGNED yP_TICK '(' expr ')'          { $$ = new AstUnsigned{$1, $4}; }
        |       ySTRING yP_TICK '(' expr ')'            { $$ = new AstCvtPackString{$1, $4}; }
        |       yCONST__ETC yP_TICK '(' expr ')'        { $$ = $4; }  // Not linting const presently
        //                      // Spec only allows primary with addition of a type reference
        //                      // We'll be more general, and later assert LHS was a type.
        |       ~l~expr yP_TICK '(' expr ')'            { $$ = new AstCastParse{$2, $4, $1}; }
        //
        //                      // IEEE: assignment_pattern_expression
        //                      // IEEE: streaming_concatenation
        //                      // See exprOkLvalue
        //
        //                      // IEEE: sequence_method_call
        //                      // Indistinguishable from function_subroutine_call:method_call
        //
        |       '$'                                     { $$ = new AstUnbounded{$<fl>1}; }
        |       yNULL                                   { $$ = new AstConst{$1, AstConst::Null{}}; }
        //                      // IEEE: yTHIS
        //                      // See exprScope
        //
        //----------------------
        //
        //                      // Part of expr that may also be used as lvalue
        |       ~l~exprOkLvalue                         { $$ = $1; }
        //
        //----------------------
        //
        //                      // IEEE: cond_predicate - here to avoid reduce problems
        //                      // Note expr includes cond_pattern
        |       ~l~expr yP_ANDANDAND ~r~expr            { $$ = new AstConst{$2, AstConst::BitFalse{}};
                                                          BBUNSUP($<fl>2, "Unsupported: &&& expression"); }
        //
        //                      // IEEE: cond_pattern - here to avoid reduce problems
        //                      // "expr yMATCHES pattern"
        //                      // IEEE: pattern - expanded here to avoid conflicts
        |       ~l~expr yMATCHES patternNoExpr          { $$ = new AstConst{$2, AstConst::BitFalse{}};
                                                          BBUNSUP($<fl>2, "Unsupported: matches operator"); }
        |       ~l~expr yMATCHES ~r~expr                { $$ = new AstConst{$2, AstConst::BitFalse{}};
                                                          BBUNSUP($<fl>2, "Unsupported: matches operator"); }
        //
        //                      // IEEE: expression_or_dist - here to avoid reduce problems
        //                      // "expr yDIST '{' dist_list '}'"
        |       ~l~expr yDIST '{' dist_list '}'         { $$ = $1; BBUNSUP($2, "Unsupported: dist"); }
        ;

fexpr<nodeExprp>:                   // For use as first part of statement (disambiguates <=)
                BISONPRE_COPY(expr,{s/~l~/f/g; s/~r~/f/g; s/~f__IGNORE~/__IGNORE/g;})   // {copied}
        ;

//UNSUPpev_expr<nodeExprp>:  // IEEE: event_expression
//UNSUP //                      // for yOR/, see event_expression
//UNSUP //
//UNSUP //                      // IEEE: [ edge_identifier ] expression [ yIFF expression ]
//UNSUP //                      // expr alone see below
//UNSUP         senitemEdge                             { $$ = $1; }
//UNSUP |       ev_expr yIFF expr                       { }
//UNSUP //
//UNSUP //                      // IEEE: sequence_instance [ yIFF expression ]
//UNSUP //                      // seq_inst is in expr, so matches senitem rule above
//UNSUP //
//UNSUP //                      // IEEE: event_expression yOR event_expression
//UNSUP |       ev_expr yOR ev_expr                     { }
//UNSUP //                      // IEEE: event_expression ',' event_expression
//UNSUP //                      // See real event_expression rule
//UNSUP //
//UNSUP //---------------------
//UNSUP //                      // IEEE: expr
//UNSUP |       BISONPRE_COPY(expr,{s/~l~/ev_/g; s/~r~/ev_/g; s/~p~/ev_/g; s/~noPar__IGNORE~'.'/yP_PAR__IGNORE /g;})  // {copied}
//UNSUP //
//UNSUP //                      // IEEE: '(' event_expression ')'
//UNSUP //                      // expr:'(' x ')' conflicts with event_expression:'(' event_expression ')'
//UNSUP //                      // so we use a special expression class
//UNSUP |       '(' event_expression ')'                { $<fl>$ = $<fl>1; $$ = "(...)"; }
//UNSUP //                      // IEEE: From normal expr: '(' expr ':' expr ':' expr ')'
//UNSUP //                      // But must avoid conflict
//UNSUP |       '(' event_expression ':' expr ':' expr ')'      { $<fl>$ = $<fl>1; $$ = "(...)"; }
//UNSUP ;

exprNoStr<nodeExprp>:               // expression with string removed
                BISONPRE_COPY(expr,{s/~noStr__IGNORE~/Ignore/g;})       // {copied}
        ;

exprOkLvalue<nodeExprp>:            // expression that's also OK to use as a variable_lvalue
                ~l~exprScope                            { $$ = $1; }
        //                      // IEEE: concatenation/constant_concatenation
        //                      // Replicate(1) required as otherwise "{a}" would not be self-determined
        |       '{' cateList '}'                        { $$ = new AstReplicate{$1, $2, 1}; }
        |       '{' cateList '}' '[' expr ']'           { $$ = new AstSelBit{$4, new AstReplicate{$1, $2, 1}, $5}; }
        |       '{' cateList '}' '[' constExpr ':' constExpr ']'
                                                        { $$ = new AstSelExtract{$4, new AstReplicate{$1, $2, 1}, $5, $7}; }
        |       '{' cateList '}' '[' expr yP_PLUSCOLON constExpr ']'
                                                        { $$ = new AstSelPlus{$4, new AstReplicate{$1, $2, 1}, $5, $7}; }
        |       '{' cateList '}' '[' expr yP_MINUSCOLON constExpr ']'
                                                        { $$ = new AstSelMinus{$4, new AstReplicate{$1, $2, 1}, $5, $7}; }
        //                      // IEEE: assignment_pattern_expression
        //                      // IEEE: [ assignment_pattern_expression_type ] == [ ps_type_id /ps_paremeter_id/data_type]
        //                      // We allow more here than the spec requires
        //UNSUP ~l~exprScope assignment_pattern         { UNSUP }
        |       data_type assignment_pattern            { $$ = $2; if ($2) $2->childDTypep($1); }
        |       assignment_pattern                      { $$ = $1; }
        //
        |       streaming_concatenation                 { $$ = $1; }
        ;

fexprOkLvalue<nodeExprp>:           // exprOkLValue, For use as first part of statement (disambiguates <=)
                BISONPRE_COPY(exprOkLvalue,{s/~l~/f/g}) // {copied}
        ;

sexprOkLvalue<nodeExprp>:  // exprOkLValue, For use by sequence_expr
                BISONPRE_COPY(exprOkLvalue,{s/~l~/s/g}) // {copied}
        ;

pexprOkLvalue<nodeExprp>:  // exprOkLValue, For use by property_expr
                BISONPRE_COPY(exprOkLvalue,{s/~l~/p/g}) // {copied}
        ;

//UNSUPev_exprOkLvalue<nodeExprp>:  // exprOkLValue, For use by ev_expr
//UNSUP         BISONPRE_COPY(exprOkLvalue,{s/~l~/ev_/g})       // {copied}
//UNSUP ;

//UNSUPpev_exprOkLvalue<nodeExprp>:  // exprOkLValue, For use by ev_expr
//UNSUP         BISONPRE_COPY(exprOkLvalue,{s/~l~/pev_/g})      // {copied}
//UNSUP ;

fexprLvalue<nodeExprp>:             // For use as first part of statement (disambiguates <=)
                fexprOkLvalue                           { $<fl>$ = $<fl>1; $$ = $1; }
        ;

exprScope<nodeExprp>:               // scope and variable for use to inside an expression
        //                      // Here we've split method_call_root | implicit_class_handle | class_scope | package_scope
        //                      // from the object being called and let expr's "." deal with resolving it.
        //                      // (note method_call_root was simplified to require a primary in 1800-2009)
        //
        //                      // IEEE: [ implicit_class_handle . | class_scope | package_scope ] hierarchical_identifier select
        //                      // Or method_call_body without parenthesis
        //                      // See also varRefClassBit, which is the non-expr version of most of this
                yTHIS                                   { $$ = new AstParseRef{$<fl>1, VParseRefExp::PX_ROOT, "this"}; }
        |       yD_ROOT                                 { $$ = new AstParseRef{$<fl>1, VParseRefExp::PX_ROOT, "$root"}; }
        |       idArrayed                               { $$ = $1; }
        |       packageClassScope idArrayed             { $$ = AstDot::newIfPkg($2->fileline(), $1, $2); }
        |       ~l~expr '.' idArrayed                   { $$ = new AstDot{$<fl>2, false, $1, $3}; }
        //                      // expr below must be a "yTHIS"
        |       ~l~expr '.' ySUPER                      { $$ = $1; BBUNSUP($3, "Unsupported: super"); }
        //                      // Part of implicit_class_handle
        |       ySUPER                                  { $$ = new AstParseRef{$<fl>1, VParseRefExp::PX_ROOT, "super"}; }
        ;

fexprScope<nodeExprp>:              // exprScope, For use as first part of statement (disambiguates <=)
                BISONPRE_COPY(exprScope,{s/~l~/f/g})    // {copied}
        ;

sexprScope<nodeExprp>:  // exprScope, For use by sequence_expr
                BISONPRE_COPY(exprScope,{s/~l~/s/g})    // {copied}
        ;

pexprScope<nodeExprp>:  // exprScope, For use by property_expr
                BISONPRE_COPY(exprScope,{s/~l~/p/g})    // {copied}
        ;

//UNSUPev_exprScope<nodeExprp>:  // exprScope, For use by ev_expr
//UNSUP         BISONPRE_COPY(exprScope,{s/~l~/ev_/g})  // {copied}
//UNSUP ;

//UNSUPpev_exprScope<nodeExprp>:  // exprScope, For use by ev_expr
//UNSUP         BISONPRE_COPY(exprScope,{s/~l~/pev_/g}) // {copied}
//UNSUP ;

// PLI calls exclude "" as integers, they're strings
// For $c("foo","bar") we want "bar" as a string, not a Verilog integer.
exprStrText<nodep>:
                exprNoStr                               { $$ = $1; }
        |       strAsText                               { $$ = $1; }
        ;

exprTypeCompare<nodeExprp>:
                expr                                    { $$ = $1; }
        |       type_referenceBoth                      { $$ = $1; }
        ;

cStrList<nodep>:
                exprStrText                             { $$ = $1; }
        |       exprStrText ',' cStrList                { $$ = $1->addNext($3); }
        ;

cateList<nodeExprp>:
        //                      // Not just 'expr' to prevent conflict via stream_concOrExprOrType
                stream_expression                       { $$ = $1; }
        |       cateList ',' stream_expression          { $$ = new AstConcat{$2, $1, $3}; }
        ;

exprListE<nodeExprp>:
                /* empty */                             { $$ = nullptr; }
        |       exprList                                { $$ = $1; }
        ;

exprList<nodeExprp>:
                expr                                    { $$ = $1; }
        |       exprList ',' expr                       { $$ = $1->addNext($3); }
        ;

exprDispList<nodeExprp>:            // exprList for within $display
                expr                                    { $$ = $1; }
        |       exprDispList ',' expr                   { $$ = $1->addNext($3); }
        //                      // ,, creates a space in $display
        |       exprDispList ',' /*empty*/
                        { $$ = $1->addNext(new AstConst{$<fl>2, AstConst::VerilogStringLiteral{}, " "}); }
        ;

vrdList<nodep>:
                idClassSel                              { $$ = $1; }
        |       vrdList ',' idClassSel                  { $$ = $1->addNext($3); }
        ;

commasE:
                /* empty */                             { } /* ignored */
        |       ',' commasE                             { } /* ignored */
        ;

commaVRDListE<nodep>:
                /* empty */                             { $$ = nullptr; }
        |       ',' vrdList                             { $$ = $2; }
        ;

argsExprList<nodeExprp>:        // IEEE: part of list_of_arguments (used where ,, isn't legal)
                expr                                    { $$ = $1; }
        |       argsExprList ',' expr                   { $$ = $1->addNext($3); }
        ;

argsExprListE<nodeExprp>:       // IEEE: part of list_of_arguments
                argsExprOneE                            { $$ = $1; }
        |       argsExprListE ',' argsExprOneE          { $$ = $1->addNext($3); }
        ;

//UNSUPpev_argsExprListE<nodeExprp>:  // IEEE: part of list_of_arguments - pev_expr at bottom
//UNSUP         pev_argsExprOneE                        { $$ = $1; }
//UNSUP |       pev_argsExprListE ',' pev_argsExprOneE  { $$ = addNextNull($1, $3); }
//UNSUP ;

argsExprOneE<nodeExprp>:        // IEEE: part of list_of_arguments
                /*empty*/                               { $$ = new AstArg{CRELINE(), "", nullptr}; }
        |       expr                                    { $$ = new AstArg{$1->fileline(), "", $1}; }
        ;

//UNSUPpev_argsExprOneE<nodeExprp>:  // IEEE: part of list_of_arguments - pev_expr at bottom
//UNSUP         /*empty*/                               { $$ = nullptr; }       // ,, is legal in list_of_arguments
//UNSUP |       pev_expr                                { $$ = $1; }
//UNSUP ;

argsDottedList<nodeExprp>:      // IEEE: part of list_of_arguments
                argsDotted                              { $$ = $1; }
        |       argsDottedList ',' argsDotted           { $$ = addNextNull($1, $3); }
        ;

//UNSUPpev_argsDottedList<nodeExprp>:  // IEEE: part of list_of_arguments - pev_expr at bottom
//UNSUP         pev_argsDotted                          { $$ = $1; }
//UNSUP |       pev_argsDottedList ',' pev_argsDotted   { $$ = addNextNull($1, $3); }
//UNSUP ;

argsDotted<nodeExprp>:          // IEEE: part of list_of_arguments
                '.' idAny '(' ')'                       { $$ = new AstArg{$<fl>2, *$2, nullptr}; }
        |       '.' idAny '(' expr ')'                  { $$ = new AstArg{$<fl>2, *$2, $4}; }
        ;

//UNSUPpev_argsDotted<nodeExprp>:  // IEEE: part of list_of_arguments - pev_expr at bottom
//UNSUP         '.' idAny '(' ')'                       { $$ = new AstArg{$<fl>2, *$2, nullptr}; }
//UNSUP |       '.' idAny '(' pev_expr ')'              { $$ = new AstArg{$<fl>2, *$2, $4}; }
//UNSUP ;

streaming_concatenation<nodeStreamp>: // ==IEEE: streaming_concatenation
        //                      // Need to disambiguate {<< expr-{ ... expr-} stream_concat }
        //                      // From                 {<< stream-{ ... stream-} }
        //                      // Likewise simple_type's idScoped from constExpr's idScope
        //                      // Thus we allow always any two operations.  Sorry
        //                      // IEEE: "'{' yP_SL/R             stream_concatenation '}'"
        //                      // IEEE: "'{' yP_SL/R simple_type stream_concatenation '}'"
        //                      // IEEE: "'{' yP_SL/R constExpr   stream_concatenation '}'"
                '{' yP_SLEFT  stream_concatenation '}'
                        { $$ = new AstStreamL{$2, $3, new AstConst{$2, 1}}; }
        |       '{' yP_SRIGHT stream_concatenation '}'
                        { $$ = new AstStreamR{$2, $3, new AstConst{$2, 1}}; }
        |       '{' yP_SLEFT  stream_expressionOrDataType stream_concatenation '}'
                        { AstNodeExpr* const bitsp = VN_IS($3, NodeExpr) ? VN_AS($3, NodeExpr)
                                                                         : new AstAttrOf{$1, VAttrType::DIM_BITS, $3};
                          $$ = new AstStreamL{$2, $4, bitsp}; }
        |       '{' yP_SRIGHT stream_expressionOrDataType stream_concatenation '}'
                        { AstNodeExpr* const bitsp = VN_IS($3, NodeExpr) ? VN_AS($3, NodeExpr)
                                                                          : new AstAttrOf{$1, VAttrType::DIM_BITS, $3};
                          $$ = new AstStreamR{$2, $4, bitsp}; }
        ;

stream_concatenation<nodeExprp>:    // ==IEEE: stream_concatenation
        //                      // '{' { stream_expression } '}'
                '{' cateList '}'                        { $$ = $2; }
        ;

stream_expression<nodeExprp>:   // ==IEEE: stream_expression
        //                      // IEEE: array_range_expression expanded below
                expr                                    { $$ = $1; }
        |       expr yWITH__BRA '[' expr ']'
                        { $$ = $1; BBUNSUP($2, "Unsupported: with[] stream expression"); }
        |       expr yWITH__BRA '[' expr ':' expr ']'
                        { $$ = $1; BBUNSUP($2, "Unsupported: with[] stream expression"); }
        |       expr yWITH__BRA '[' expr yP_PLUSCOLON  expr ']'
                        { $$ = $1; BBUNSUP($2, "Unsupported: with[] stream expression"); }
        |       expr yWITH__BRA '[' expr yP_MINUSCOLON expr ']'
                        { $$ = $1; BBUNSUP($2, "Unsupported: with[] stream expression"); }
        ;

stream_expressionOrDataType<nodep>:     // IEEE: from streaming_concatenation
                exprOrDataType                          { $$ = $1; }
        |       expr yWITH__BRA '[' expr ']'
                        { $$ = $1; BBUNSUP($2, "Unsupported: with[] stream expression"); }
        |       expr yWITH__BRA '[' expr ':' expr ']'
                        { $$ = $1; BBUNSUP($2, "Unsupported: with[] stream expression"); }
        |       expr yWITH__BRA '[' expr yP_PLUSCOLON  expr ']'
                        { $$ = $1; BBUNSUP($2, "Unsupported: with[] stream expression"); }
        |       expr yWITH__BRA '[' expr yP_MINUSCOLON expr ']'
                        { $$ = $1; BBUNSUP($2, "Unsupported: with[] stream expression"); }
        ;

//************************************************
// Let

letId<letp>:  // IEEE: pert of let_declaration
                idAny/*let_identifieer*/
                        { $<fl>$ = $<fl>1;
                          $<scp>$ = nullptr;
                          $$ = new AstLet{$<fl>$, *$1};
                          SYMP->pushNewUnderNodeOrCurrent($$, $<scp>$); }
        ;

let_declaration<letp>:  // IEEE: let_declaration
                yLET letId '=' expr ';'
                        { $$ = $2;
                          $$->addStmtsp(new AstStmtExpr{$1, $4});
                          SYMP->popScope($2); }
        |       yLET letId '(' let_port_listE ')' '=' expr ';'
                        { $$ = $2;
                          $$->addStmtsp(new AstStmtExpr{$1, $7});
                          $$->addStmtsp($4);
                          SYMP->popScope($2); }
        ;

let_port_listE<nodep>:   // IEEE: [ let_port_list ]
                /*empty*/                               { $$ = nullptr; }
        |       /*emptyStart*/
        /*mid*/         { VARRESET_LIST(UNKNOWN); VARIO(INOUT); }
        /*cont*/  let_port_list                         { $$ = $2; VARRESET_NONLIST(UNKNOWN); }
        ;

let_port_list<nodep>:   // IEEE: let_port_list
                let_port_item                           { $$ = $1; }
        |       let_port_list ',' let_port_item         { $$ = addNextNull($1, $3); }
        ;

let_port_item<varp>:  // IEEE: let_port_Item
        //                      // IEEE: Expanded let_formal_type
                yUNTYPED idAny/*formal_port_identifier*/ variable_dimensionListE exprEqE
                        { $$ = new AstVar{$<fl>2, VVarType::PORT, *$2, VFlagChildDType{},
                                          new AstBasicDType{$<fl>2, LOGIC_IMPLICIT}};
                          $$->direction(VDirection::INOUT);
                          $$->lifetime(VLifetime::AUTOMATIC);
                          if ($4) $$->valuep($4);
                          PINNUMINC(); }
        |       data_type id/*formal_port_identifier*/ variable_dimensionListE exprEqE
                        { BBUNSUP($<fl>1, "Unsupported: let typed ports");
                          $$ = new AstVar{$<fl>2, VVarType::PORT, *$2, VFlagChildDType{},
                                          new AstBasicDType{$<fl>2, LOGIC_IMPLICIT}};
                          $$->direction(VDirection::INOUT);
                          $$->lifetime(VLifetime::AUTOMATIC);
                          if ($4) $$->valuep($4);
                          PINNUMINC(); }
        |       implicit_typeE id/*formal_port_identifier*/ variable_dimensionListE exprEqE
                        { if ($1) BBUNSUP($<fl>1, "Unsupported: let typed ports");
                          $$ = new AstVar{$<fl>2, VVarType::PORT, *$2, VFlagChildDType{},
                                          new AstBasicDType{$<fl>2, LOGIC_IMPLICIT}};
                          $$->direction(VDirection::INOUT);
                          $$->lifetime(VLifetime::AUTOMATIC);
                          if ($4) $$->valuep($4);
                          PINNUMINC(); }
        ;

//************************************************
// Gate declarations

gateDecl<nodep>:
                yBUF    driveStrengthE delay_controlE gateBufList ';'     { $$ = $4; STRENGTHUNSUP($2); DELAY_LIST($3, $4); }
        |       yBUFIF0 driveStrengthE delay_controlE gateBufif0List ';'  { $$ = $4; STRENGTHUNSUP($2); DELAY_LIST($3, $4); }
        |       yBUFIF1 driveStrengthE delay_controlE gateBufif1List ';'  { $$ = $4; STRENGTHUNSUP($2); DELAY_LIST($3, $4); }
        |       yNOT    driveStrengthE delay_controlE gateNotList ';'     { $$ = $4; STRENGTH_LIST($4, $2, AssignW); DELAY_LIST($3, $4); }
        |       yNOTIF0 driveStrengthE delay_controlE gateNotif0List ';'  { $$ = $4; STRENGTHUNSUP($2); DELAY_LIST($3, $4); }
        |       yNOTIF1 driveStrengthE delay_controlE gateNotif1List ';'  { $$ = $4; STRENGTHUNSUP($2); DELAY_LIST($3, $4); }
        |       yAND    driveStrengthE delay_controlE gateAndList ';'     { $$ = $4; STRENGTH_LIST($4, $2, AssignW); DELAY_LIST($3, $4); }
        |       yNAND   driveStrengthE delay_controlE gateNandList ';'    { $$ = $4; STRENGTH_LIST($4, $2, AssignW); DELAY_LIST($3, $4); }
        |       yOR     driveStrengthE delay_controlE gateOrList ';'      { $$ = $4; STRENGTH_LIST($4, $2, AssignW); DELAY_LIST($3, $4); }
        |       yNOR    driveStrengthE delay_controlE gateNorList ';'     { $$ = $4; STRENGTH_LIST($4, $2, AssignW); DELAY_LIST($3, $4); }
        |       yXOR    driveStrengthE delay_controlE gateXorList ';'     { $$ = $4; STRENGTH_LIST($4, $2, AssignW); DELAY_LIST($3, $4); }
        |       yXNOR   driveStrengthE delay_controlE gateXnorList ';'    { $$ = $4; STRENGTH_LIST($4, $2, AssignW); DELAY_LIST($3, $4); }
        |       yPULLUP   delay_controlE gatePullupList ';'     { $$ = $3; DELAY_LIST($2, $3); }
        |       yPULLDOWN delay_controlE gatePulldownList ';'   { $$ = $3; DELAY_LIST($2, $3); }
        |       yNMOS     delay_controlE gateBufif1List ';'     { $$ = $3; DELAY_LIST($2, $3); }
        |       yPMOS     delay_controlE gateBufif0List ';'     { $$ = $3; DELAY_LIST($2, $3); }
        //
        |       yTRAN delay_controlE gateUnsupList ';'          { $$ = $3; GATEUNSUP($3, "tran"); }
        |       yRCMOS delay_controlE gateUnsupList ';'         { $$ = $3; GATEUNSUP($3, "rcmos"); }
        |       yCMOS delay_controlE gateUnsupList ';'          { $$ = $3; GATEUNSUP($3, "cmos"); }
        |       yRNMOS delay_controlE gateUnsupList ';'         { $$ = $3; GATEUNSUP($3, "rmos"); }
        |       yRPMOS delay_controlE gateUnsupList ';'         { $$ = $3; GATEUNSUP($3, "pmos"); }
        |       yRTRAN delay_controlE gateUnsupList ';'         { $$ = $3; GATEUNSUP($3, "rtran"); }
        |       yRTRANIF0 delay_controlE gateUnsupList ';'      { $$ = $3; GATEUNSUP($3, "rtranif0"); }
        |       yRTRANIF1 delay_controlE gateUnsupList ';'      { $$ = $3; GATEUNSUP($3, "rtranif1"); }
        |       yTRANIF0 delay_controlE gateUnsupList ';'       { $$ = $3; GATEUNSUP($3, "tranif0"); }
        |       yTRANIF1 delay_controlE gateUnsupList ';'       { $$ = $3; GATEUNSUP($3, "tranif1"); }
        ;

gateBufList<nodep>:
                gateBuf                                 { $$ = $1; }
        |       gateBufList ',' gateBuf                 { $$ = $1->addNext($3); }
        ;
gateBufif0List<nodep>:
                gateBufif0                              { $$ = $1; }
        |       gateBufif0List ',' gateBufif0           { $$ = $1->addNext($3); }
        ;
gateBufif1List<nodep>:
                gateBufif1                              { $$ = $1; }
        |       gateBufif1List ',' gateBufif1           { $$ = $1->addNext($3); }
        ;
gateNotList<nodep>:
                gateNot                                 { $$ = $1; }
        |       gateNotList ',' gateNot                 { $$ = $1->addNext($3); }
        ;
gateNotif0List<nodep>:
                gateNotif0                              { $$ = $1; }
        |       gateNotif0List ',' gateNotif0           { $$ = $1->addNext($3); }
        ;
gateNotif1List<nodep>:
                gateNotif1                              { $$ = $1; }
        |       gateNotif1List ',' gateNotif1           { $$ = $1->addNext($3); }
        ;
gateAndList<nodep>:
                gateAnd                                 { $$ = $1; }
        |       gateAndList ',' gateAnd                 { $$ = $1->addNext($3); }
        ;
gateNandList<nodep>:
                gateNand                                { $$ = $1; }
        |       gateNandList ',' gateNand               { $$ = $1->addNext($3); }
        ;
gateOrList<nodep>:
                gateOr                                  { $$ = $1; }
        |       gateOrList ',' gateOr                   { $$ = $1->addNext($3); }
        ;
gateNorList<nodep>:
                gateNor                                 { $$ = $1; }
        |       gateNorList ',' gateNor                 { $$ = $1->addNext($3); }
        ;
gateXorList<nodep>:
                gateXor                                 { $$ = $1; }
        |       gateXorList ',' gateXor                 { $$ = $1->addNext($3); }
        ;
gateXnorList<nodep>:
                gateXnor                                { $$ = $1; }
        |       gateXnorList ',' gateXnor               { $$ = $1->addNext($3); }
        ;
gatePullupList<nodep>:
                gatePullup                              { $$ = $1; }
        |       gatePullupList ',' gatePullup           { $$ = $1->addNext($3); }
        ;
gatePulldownList<nodep>:
                gatePulldown                            { $$ = $1; }
        |       gatePulldownList ',' gatePulldown       { $$ = $1->addNext($3); }
        ;
gateUnsupList<nodep>:
                gateUnsup                               { $$ = $1; }
        |       gateUnsupList ',' gateUnsup             { $$ = $1->addNext($3); }
        ;

gateRangeE<nodep>:
                instRangeListE                          { $$ = $1; GATERANGE(GRAMMARP->scrubRange($1)); }
        ;

gateBuf<nodep>:
                gateFront variable_lvalue ',' exprList ')'
                        { AstNodeExpr* inp = $4;
                          while (inp->nextp()) inp = VN_AS(inp->nextp(), NodeExpr);
                          $$ = new AstAssignW{$<fl>1, $2, GRAMMARP->createGatePin(inp->cloneTree(false))};
                          for (AstNodeExpr* outp = $4; outp->nextp(); outp = VN_CAST(outp->nextp(), NodeExpr)) {
                              $$->addNext(new AstAssignW{$<fl>1, outp->cloneTree(false),
                                                         GRAMMARP->createGatePin(inp->cloneTree(false))});
                          }
                          DEL($1); DEL($4); }
        ;
gateNot<nodep>:
                gateFront variable_lvalue ',' exprList ')'
                        { AstNodeExpr* inp = $4;
                          while (inp->nextp()) inp = VN_AS(inp->nextp(), NodeExpr);
                          $$ = new AstAssignW{$<fl>1, $2, new AstNot{$<fl>1,
                                                                 GRAMMARP->createGatePin(inp->cloneTree(false))}};
                          for (AstNodeExpr* outp = $4; outp->nextp(); outp = VN_CAST(outp->nextp(), NodeExpr)) {
                              $$->addNext(new AstAssignW{$<fl>1, outp->cloneTree(false),
                                                         new AstNot{$<fl>1,
                                                                 GRAMMARP->createGatePin(inp->cloneTree(false))}});
                          }
                          DEL($1); DEL($4); }
        ;
gateBufif0<nodep>:
                gateFront variable_lvalue ',' gatePinExpr ',' gatePinExpr ')'
                        { $$ = new AstAssignW{$<fl>1, $2, new AstBufIf1{$<fl>1, new AstNot{$<fl>1, $6}, $4}}; DEL($1); }
        ;
gateBufif1<nodep>:
                gateFront variable_lvalue ',' gatePinExpr ',' gatePinExpr ')'
                        { $$ = new AstAssignW{$<fl>1, $2, new AstBufIf1{$<fl>1, $6, $4}}; DEL($1); }
        ;
gateNotif0<nodep>:
                gateFront variable_lvalue ',' gatePinExpr ',' gatePinExpr ')'
                        { $$ = new AstAssignW{$<fl>1, $2, new AstBufIf1{$<fl>1, new AstNot{$<fl>1, $6},
                                                                        new AstNot{$<fl>1, $4}}}; DEL($1); }
        ;
gateNotif1<nodep>:
                gateFront variable_lvalue ',' gatePinExpr ',' gatePinExpr ')'
                        { $$ = new AstAssignW{$<fl>1, $2, new AstBufIf1{$<fl>1, $6, new AstNot{$<fl>1, $4}}}; DEL($1); }
        ;
gateAnd<nodep>:
                gateFront variable_lvalue ',' gateAndPinList ')'
                        { $$ = new AstAssignW{$<fl>1, $2, $4}; DEL($1); }
        ;
gateNand<nodep>:
                gateFront variable_lvalue ',' gateAndPinList ')'
                        { $$ = new AstAssignW{$<fl>1, $2, new AstNot{$<fl>1, $4}}; DEL($1); }
        ;
gateOr<nodep>:
                gateFront variable_lvalue ',' gateOrPinList ')'
                        { $$ = new AstAssignW{$<fl>1, $2, $4}; DEL($1); }
        ;
gateNor<nodep>:
                gateFront variable_lvalue ',' gateOrPinList ')'
                        { $$ = new AstAssignW{$<fl>1, $2, new AstNot{$<fl>1, $4}}; DEL($1); }
        ;
gateXor<nodep>:
                gateFront variable_lvalue ',' gateXorPinList ')'
                        { $$ = new AstAssignW{$<fl>1, $2, $4}; DEL($1); }
        ;
gateXnor<nodep>:
                gateFront variable_lvalue ',' gateXorPinList ')'
                        { $$ = new AstAssignW{$<fl>1, $2, new AstNot{$<fl>1, $4}}; DEL($1); }
        ;
gatePullup<nodep>:
                gateFront variable_lvalue ')'           { $$ = new AstPull{$<fl>1, $2, true}; DEL($1); }
        ;
gatePulldown<nodep>:
                gateFront variable_lvalue ')'           { $$ = new AstPull{$<fl>1, $2, false}; DEL($1); }
        ;
gateUnsup<nodep>:
                gateFront gateUnsupPinList ')'          { $$ = new AstImplicit{$<fl>1, $2}; DEL($1); }
        ;

gateFront<nodep>:
                id/*gate*/ gateRangeE '('               { $$ = $2; $<fl>$ = $<fl>1; }
        |       gateRangeE '('                          { $$ = $1; $<fl>$ = $<fl>2; }
        ;

gateAndPinList<nodeExprp>:
                gatePinExpr                             { $$ = $1; }
        |       gateAndPinList ',' gatePinExpr          { $$ = new AstAnd{$2, $1, $3}; }
        ;
gateOrPinList<nodeExprp>:
                gatePinExpr                             { $$ = $1; }
        |       gateOrPinList ',' gatePinExpr           { $$ = new AstOr{$2, $1, $3}; }
        ;
gateXorPinList<nodeExprp>:
                gatePinExpr                             { $$ = $1; }
        |       gateXorPinList ',' gatePinExpr          { $$ = new AstXor{$2, $1, $3}; }
        ;
gateUnsupPinList<nodeExprp>:
                gatePinExpr                             { $$ = $1; }
        |       gateUnsupPinList ',' gatePinExpr        { $$ = $1->addNext($3); }
        ;

gatePinExpr<nodeExprp>:
                expr                                    { $$ = GRAMMARP->createGatePin($1); }
        ;

strength0<strength>:
                ySUPPLY0                                { $$ = VStrength::SUPPLY; }
        |       ySTRONG0                                { $$ = VStrength::STRONG; }
        |       yPULL0                                  { $$ = VStrength::PULL; }
        |       yWEAK0                                  { $$ = VStrength::WEAK; }
        ;

strength1<strength>:
                ySUPPLY1                                { $$ = VStrength::SUPPLY; }
        |       ySTRONG1                                { $$ = VStrength::STRONG; }
        |       yPULL1                                  { $$ = VStrength::PULL; }
        |       yWEAK1                                  { $$ = VStrength::WEAK; }
        ;

driveStrengthE<nodep>:
                /* empty */                             { $$ = nullptr; }
        |       driveStrength                           { $$ = $1; }
        ;


driveStrength<nodep>:
                yP_PAR__STRENGTH strength0 ',' strength1 ')' { $$ = new AstStrengthSpec{$1, $2, $4}; }
        |       yP_PAR__STRENGTH strength1 ',' strength0 ')' { $$ = new AstStrengthSpec{$1, $4, $2}; }
        |       yP_PAR__STRENGTH strength0 ',' yHIGHZ1 ')' { BBUNSUP($<fl>4, "Unsupported: highz strength"); }
        |       yP_PAR__STRENGTH strength1 ',' yHIGHZ0 ')' { BBUNSUP($<fl>4, "Unsupported: highz strength"); }
        |       yP_PAR__STRENGTH yHIGHZ0 ',' strength1 ')' { BBUNSUP($<fl>2, "Unsupported: highz strength"); }
        |       yP_PAR__STRENGTH yHIGHZ1 ',' strength0 ')' { BBUNSUP($<fl>2, "Unsupported: highz strength"); }
        ;

//************************************************
// Tables

combinational_body<nodep>:      // IEEE: combinational_body + sequential_body
                yTABLE tableEntryList yENDTABLE         { $$ = new AstUdpTable{$1, $2}; }
        ;

tableEntryList<udpTableLinep>:  // IEEE: { combinational_entry | sequential_entry }
                tableEntry                              { $$ = $1; }
        |       tableEntryList tableEntry               { $$ = addNextNull($1, $2); }
        ;

tableEntry<udpTableLinep>:      // IEEE: combinational_entry + sequential_entry
                yaTABLELINE                             { $$ = new AstUdpTableLine{$<fl>1, *$1}; }
        |       error                                   { $$ = nullptr; }
        ;

//************************************************
// Specify

specify_block<nodep>:           // ==IEEE: specify_block
                ySPECIFY specifyJunkList yENDSPECIFY    { $$ = nullptr; }
        |       ySPECIFY yENDSPECIFY                    { $$ = nullptr; }
        ;

specifyJunkList:
                specifyJunk                             { } /* ignored */
        |       specifyJunkList specifyJunk             { } /* ignored */
        ;

specifyJunk:
                BISONPRE_NOT(ySPECIFY,yENDSPECIFY)      { }
        |       ySPECIFY specifyJunk yENDSPECIFY        { }
        |       error {}
        ;

specparam_declaration<nodep>:           // ==IEEE: specparam_declaration
                ySPECPARAM junkToSemiList ';'           { $$ = nullptr; }
        ;

junkToSemiList:
                junkToSemi                              { } /* ignored */
        |       junkToSemiList junkToSemi               { } /* ignored */
        ;

junkToSemi:
                BISONPRE_NOT(';',yENDSPECIFY,yENDMODULE)        { }
        |       error {}
        ;

//************************************************
// IDs

id<strp>:
                yaID__ETC                               { $$ = $1; $<fl>$ = $<fl>1; }
        |       idRandomize                             { $$ = $1; $<fl>$ = $<fl>1; }
        ;

idAny<strp>:                    // Any kind of identifier
                yaID__ETC                               { $$ = $1; $<fl>$ = $<fl>1; }
        |       yaID__aTYPE                             { $$ = $1; $<fl>$ = $<fl>1; }
        |       idRandomize                             { $$ = $1; $<fl>$ = $<fl>1; }
        ;

idType<strp>:                   // IEEE: class_identifier or other type identifier
        //                      // Used where reference is needed
                yaID__aTYPE                             { $$ = $1; $<fl>$ = $<fl>1; }
        ;

idCC<strp>:                     // IEEE: class/package then ::
                                // lexer matches this:  yaID_LEX [ '#' '(' ... ')' ] yP_COLONCOLON
                yaID__CC                                { $$ = $1; $<fl>$ = $<fl>1; }
        ;

idRandomize<strp>:              // Keyword as an identifier
                yRANDOMIZE                              { static string s = "randomize"; $$ = &s; $<fl>$ = $<fl>1; }
        ;

idSVKwd<strp>:                  // Warn about non-forward compatible Verilog 2001 code
        //                      // yBIT, yBYTE won't work here as causes conflicts
                yDO
                        { static string s = "do"   ; $$ = &s; ERRSVKWD($1, *$$); $<fl>$ = $<fl>1; }
        |       yFINAL
                        { static string s = "final"; $$ = &s; ERRSVKWD($1, *$$); $<fl>$ = $<fl>1; }
        ;

variable_lvalue<nodeExprp>:         // IEEE: variable_lvalue or net_lvalue
        //                      // Note many variable_lvalue's must use exprOkLvalue when arbitrary expressions may also exist
                idClassSel                              { $$ = $1; }
        |       '{' variable_lvalueConcList '}'         { $$ = $2; }
        //                      // IEEE: [ assignment_pattern_expression_type ] assignment_pattern_variable_lvalue
        //                      // We allow more assignment_pattern_expression_types then strictly required
        //UNSUP data_type  yP_TICKBRA variable_lvalueList '}'   { UNSUP }
        //UNSUP idClassSel yP_TICKBRA variable_lvalueList '}'   { UNSUP }
        //UNSUP /**/       yP_TICKBRA variable_lvalueList '}'   { UNSUP }
        |       streaming_concatenation                 { $$ = $1; }
        ;

variable_lvalueConcList<nodeExprp>: // IEEE: part of variable_lvalue: '{' variable_lvalue { ',' variable_lvalue } '}'
                variable_lvalue                                 { $$ = $1; }
        |       variable_lvalueConcList ',' variable_lvalue     { $$ = new AstConcat{$2, $1, $3}; }
        ;

//UNSUPvariable_lvalueList<nodeExprp>:  // IEEE: part of variable_lvalue: variable_lvalue { ',' variable_lvalue }
//UNSUP         variable_lvalue                         { $$ = $1; }
//UNSUP |       variable_lvalueList ',' variable_lvalue { $$ = addNextNull($1, $3); }
//UNSUP ;

// VarRef to dotted, and/or arrayed, and/or bit-ranged variable
idClassSel<nodeExprp>:                      // Misc Ref to dotted, and/or arrayed, and/or bit-ranged variable
                idDotted                                { $$ = $1; }
        //                      // IEEE: [ implicit_class_handle . | package_scope ] hierarchical_variable_identifier select
        |       yTHIS '.' idDotted
                        { $$ = new AstDot{$2, false, new AstParseRef{$<fl>1, VParseRefExp::PX_ROOT, "this"}, $3}; }
        |       ySUPER '.' idDotted
                        { $$ = new AstDot{$2, false, new AstParseRef{$<fl>1, VParseRefExp::PX_ROOT, "super"}, $3}; }
        |       yTHIS '.' ySUPER '.' idDotted           { $$ = $5; BBUNSUP($1, "Unsupported: this.super"); }
        //                      // Expanded: package_scope idDotted
        |       packageClassScope idDotted              { $$ = new AstDot{$<fl>2, true, $1, $2}; }
        ;

idClassSelForeach<nodeExprp>:
                idDottedForeach                         { $$ = $1; }
        //                      // IEEE: [ implicit_class_handle . | package_scope ] hierarchical_variable_identifier select
        |       yTHIS '.' idDottedForeach
                        { $$ = new AstDot{$2, false, new AstParseRef{$<fl>1, VParseRefExp::PX_ROOT, "this"}, $3}; }
        |       ySUPER '.' idDottedForeach
                        { $$ = new AstDot{$2, false, new AstParseRef{$<fl>1, VParseRefExp::PX_ROOT, "super"}, $3}; }
        |       yTHIS '.' ySUPER '.' idDottedForeach    { $$ = $5; BBUNSUP($1, "Unsupported: this.super"); }
        //                      // Expanded: package_scope idForeach
        |       packageClassScope idDottedForeach       { $$ = new AstDot{$<fl>2, true, $1, $2}; }
        ;

idDotted<nodeExprp>:
                yD_ROOT '.' idDottedMore
                        { $$ = new AstDot{$2, false, new AstParseRef{$<fl>1, VParseRefExp::PX_ROOT, "$root"}, $3}; }
        |       idDottedMore                            { $$ = $1; }
        ;

idDottedForeach<nodeExprp>:
                yD_ROOT '.' idDottedMoreForeach
                        { $$ = new AstDot{$2, false, new AstParseRef{$<fl>1, VParseRefExp::PX_ROOT, "$root"}, $3}; }
        |       idDottedMoreForeach                     { $$ = $1; }
        ;

idDottedMore<nodeExprp>:
                idArrayed                               { $$ = $1; }
        |       idDottedMore '.' idArrayed              { $$ = new AstDot{$2, false, $1, $3}; }
        ;

idDottedMoreForeach<nodeExprp>:
                idArrayedForeach                        { $$ = $1; }
        |       idDottedMoreForeach '.' idArrayedForeach        { $$ = new AstDot{$2, false, $1, $3}; }
        ;

// Single component of dotted path, maybe [#].
// Due to lookahead constraints, we can't know if [:] or [+:] are valid (last dotted part),
// we'll assume so and cleanup later.
// id below includes:
//       enum_identifier
idArrayed<nodeExprp>:               // IEEE: id + select
                id
                        { $$ = new AstParseRef{$<fl>1, VParseRefExp::PX_TEXT, *$1, nullptr, nullptr}; }
        //                      // IEEE: id + part_select_range/constant_part_select_range
        |       idArrayed '[' expr ']'                          { $$ = new AstSelBit{$2, $1, $3}; }  // Or AstArraySel, don't know yet.
        |       idArrayed '[' constExpr ':' constExpr ']'       { $$ = new AstSelExtract{$2, $1, $3, $5}; }
        //                      // IEEE: id + indexed_range/constant_indexed_range
        |       idArrayed '[' expr yP_PLUSCOLON  constExpr ']'  { $$ = new AstSelPlus{$2, $1, $3, $5}; }
        |       idArrayed '[' expr yP_MINUSCOLON constExpr ']'  { $$ = new AstSelMinus{$2, $1, $3, $5}; }
        ;

idArrayedForeach<nodeExprp>:    // IEEE: id + select (under foreach expression)
                id
                        { $$ = new AstParseRef{$<fl>1, VParseRefExp::PX_TEXT, *$1, nullptr, nullptr}; }
        //                      // IEEE: id + part_select_range/constant_part_select_range
        |       idArrayed '[' expr ']'                          { $$ = new AstSelBit{$2, $1, $3}; }  // Or AstArraySel, don't know yet.
        |       idArrayed '[' constExpr ':' constExpr ']'       { $$ = new AstSelExtract{$2, $1, $3, $5}; }
        //                      // IEEE: id + indexed_range/constant_indexed_range
        |       idArrayed '[' expr yP_PLUSCOLON  constExpr ']'  { $$ = new AstSelPlus{$2, $1, $3, $5}; }
        |       idArrayed '[' expr yP_MINUSCOLON constExpr ']'  { $$ = new AstSelMinus{$2, $1, $3, $5}; }
        //                      // IEEE: loop_variables (under foreach expression)
        //                      // To avoid conflicts we allow expr as first element, must post-check
        |       idArrayed '[' expr ',' loop_variables ']'
                        { $$ = new AstSelLoopVars{$2, $1, addNextNull(static_cast<AstNode*>($3), $5)}; }
        |       idArrayed '[' ',' loop_variables ']'
                        { $$ = new AstSelLoopVars{$2, $1, addNextNull(static_cast<AstNode*>(new AstEmpty{$3}), $4)}; }
        ;

// VarRef without any dots or vectorizaion
varRefBase<parseRefp>:
                id                                      { $$ = new AstParseRef{$<fl>1, VParseRefExp::PX_TEXT, *$1}; }
        ;

// ParseRef
parseRefBase<nodep>:
                id
                        { $$ = new AstParseRef{$<fl>1, VParseRefExp::PX_TEXT, *$1, nullptr, nullptr}; }
        ;

// yaSTRING shouldn't be used directly, instead via an abstraction below
str<strp>:                      // yaSTRING but with \{escapes} need decoded
                yaSTRING                                { $$ = PARSEP->newString(GRAMMARP->unquoteString($<fl>1, *$1)); }
        ;

strAsInt<nodeExprp>:
                yaSTRING
                        { // Numeric context, so IEEE 1800-2017 11.10.3 "" is a "\000"
                          $$ = new AstConst{$<fl>1, AstConst::VerilogStringLiteral{}, GRAMMARP->unquoteString($<fl>1, *$1)}; }
        ;

strAsIntIgnore<nodeExprp>:          // strAsInt, but never matches for when expr shouldn't parse strings
                yaSTRING__IGNORE                        { $$ = nullptr; yyerror("Impossible token"); }
        ;

strAsText<nodep>:
                yaSTRING                                { $$ = GRAMMARP->createTextQuoted($<fl>1, *$1); }
        ;

endLabelE<strp>:
                /* empty */                             { $$ = nullptr; $<fl>$ = nullptr; }
        |       ':' idAny                               { $$ = $2; $<fl>$ = $<fl>2; }
        |       ':' yNEW__ETC                           { static string n = "new"; $$ = &n; $<fl>$ = $<fl>2; }
        ;

//************************************************
// Clocking

clocking_declaration<nodep>:            // IEEE: clocking_declaration
                yCLOCKING idAny clocking_event ';' clocking_itemListE yENDCLOCKING endLabelE
                        { $$ = new AstClocking{$<fl>2, *$2, $3, $5, false, false}; }
        |       yDEFAULT yCLOCKING clocking_event ';' clocking_itemListE yENDCLOCKING endLabelE
                        { $$ = new AstClocking{$<fl>2, "", $3, $5, true, false}; }
        |       yDEFAULT yCLOCKING idAny clocking_event ';' clocking_itemListE yENDCLOCKING endLabelE
                        { $$ = new AstClocking{$<fl>3, *$3, $4, $6, true, false}; }
        |       yGLOBAL__CLOCKING yCLOCKING clocking_event ';' clocking_itemListE yENDCLOCKING endLabelE
                        { $$ = new AstClocking{$<fl>2, "", $3, $5, false, true}; }
        |       yGLOBAL__CLOCKING yCLOCKING idAny clocking_event ';' clocking_itemListE yENDCLOCKING endLabelE
                        { $$ = new AstClocking{$<fl>3, *$3, $4, $6, false, true}; }
        ;

clocking_eventE<senItemp>:      // IEEE: optional clocking_event
                /* empty */                             { $$ = nullptr; }
        |       clocking_event                          { $$ = $1; }
        ;

clocking_event<senItemp>:       // IEEE: clocking_event
                '@' id
                        { $$ = new AstSenItem{$<fl>2, VEdgeType::ET_CHANGED,
                                              new AstParseRef{$<fl>2, VParseRefExp::PX_TEXT, *$2, nullptr, nullptr}}; }
        |       '@' '(' event_expression ')'            { $$ = $3; }
        ;

clocking_itemListE<clockingItemp>:
                /* empty */                             { $$ = nullptr; }
        |       clocking_itemList                       { $$ = $1; }
        ;

clocking_itemList<clockingItemp>:  // IEEE: [ clocking_item ]
                clocking_item                           { $$ = $1; }
        |       clocking_itemList clocking_item         { if ($1) $$ = addNextNull($1, $2); }
        ;

clocking_item<clockingItemp>:   // IEEE: clocking_item
                yDEFAULT yINPUT clocking_skew ';'       { $$ = new AstClockingItem{$<fl>1, VDirection::INPUT, $3, nullptr}; }
        |       yDEFAULT yOUTPUT clocking_skew ';'      { $$ = new AstClockingItem{$<fl>1, VDirection::OUTPUT, $3, nullptr}; }
        |       yDEFAULT yINPUT clocking_skew yOUTPUT clocking_skew ';'
                        { $$ = new AstClockingItem{$<fl>1, VDirection::INPUT, $3, nullptr};
                          $$->addNext(new AstClockingItem{$<fl>4, VDirection::OUTPUT, $5, nullptr}); }
        |       yINPUT clocking_skewE list_of_clocking_decl_assign ';'
                        { $$ = GRAMMARP->makeClockingItemList($<fl>1, VDirection::INPUT, $2, $3); }
        |       yOUTPUT clocking_skewE list_of_clocking_decl_assign ';'
                        { $$ = GRAMMARP->makeClockingItemList($<fl>1, VDirection::OUTPUT, $2, $3); }
        |       yINPUT clocking_skewE yOUTPUT clocking_skewE list_of_clocking_decl_assign ';'
                        { $$ = nullptr;
                          BBUNSUP($5, "Unsupported: Mixed input/output clocking items"); }
        |       yINOUT list_of_clocking_decl_assign ';'
                        { $$ = nullptr;
                          BBUNSUP($1, "Unsupported: 'inout' clocking items"); }
        |       assertion_item_declaration
                        { $$ = nullptr;
                          BBUNSUP($1, "Unsupported: assertion items in clocking blocks"); }
        ;

list_of_clocking_decl_assign<nodep>:  // IEEE: list_of_clocking_decl_assign
                clocking_decl_assign                    { $$ = $1; }
        |       list_of_clocking_decl_assign ',' clocking_decl_assign
                        { $$ = addNextNull($1, $3); }
        ;

clocking_decl_assign<nodep>:    // IEEE: clocking_decl_assign
                idAny/*new-signal_identifier*/ exprEqE
                        { AstParseRef* const refp = new AstParseRef{$<fl>1, VParseRefExp::PX_TEXT, *$1, nullptr, nullptr};
                          $$ = refp;
                          if ($2) $$ = new AstAssign{$<fl>2, refp, $2}; }
        ;

clocking_skewE<nodeExprp>:          // IEEE: [clocking_skew]
                /* empty */                             { $$ = nullptr; }
        |       clocking_skew                           { $$ = $1; }
        ;

clocking_skew<nodeExprp>:           // IEEE: clocking_skew
                delay_control                           { $$ = $1->lhsp()->unlinkFrBack(); $1->deleteTree(); }
        |      '#' ya1STEP                              { $$ = new AstConst{$<fl>1, AstConst::OneStep{}}; }
        |      yPOSEDGE delay_controlE                  { $$ = nullptr;
                                                          BBUNSUP($1, "Unsupported: clocking event edge override"); }
        |      yNEGEDGE delay_controlE                  { $$ = nullptr;
                                                          BBUNSUP($1, "Unsupported: clocking event edge override"); }
        |      yEDGE delay_controlE                     { $$ = nullptr;
                                                          BBUNSUP($1, "Unsupported: clocking event edge override"); }
        ;

cycle_delay<delayp>:  // IEEE: cycle_delay
               yP_POUNDPOUND yaINTNUM
                       { $$ = new AstDelay{$<fl>1, new AstConst{$<fl>2, *$2}, true}; }
        |      yP_POUNDPOUND id
                       { $$ = new AstDelay{$<fl>1, new AstParseRef{$<fl>2, VParseRefExp::PX_TEXT, *$2, nullptr, nullptr}, true}; }
        |      yP_POUNDPOUND '(' expr ')'
                       { $$ = new AstDelay{$<fl>1, $3, true}; }
        ;

//************************************************
// Asserts

assertion_item_declaration<nodep>:  // ==IEEE: assertion_item_declaration
                property_declaration                    { $$ = $1; }
        |       sequence_declaration                    { $$ = $1; }
        |       let_declaration                         { $$ = $1; }
        ;

assertion_item<nodep>:          // ==IEEE: assertion_item
                concurrent_assertion_item               { $$ = $1; }
        |       deferred_immediate_assertion_item
                        { $$ = $1 ? new AstAlways{$1->fileline(), VAlwaysKwd::ALWAYS_COMB, nullptr, $1} : nullptr; }
        ;

deferred_immediate_assertion_item<nodep>:       // ==IEEE: deferred_immediate_assertion_item
                deferred_immediate_assertion_statement  { $$ = $1; }
        |       id/*block_identifier*/ ':' deferred_immediate_assertion_statement
                        { $$ = new AstBegin{$<fl>1, *$1, $3, false, true}; }
        ;

procedural_assertion_statement<nodep>:  // ==IEEE: procedural_assertion_statement
                concurrent_assertion_statement          { $$ = $1; }
        |       immediate_assertion_statement           { $$ = $1; }
        //                      // IEEE: checker_instantiation
        //                      // Unlike modules, checkers are the only "id id (...)" form in statements.
        //UNSUP checker_instantiation                   { $$ = $1; }
        ;

immediate_assertion_statement<nodep>:   // ==IEEE: immediate_assertion_statement
                simple_immediate_assertion_statement    { $$ = $1; }
        |       deferred_immediate_assertion_statement  { $$ = $1; }
        ;

simple_immediate_assertion_statement<nodep>:    // ==IEEE: simple_immediate_assertion_statement
        //                      // action_block expanded here, for compatibility with AstAssert
                assertOrAssume '(' expr ')' stmtBlock %prec prLOWER_THAN_ELSE
                        { $$ = new AstAssert{$1, $3, $5, nullptr, true}; }
        |       assertOrAssume '(' expr ')'           yELSE stmtBlock
                        { $$ = new AstAssert{$1, $3, nullptr, $6, true}; }
        |       assertOrAssume '(' expr ')' stmtBlock yELSE stmtBlock
                        { $$ = new AstAssert{$1, $3, $5, $7, true}; }
        //                      // IEEE: simple_immediate_cover_statement
        |       yCOVER '(' expr ')' stmt                { $$ = new AstCover{$1, $3, $5, true}; }
        ;

assertOrAssume<fl>:
                yASSERT                                 { $$ = $1; }
        |       yASSUME                                 { $$ = $1; }
        ;

final_zero:                     // IEEE: part of deferred_immediate_assertion_statement
                '#' yaINTNUM
                        { if ($2->isNeqZero()) { $<fl>2->v3error("Deferred assertions must use '#0' (IEEE 1800-2017 16.4)"); } }
        //                      // 1800-2012:
        |       yFINAL                                                  { }
        ;

deferred_immediate_assertion_statement<nodep>:  // ==IEEE: deferred_immediate_assertion_statement
        //                      // IEEE: deferred_immediate_assert_statement
                assertOrAssume final_zero '(' expr ')' stmtBlock %prec prLOWER_THAN_ELSE
                        { $$ = new AstAssert{$1, $4, $6, nullptr, true}; }
        |       assertOrAssume final_zero '(' expr ')'           yELSE stmtBlock
                        { $$ = new AstAssert{$1, $4, nullptr, $7, true}; }
        |       assertOrAssume final_zero '(' expr ')' stmtBlock yELSE stmtBlock
                        { $$ = new AstAssert{$1, $4, $6, $8, true}; }
        //                      // IEEE: deferred_immediate_cover_statement
        |       yCOVER final_zero '(' expr ')' stmt     { $$ = new AstCover{$1, $4, $6, true}; }
        ;

concurrent_assertion_item<nodep>:       // IEEE: concurrent_assertion_item
                concurrent_assertion_statement          { $$ = $1; }
        |       id/*block_identifier*/ ':' concurrent_assertion_statement
                        { $$ = new AstBegin{$<fl>1, *$1, $3, false, true}; }
        //                      // IEEE: checker_instantiation
        //                      // identical to module_instantiation; see etcInst
        ;

concurrent_assertion_statement<nodep>:  // ==IEEE: concurrent_assertion_statement
        //                      // IEEE: assert_property_statement
        //                      // IEEE: assume_property_statement
        //                      // action_block expanded here
                assertOrAssume yPROPERTY '(' property_spec ')' stmt %prec prLOWER_THAN_ELSE
                        { $$ = new AstAssert{$1, new AstSampled{$1, $4}, $6, nullptr, false}; }
        |       assertOrAssume yPROPERTY '(' property_spec ')' stmt yELSE stmt
                        { $$ = new AstAssert{$1, new AstSampled{$1, $4}, $6, $8, false}; }
        |       assertOrAssume yPROPERTY '(' property_spec ')' yELSE stmt
                        { $$ = new AstAssert{$1, new AstSampled{$1, $4}, nullptr, $7, false}; }
        //                      // IEEE: cover_property_statement
        |       yCOVER yPROPERTY '(' property_spec ')' stmtBlock
                        { $$ = new AstCover{$1, $4, $6, false}; }
        //                      // IEEE: cover_sequence_statement
        |       yCOVER ySEQUENCE '(' sexpr ')' stmt
                        { $$ = nullptr; BBUNSUP($2, "Unsupported: cover sequence"); }
        //                      // IEEE: yCOVER ySEQUENCE '(' clocking_event sexpr ')' stmt
        //                      // sexpr already includes "clocking_event sexpr"
        |       yCOVER ySEQUENCE '(' clocking_event yDISABLE yIFF '(' expr/*expression_or_dist*/ ')' sexpr ')' stmt
                        { $$ = nullptr; BBUNSUP($2, "Unsupported: cover sequence"); }
        |       yCOVER ySEQUENCE '(' yDISABLE yIFF '(' expr/*expression_or_dist*/ ')' sexpr ')' stmt
                        { $$ = nullptr; BBUNSUP($2, "Unsupported: cover sequence"); }
        //                      // IEEE: restrict_property_statement
        |       yRESTRICT yPROPERTY '(' property_spec ')' ';'
                        { $$ = new AstRestrict{$1, $4}; }
        ;

property_declaration<nodeFTaskp>:  // ==IEEE: property_declaration
                property_declarationFront property_port_listE ';' property_declarationBody
                        yENDPROPERTY endLabelE
                        { $$ = $1;
                          $$->addStmtsp($2);
                          $$->addStmtsp($4);
                          SYMP->popScope($$);
                          GRAMMARP->endLabel($<fl>6, $$, $6);
                          GRAMMARP->m_insideProperty = false;
                          GRAMMARP->m_typedPropertyPort = false; }
        ;

property_declarationFront<nodeFTaskp>:  // IEEE: part of property_declaration
                yPROPERTY idAny/*property_identifier*/
                        { $$ = new AstProperty{$<fl>2, *$2, nullptr};
                          GRAMMARP->m_insideProperty = true;
                          SYMP->pushNewUnderNodeOrCurrent($$, nullptr); }
        ;

property_port_listE<nodep>:  // IEEE: [ ( [ property_port_list ] ) ]
                /* empty */                       { $$ = nullptr; }
        |       '(' ')'                           { $$ = nullptr; }
        |       '(' property_port_list ')'        { $$ = $2; }
        ;

property_port_list<nodep>:  // ==IEEE: property_port_list
                property_port_item                              { $$ = $1; }
        |       property_port_list ',' property_port_item       { $$ = addNextNull($1, $3); }
        ;

property_port_item<nodep>:  // IEEE: property_port_item/sequence_port_item
        //                      // Merged in sequence_port_item
        //                      // IEEE: property_lvar_port_direction ::= yINPUT
        //                      // prop IEEE: [ yLOCAL [ yINPUT ] ] property_formal_type
        //                      //           id {variable_dimension} [ '=' property_actual_arg ]
        //                      // seq IEEE: [ yLOCAL [ sequence_lvar_port_direction ] ] sequence_formal_type
        //                      //           id {variable_dimension} [ '=' sequence_actual_arg ]
                property_port_itemFront property_port_itemAssignment { $$ = $2; }
        ;

property_port_itemFront: // IEEE: part of property_port_item/sequence_port_item
                property_port_itemDirE property_formal_typeNoDt  { VARDTYPE($2); }
        //                      // data_type_or_implicit
        |       property_port_itemDirE data_type
                        { VARDTYPE($2); GRAMMARP->m_typedPropertyPort = true; }
        |       property_port_itemDirE yVAR data_type
                        { VARDTYPE($3); GRAMMARP->m_typedPropertyPort = true; }
        |       property_port_itemDirE yVAR implicit_typeE      { VARDTYPE($3); }
        |       property_port_itemDirE implicit_typeE           { VARDTYPE($2); }
        ;

property_port_itemAssignment<nodep>:  // IEEE: part of property_port_item/sequence_port_item/checker_port_direction
                id variable_dimensionListE         { $$ = VARDONEA($<fl>1, *$1, $2, nullptr); }
        |       id variable_dimensionListE '=' property_actual_arg
                        { $$ = VARDONEA($<fl>1, *$1, $2, $4);
                          BBUNSUP($3, "Unsupported: property variable default value"); }
        ;

property_port_itemDirE:
                /* empty */
                        { VARIO(INPUT); }
        |       yLOCAL__ETC
                        { VARIO(INPUT);
                          BBUNSUP($1, "Unsupported: property port 'local'"); }
        |       yLOCAL__ETC yINPUT
                        { VARIO(INPUT);
                          BBUNSUP($1, "Unsupported: property port 'local'"); }
        ;

property_declarationBody<nodep>:  // IEEE: part of property_declaration
        //UNSUP assertion_variable_declarationList property_statement_spec  {}
        //                      // IEEE-2012: Incorectly hasyCOVER ySEQUENCE then property_spec here.
        //                      // Fixed in IEEE 1800-2017
                property_spec                 { $$ = $1; }
        |       property_spec ';'             { $$ = $1; }
        ;

assertion_variable_declarationList<nodep>: // IEEE: part of assertion_variable_declaration
                assertion_variable_declaration          { $$ = $1; }
        |       assertion_variable_declarationList assertion_variable_declaration
                        { $$ = addNextNull($1, $2); }
        ;

sequence_declaration<nodeFTaskp>:  // ==IEEE: sequence_declaration
                sequence_declarationFront sequence_port_listE ';' sequence_declarationBody
        /*cont*/    yENDSEQUENCE endLabelE
                        { $$ = $1;
                          $$->addStmtsp($2);
                          $$->addStmtsp($4);
                          SYMP->popScope($$);
                          GRAMMARP->endLabel($<fl>6, $$, $6); }
        ;

sequence_declarationFront<nodeFTaskp>:  // IEEE: part of sequence_declaration
                ySEQUENCE idAny/*new_sequence*/
                        { BBUNSUP($1, "Unsupported: sequence");
                          $$ = new AstProperty{$<fl>2, *$2, nullptr};
                          SYMP->pushNewUnderNodeOrCurrent($$, nullptr); }
        ;

sequence_port_listE<nodep>:  // IEEE: [ ( [ sequence_port_list ] ) ]
        //                      // IEEE: sequence_lvar_port_direction ::= yINPUT | yINOUT | yOUTPUT
        //                      // IEEE: [ yLOCAL [ sequence_lvar_port_direction ] ] sequence_formal_type
        //                      //           id {variable_dimension} [ '=' sequence_actual_arg ]
        //                      // All this is almost identically the same as a property.
        //                      // Difference is only yINOUT/yOUTPUT (which might be added to 1800-2012)
        //                      // and yPROPERTY.  So save some work.
                property_port_listE                     { $$ = $1; }
        ;

property_formal_typeNoDt<nodeDTypep>:  // IEEE: property_formal_type (w/o implicit)
                sequence_formal_typeNoDt                { $$ = $1; }
        |       yPROPERTY
                        { $$ = nullptr; GRAMMARP->m_typedPropertyPort = false;
                          BBUNSUP($1, "Unsupported: property argument data type"); }
        ;

sequence_formal_typeNoDt<nodeDTypep>:  // ==IEEE: sequence_formal_type (w/o data_type_or_implicit)
                        // IEEE: data_type_or_implicit
                        // implicit expanded where used
                ySEQUENCE
                        { $$ = nullptr; GRAMMARP->m_typedPropertyPort = false;
                          BBUNSUP($1, "Unsupported: sequence argument data type"); }
                        // IEEE-2009: yEVENT
                        // already part of data_type.  Removed in 1800-2012.
        |       yUNTYPED
                        { $$ = nullptr; GRAMMARP->m_typedPropertyPort = false; }
        ;

sequence_declarationBody<nodep>:  // IEEE: part of sequence_declaration
        //                      // 1800-2012 makes ';' optional
                assertion_variable_declarationList sexpr        { $$ = addNextNull($1, $2); }
        |       assertion_variable_declarationList sexpr ';'    { $$ = addNextNull($1, $2); }
        |       sexpr                                   { $$ = $1; }
        |       sexpr ';'                               { $$ = $1; }
        ;

property_spec<propSpecp>:               // IEEE: property_spec
        //UNSUP: This rule has been super-specialized to what is supported now
        //UNSUP remove below
                '@' '(' senitemEdge ')' yDISABLE yIFF '(' expr ')' pexpr
                        { $$ = new AstPropSpec{$1, $3, $8, $10}; }
        |       '@' '(' senitemEdge ')' pexpr           { $$ = new AstPropSpec{$1, $3, nullptr, $5}; }
        //UNSUP remove above
        |       yDISABLE yIFF '(' expr ')' pexpr        { $$ = new AstPropSpec{$4->fileline(), nullptr, $4, $6}; }
        |       pexpr                                   { $$ = new AstPropSpec{$1->fileline(), nullptr, nullptr, $1}; }
        ;

//UNSUPproperty_statement_spec<nodep>:  // ==IEEE: property_statement_spec
//UNSUP //                      // IEEE: [ clocking_event ] [ yDISABLE yIFF '(' expression_or_dist ')' ] property_statement
//UNSUP         property_statement                      { $$ = $1; }
//UNSUP |       yDISABLE yIFF '(' expr/*expression_or_dist*/ ')' property_statement     { }
//UNSUP //                      // IEEE: clocking_event property_statement
//UNSUP //                      // IEEE: clocking_event yDISABLE yIFF '(' expr/*expression_or_dist*/ ')' property_statement
//UNSUP //                      // Both overlap pexpr:"clocking_event pexpr"  the difference is
//UNSUP //                      // property_statement:property_statementCaseIf so replicate it
//UNSUP |       clocking_event property_statementCaseIf { }
//UNSUP |       clocking_event yDISABLE yIFF '(' expr/*expression_or_dist*/ ')' property_statementCaseIf        { }
//UNSUP ;

//UNSUPproperty_statement<nodep>:  // ==IEEE: property_statement
//UNSUP //                      // Doesn't make sense to have "pexpr ;" in pexpr rule itself, so we split out case/if
//UNSUP         pexpr ';'                               { $$ = $1; }
//UNSUP //                      // Note this term replicated in property_statement_spec
//UNSUP //                      // If committee adds terms, they may need to be there too.
//UNSUP |       property_statementCaseIf                { $$ = $1; }
//UNSUP ;

property_statementCaseIf<nodeExprp>:  // IEEE: property_statement - minus pexpr
                yCASE '(' expr/*expression_or_dist*/ ')' property_case_itemList yENDCASE
                        { $$ = new AstConst{$1, AstConst::BitFalse{}};
                          BBUNSUP($<fl>1, "Unsupported: property case expression"); }
        |       yCASE '(' expr/*expression_or_dist*/ ')' yENDCASE
                        { $$ = new AstConst{$1, AstConst::BitFalse{}};
                          BBUNSUP($<fl>1, "Unsupported: property case expression"); }
        |       yIF '(' expr/*expression_or_dist*/ ')' pexpr  %prec prLOWER_THAN_ELSE
                        { $$ = $5; BBUNSUP($<fl>1, "Unsupported: property case expression"); }
        |       yIF '(' expr/*expression_or_dist*/ ')' pexpr yELSE pexpr
                        { $$ = $5; BBUNSUP($<fl>1, "Unsupported: property case expression"); }
        ;

property_case_itemList<caseItemp>:  // IEEE: {property_case_item}
                property_case_item                      { $$ = $1; }
        |       property_case_itemList ',' property_case_item   { $$ = addNextNull($1, $3); }
        ;

property_case_item<caseItemp>:  // ==IEEE: property_case_item
        //                      // IEEE: expression_or_dist { ',' expression_or_dist } ':' property_statement
        //                      // IEEE 1800-2012 changed from property_statement to property_expr
        //                      // IEEE 1800-2017 changed to require the semicolon
                caseCondList ':' pexpr                  { $$ = new AstCaseItem{$2, $1, $3}; }
        |       caseCondList ':' pexpr ';'              { $$ = new AstCaseItem{$2, $1, $3}; }
        |       yDEFAULT pexpr                          { $$ = new AstCaseItem{$1, nullptr, $2}; }
        |       yDEFAULT ':' pexpr ';'                  { $$ = new AstCaseItem{$1, nullptr, $3}; }
        ;

//UNSUPpev_expr<nodep>:  // IEEE: property_actual_arg | expr
//UNSUP //                      //       which expands to pexpr | event_expression
//UNSUP //                      // Used in port and function calls, when we can't know yet if something
//UNSUP //                      // is a function/sequence/property or instance/checker pin.
//UNSUP //
//UNSUP //                      // '(' pev_expr ')'
//UNSUP //                      // Already in pexpr
//UNSUP //                      // IEEE: event_expression ',' event_expression
//UNSUP //                      // ','s are legal in event_expressions, but parens required to avoid conflict with port-sep-,
//UNSUP //                      // IEEE: event_expression yOR event_expression
//UNSUP //                      // Already in pexpr - needs removal there
//UNSUP //                      // IEEE: event_expression yIFF expr
//UNSUP //                      // Already in pexpr - needs removal there
//UNSUP //
//UNSUP         senitemEdge                             { $$ = $1; }
//UNSUP //
//UNSUP //============= pexpr rules copied for pev_expr
//UNSUP |       BISONPRE_COPY_ONCE(pexpr,{s/~o~p/pev_/g; })     // {copied}
//UNSUP //
//UNSUP //============= sexpr rules copied for pev_expr
//UNSUP |       BISONPRE_COPY_ONCE(sexpr,{s/~p~s/pev_/g; })     // {copied}
//UNSUP //
//UNSUP //============= expr rules copied for pev_expr
//UNSUP |       BISONPRE_COPY_ONCE(expr,{s/~l~/pev_/g; s/~p~/pev_/g; s/~noPar__IGNORE~'.'/yP_PAR__IGNORE /g; })    // {copied}
//UNSUP ;

pexpr<nodeExprp>:  // IEEE: property_expr  (The name pexpr is important as regexps just add an "p" to expr.)
        //
        //                      // IEEE: sequence_expr
        //                      // Expanded below
        //
        //                      // IEEE: '(' pexpr ')'
        //                      // Expanded below
        //
                yNOT pexpr %prec prNEGATION             { $$ = new AstLogNot{$1, $2}; }
        |       ySTRONG '(' sexpr ')'
                        { $$ = $3; BBUNSUP($2, "Unsupported: strong (in property expression)"); }
        |       yWEAK '(' sexpr ')'
                        { $$ = $3; BBUNSUP($2, "Unsupported: weak (in property expression)"); }
        //                      // IEEE: pexpr yOR pexpr
        //                      // IEEE: pexpr yAND pexpr
        //                      // Under ~p~sexpr and/or ~p~sexpr
        //
        //                      // IEEE: "sequence_expr yP_ORMINUSGT pexpr"
        //                      // Instead we use pexpr to prevent conflicts
        |       ~o~pexpr yP_ORMINUSGT pexpr             { $$ = new AstLogOr{$2, new AstLogNot{$2, $1}, $3}; }
        |       ~o~pexpr yP_OREQGT pexpr                { $$ = new AstImplication{$2, $1, $3}; }
        //
        //                      // IEEE-2009: property_statement
        //                      // IEEE-2012: yIF and yCASE
        |       property_statementCaseIf                { $$ = $1; }
        //
        |       ~o~pexpr/*sexpr*/ yP_POUNDMINUSPD pexpr
                        { $$ = $3; BBUNSUP($2, "Unsupported: #-# (in property expression)"); }
        |       ~o~pexpr/*sexpr*/ yP_POUNDEQPD pexpr
                        { $$ = $3; BBUNSUP($2, "Unsupported: #=# (in property expression)"); }
        |       yNEXTTIME pexpr
                        { $$ = $2; BBUNSUP($1, "Unsupported: nexttime (in property expression)"); }
        |       yS_NEXTTIME pexpr
                        { $$ = $2; BBUNSUP($1, "Unsupported: s_nexttime (in property expression)"); }
        |       yNEXTTIME '[' constExpr ']' pexpr %prec yNEXTTIME
                        { $$ = $5; BBUNSUP($1, "Unsupported: nexttime[] (in property expression)"); }
        |       yS_NEXTTIME '[' constExpr ']' pexpr %prec yS_NEXTTIME
                        { $$ = $5; BBUNSUP($1, "Unsupported: s_nexttime[] (in property expression)"); }
        |       yALWAYS pexpr
                        { $$ = $2; BBUNSUP($1, "Unsupported: always (in property expression)"); }
        |       yALWAYS anyrange pexpr  %prec yALWAYS
                        { $$ = $3; BBUNSUP($1, "Unsupported: always[] (in property expression)"); }
        |       yS_ALWAYS anyrange pexpr  %prec yS_ALWAYS
                        { $$ = $3; BBUNSUP($1, "Unsupported: s_always (in property expression)"); }
        |       yEVENTUALLY pexpr
                        { $$ = $2; BBUNSUP($1, "Unsupported: eventually (in property expression)"); }
        |       yS_EVENTUALLY pexpr
                        { $$ = $2; BBUNSUP($1, "Unsupported: s_eventually (in property expression)"); }
        |       yEVENTUALLY '[' constExpr ']' pexpr  %prec yEVENTUALLY
                        { $$ = $5; BBUNSUP($1, "Unsupported: eventually[] (in property expression)"); }
        |       yS_EVENTUALLY anyrange pexpr  %prec yS_EVENTUALLY
                        { $$ = $3; BBUNSUP($1, "Unsupported: s_eventually[] (in property expression)"); }
        |       ~o~pexpr yUNTIL pexpr
                        { $$ = $1; BBUNSUP($2, "Unsupported: until (in property expression)"); }
        |       ~o~pexpr yS_UNTIL pexpr
                        { $$ = $1; BBUNSUP($2, "Unsupported: s_until (in property expression)"); }
        |       ~o~pexpr yUNTIL_WITH pexpr
                        { $$ = $1; BBUNSUP($2, "Unsupported: until_with (in property expression)"); }
        |       ~o~pexpr yS_UNTIL_WITH pexpr
                        { $$ = $1; BBUNSUP($2, "Unsupported: s_until_with (in property expression)"); }
        |       ~o~pexpr yIMPLIES pexpr
                        { $$ = $1; BBUNSUP($2, "Unsupported: implies (in property expression)"); }
        //                      // yIFF also used by event_expression
        |       ~o~pexpr yIFF pexpr
                        { $$ = $1; BBUNSUP($2, "Unsupported: iff (in property expression)"); }
        |       yACCEPT_ON '(' expr/*expression_or_dist*/ ')' pexpr  %prec yACCEPT_ON
                        { $$ = $5; BBUNSUP($2, "Unsupported: accept_on (in property expression)"); }
        |       yREJECT_ON '(' expr/*expression_or_dist*/ ')' pexpr  %prec yREJECT_ON
                        { $$ = $5; BBUNSUP($2, "Unsupported: reject_on (in property expression)"); }
        |       ySYNC_ACCEPT_ON '(' expr/*expression_or_dist*/ ')' pexpr %prec ySYNC_ACCEPT_ON
                        { $$ = $5; BBUNSUP($2, "Unsupported: sync_accept_on (in property expression)"); }
        |       ySYNC_REJECT_ON '(' expr/*expression_or_dist*/ ')' pexpr %prec ySYNC_REJECT_ON
                        { $$ = $5; BBUNSUP($2, "Unsupported: sync_reject_on (in property expression)"); }
        //
        //                      // IEEE: "property_instance"
        //                      // Looks just like a function/method call
        //
        //                      // Note "clocking_event pexpr" overlaps
        //                      // property_statement_spec: clocking_event property_statement
        //
        //                      // Include property_specDisable to match property_spec rule
        //UNSUP clocking_event yDISABLE yIFF '(' expr ')' pexpr %prec prSEQ_CLOCKING    { }
        //
        //============= sexpr rules copied for property_expr
        |       BISONPRE_COPY_ONCE(sexpr,{s/~p~s/p/g; })        // {copied}
        //
        //============= expr rules copied for property_expr
        |       BISONPRE_COPY_ONCE(expr,{s/~l~/p/g; s/~p~/p/g; s/~noPar__IGNORE~'.'/yP_PAR__IGNORE /g; })  // {copied}
        ;

sexpr<nodeExprp>:  // ==IEEE: sequence_expr  (The name sexpr is important as regexps just add an "s" to expr.)
        //                      // ********* RULES COPIED IN sequence_exprProp
        //                      // For precedence, see IEEE 17.7.1
        //
        //                      // IEEE: "cycle_delay_range sequence_expr { cycle_delay_range sequence_expr }"
        //                      // IEEE: "sequence_expr cycle_delay_range sequence_expr { cycle_delay_range sequence_expr }"
        //                      // Both rules basically mean we can repeat sequences, so make it simpler:
                cycle_delay_range sexpr  %prec yP_POUNDPOUND
                        { $$ = $2; BBUNSUP($2->fileline(), "Unsupported: ## (in sequence expression)"); }
        |       ~p~sexpr cycle_delay_range sexpr %prec prPOUNDPOUND_MULTI
                        { $$ = $1; BBUNSUP($2->fileline(), "Unsupported: ## (in sequence expression)"); }
        //
        //                      // IEEE: expression_or_dist [ boolean_abbrev ]
        //                      // Note expression_or_dist includes "expr"!
        //                      // sexpr/*sexpression_or_dist*/  --- Hardcoded below
        |       ~p~sexpr/*sexpression_or_dist*/ boolean_abbrev
                        { $$ = $1; BBUNSUP($2->fileline(), "Unsupported: boolean abbrev (in sequence expression)"); }
        //
        //                      // IEEE: "sequence_instance [ sequence_abbrev ]"
        //                      // version without sequence_abbrev looks just like normal function call
        //                      // version w/sequence_abbrev matches above;
        //                      // expression_or_dist:expr:func boolean_abbrev:sequence_abbrev
        //
        //                      // IEEE: '(' expression_or_dist {',' sequence_match_item } ')' [ boolean_abbrev ]
        //                      // IEEE: '(' sexpr {',' sequence_match_item } ')' [ sequence_abbrev ]
        //                      // As sequence_expr includes expression_or_dist, and boolean_abbrev includes sequence_abbrev:
        //                      // '(' sequence_expr {',' sequence_match_item } ')' [ boolean_abbrev ]
        //                      // "'(' sexpr ')' boolean_abbrev" matches "[sexpr:'(' expr ')'] boolean_abbrev" so we can drop it
        |       '(' ~p~sexpr ')'                        { $$ = $2; }
        //UNSUP '(' ~p~sexpr ',' sequence_match_itemList ')'    { }
        //
        //                      // AND/OR are between pexprs OR sexprs
        |       ~p~sexpr yAND ~p~sexpr
                        { $$ = new AstLogAnd{$2, $1, $3};
                          BBUNSUP($2, "Unsupported: and (in sequence expression)"); }
        |       ~p~sexpr yOR ~p~sexpr
                        { $$ = new AstLogOr{$2, $1, $3};
                          BBUNSUP($2, "Unsupported: or (in sequence expression)"); }
        //                      // Intersect always has an sexpr rhs
        |       ~p~sexpr yINTERSECT sexpr
                        { $$ = $1; BBUNSUP($2, "Unsupported: intersect (in sequence expression)"); }
        //
        |       yFIRST_MATCH '(' sexpr ')'
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: first_match (in sequence expression)"); }
        |       yFIRST_MATCH '(' sexpr ',' sequence_match_itemList ')'
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: first_match (in sequence expression)"); }
        |       ~p~sexpr/*sexpression_or_dist*/ yTHROUGHOUT sexpr
                        { $$ = $1; BBUNSUP($2, "Unsupported: throughout (in sequence expression)"); }
        //                      // Below pexpr's are really sequence_expr, but avoid conflict
        //                      // IEEE: sexpr yWITHIN sexpr
        |       ~p~sexpr yWITHIN sexpr
                        { $$ = $1; BBUNSUP($2, "Unsupported: within (in sequence expression)"); }
        //                      // Note concurrent_assertion had duplicate rule for below
        //UNSUP clocking_event ~p~sexpr %prec prSEQ_CLOCKING    { }
        //
        //============= expr rules copied for sequence_expr
        |       BISONPRE_COPY_ONCE(expr,{s/~l~/s/g; s/~p~/s/g; s/~noPar__IGNORE~'.'/yP_PAR__IGNORE /g; })  // {copied}
        ;

cycle_delay_range<nodep>:  // IEEE: ==cycle_delay_range
        //                      // These three terms in 1800-2005 ONLY
                yP_POUNDPOUND intnumAsConst
                        { $$ = $2;
                          BBUNSUP($<fl>1, "Unsupported: ## () cycle delay range expression"); }
        |       yP_POUNDPOUND id
                        { $$ = new AstConst{$1, AstConst::BitFalse{}};
                          BBUNSUP($<fl>1, "Unsupported: ## id cycle delay range expression"); }
        |       yP_POUNDPOUND '(' constExpr ')'
                        { $$ = $3;
                          BBUNSUP($<fl>1, "Unsupported: ## () cycle delay range expression"); }
        //                      // In 1800-2009 ONLY:
        //                      // IEEE: yP_POUNDPOUND constant_primary
        //                      // UNSUP: This causes a big grammer ambiguity
        //                      // as ()'s mismatch between primary and the following statement
        //                      // the sv-ac committee has been asked to clarify  (Mantis 1901)
        |       yP_POUNDPOUND anyrange
                        { $$ = new AstConst{$1, AstConst::BitFalse{}};
                          BBUNSUP($<fl>1, "Unsupported: ## range cycle delay range expression"); }
        |       yP_POUNDPOUND yP_BRASTAR ']'
                        { $$ = new AstConst{$1, AstConst::BitFalse{}};
                          BBUNSUP($<fl>1, "Unsupported: ## [*] cycle delay range expression"); }
        |       yP_POUNDPOUND yP_BRAPLUSKET
                        { $$ = new AstConst{$1, AstConst::BitFalse{}};
                          BBUNSUP($<fl>1, "Unsupported: ## [+] cycle delay range expression"); }
        ;

sequence_match_itemList<nodep>:  // IEEE: [sequence_match_item] part of sequence_expr
                sequence_match_item                     { $$ = $1; }
        |       sequence_match_itemList ',' sequence_match_item { $$ = addNextNull($1, $3); }
        ;

sequence_match_item<nodep>:  // ==IEEE: sequence_match_item
        //                      // IEEE says: operator_assignment
        //                      // IEEE says: inc_or_dec_expression
        //                      // IEEE says: subroutine_call
        //                      // This is the same list as...
                for_step_assignment                     { $$ = $1; }
        ;

boolean_abbrev<nodeExprp>:  // ==IEEE: boolean_abbrev
        //                      // IEEE: consecutive_repetition
                yP_BRASTAR constExpr ']'
                        { $$ = $2; BBUNSUP($<fl>1, "Unsupported: [*] boolean abbrev expression"); }
        |       yP_BRASTAR constExpr ':' constExpr ']'
                        { $$ = $2; BBUNSUP($<fl>1, "Unsupported: [*] boolean abbrev expression"); }
        |       yP_BRASTAR ']'
                        { $$ = new AstConst{$1, AstConst::BitFalse{}};
                          BBUNSUP($<fl>1, "Unsupported: [*] boolean abbrev expression"); }
        |       yP_BRAPLUSKET
                        { $$ = new AstConst{$1, AstConst::BitFalse{}};
                          BBUNSUP($<fl>1, "Unsupported: [+] boolean abbrev expression"); }
        //                      // IEEE: non_consecutive_repetition
        |       yP_BRAEQ constExpr ']'
                        { $$ = $2; BBUNSUP($<fl>1, "Unsupported: [= boolean abbrev expression"); }
        |       yP_BRAEQ constExpr ':' constExpr ']'
                        { $$ = $2; BBUNSUP($<fl>1, "Unsupported: [= boolean abbrev expression"); }
        //                      // IEEE: goto_repetition
        |       yP_BRAMINUSGT constExpr ']'
                        { $$ = $2; BBUNSUP($<fl>1, "Unsupported: [-> boolean abbrev expression"); }
        |       yP_BRAMINUSGT constExpr ':' constExpr ']'
                        { $$ = $2; BBUNSUP($<fl>1, "Unsupported: [-> boolean abbrev expression"); }
        ;

//************************************************
// Let

//************************************************
// Covergroup

covergroup_declaration<nodep>:  // ==IEEE: covergroup_declaration
                covergroup_declarationFront coverage_eventE ';'
        /*cont*/    coverage_spec_or_optionListE
        /*cont*/    yENDGROUP endLabelE
                        { $$ = $1;
                          SYMP->popScope($$);
                          GRAMMARP->endLabel($<fl>6, $1, $6); }
        |       covergroup_declarationFront '(' tf_port_listE ')'
        /*cont*/    coverage_eventE ';' coverage_spec_or_optionListE
        /*cont*/    yENDGROUP endLabelE
                        { $$ = $1;
                          SYMP->popScope($$);
                          GRAMMARP->endLabel($<fl>9, $1, $9); }
        ;

covergroup_declarationFront<classp>:  // IEEE: part of covergroup_declaration
                yCOVERGROUP idAny
                        { $$ = new AstClass{$<fl>2, *$2};
                          BBUNSUP($<fl>1, "Unsupported: covergroup");
                          SYMP->pushNew($<classp>$);
                          v3Global.setHasClasses(); }
        ;

cgexpr<nodeExprp>:  // IEEE-2012: covergroup_expression, before that just expression
                expr                                    { $$ = $1; }
        ;

coverage_spec_or_optionListE<nodep>:  // IEEE: [{coverage_spec_or_option}]
                /* empty */                             { $$ = nullptr; }
        |       coverage_spec_or_optionList             { $$ = $1; }
        ;

coverage_spec_or_optionList<nodep>:  // IEEE: {coverage_spec_or_option}
                coverage_spec_or_option                 { $$ = $1; }
        |       coverage_spec_or_optionList coverage_spec_or_option     { $$ = addNextNull($1, $2); }
        ;

coverage_spec_or_option<nodep>:  // ==IEEE: coverage_spec_or_option
        //                      // IEEE: coverage_spec
                cover_point                             { $$ = $1; }
        |       cover_cross                             { $$ = $1; }
        |       coverage_option ';'                     { $$ = $1; }
        |       error                                   { $$ = nullptr; }
        ;

coverage_option<nodep>:  // ==IEEE: coverage_option
        //                      // option/type_option aren't really keywords
                id/*yOPTION | yTYPE_OPTION*/ '.' idAny/*member_identifier*/ '=' expr
                        { // TODO: check that 'id' is 'option' or 'type_option'
                          $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: coverage option"); }
        ;

cover_point<nodep>:  // ==IEEE: cover_point
        //              // [ [ data_type_or_implicit ] cover_point_identifier ':' ] yCOVERPOINT
                yCOVERPOINT expr iffE bins_or_empty
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: cover point"); }
        //                      // IEEE-2012: class_scope before an ID
        |       id/*cover_point_id*/ ':' yCOVERPOINT expr iffE bins_or_empty
                        { $$ = nullptr; BBUNSUP($<fl>3, "Unsupported: cover point"); }
        //                      // data_type_or_implicit expansion
        |       data_type id/*cover_point_id*/ ':' yCOVERPOINT expr iffE bins_or_empty
                        { $$ = nullptr; BBUNSUP($<fl>4, "Unsupported: cover point"); }
        |       yVAR data_type id/*cover_point_id*/ ':' yCOVERPOINT expr iffE bins_or_empty
                        { $$ = nullptr; BBUNSUP($<fl>5, "Unsupported: cover point"); }
        |       yVAR implicit_typeE id/*cover_point_id*/ ':' yCOVERPOINT expr iffE bins_or_empty
                        { $$ = nullptr; BBUNSUP($<fl>5, "Unsupported: cover point"); }
        |       signingE rangeList id/*cover_point_id*/ ':' yCOVERPOINT expr iffE bins_or_empty
                        { $$ = nullptr; BBUNSUP($<fl>5, "Unsupported: cover point"); }
        |       signing id/*cover_point_id*/ ':' yCOVERPOINT expr iffE bins_or_empty
                        { $$ = nullptr; BBUNSUP($<fl>4, "Unsupported: cover point"); }
        //                      // IEEE-2012:
        |       bins_or_empty                           { $$ = $1; }
        ;

iffE<nodep>:  // IEEE: part of cover_point, others
                /* empty */                             { $$ = nullptr; }
        |       yIFF '(' expr ')'
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: cover 'iff'"); }
        ;

bins_or_empty<nodep>:  // ==IEEE: bins_or_empty
                '{' bins_or_optionsList '}'             { $$ = $2; }
        |       '{' '}'                                 { $$ = nullptr; }
        |       ';'                                     { $$ = nullptr; }
        ;

bins_or_optionsList<nodep>:  // IEEE: { bins_or_options ';' }
                bins_or_options ';'                     { $$ = $1; }
        |       bins_or_optionsList bins_or_options ';' { $$ = addNextNull($1, $2); }
        ;

bins_or_options<nodep>:  // ==IEEE: bins_or_options
        //                      // Superset of IEEE - we allow []'s in more places
                coverage_option                         { $$ = $1; }
        //                      // Can't use wildcardE as results in conflicts
        |       bins_keyword id/*bin_identifier*/ bins_orBraE '=' '{' open_range_list '}' iffE
                        { $$ = nullptr; BBUNSUP($<fl>4, "Unsupported: cover bin specification"); }
        |       bins_keyword id/*bin_identifier*/ bins_orBraE '=' '{' open_range_list '}' yWITH__CUR '{' cgexpr '}' iffE
                        { $$ = nullptr; BBUNSUP($<fl>8, "Unsupported: cover bin 'with' specification"); }
        |       yWILDCARD bins_keyword id/*bin_identifier*/ bins_orBraE '=' '{' open_range_list '}' iffE
                        { $$ = nullptr; BBUNSUP($<fl>5, "Unsupported: cover bin 'wildcard' specification"); }
        |       yWILDCARD bins_keyword id/*bin_identifier*/ bins_orBraE '=' '{' open_range_list '}' yWITH__CUR '{' cgexpr '}' iffE
                        { $$ = nullptr; BBUNSUP($<fl>9, "Unsupported: cover bin 'wildcard' 'with' specification"); }
        //
        //                      // cgexpr part of trans_list
        |       bins_keyword id/*bin_identifier*/ bins_orBraE '=' trans_list iffE
                        { $$ = nullptr; BBUNSUP($<fl>4, "Unsupported: cover bin trans list"); }
        |       yWILDCARD bins_keyword id/*bin_identifier*/ bins_orBraE '=' trans_list iffE
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: cover bin 'wildcard' trans list"); }
        //
        |       bins_keyword id/*bin_identifier*/ bins_orBraE '=' yDEFAULT iffE
                        { $$ = nullptr; BBUNSUP($<fl>5, "Unsupported: cover bin 'default'"); }
        |       bins_keyword id/*bin_identifier*/ bins_orBraE '=' yDEFAULT ySEQUENCE iffE
                        { $$ = nullptr; BBUNSUP($<fl>6, "Unsupported: cover bin 'default' 'sequence'"); }
        ;

bins_orBraE<nodep>:  // IEEE: part of bins_or_options:
                /* empty */                             { $$ = nullptr; }
        |       '[' ']'                                 { $$ = nullptr; /*UNSUP*/ }
        |       '[' cgexpr ']'                          { $$ = nullptr; /*UNSUP*/ }
        ;

bins_keyword<fl>:  // ==IEEE: bins_keyword
                yBINS                                   { $$ = $1; /*UNSUP*/ }
        |       yILLEGAL_BINS                           { $$ = $1; /*UNSUP*/ }
        |       yIGNORE_BINS                            { $$ = $1; /*UNSUP*/ }
        ;

trans_list<nodep>:  // ==IEEE: trans_list
                '(' trans_set ')'                       { $$ = $2; }
        |       trans_list ',' '(' trans_set ')'        { $$ = addNextNull($1, $4); }
        ;

trans_set<nodep>:  // ==IEEE: trans_set
                trans_range_list                        { $$ = $1; }
        //                      // Note the { => } in the grammer, this is really a list
        |       trans_set yP_EQGT trans_range_list
                        { $$ = $1; BBUNSUP($<fl>2, "Unsupported: cover trans set '=>'"); }
        ;

trans_range_list<nodep>:  // ==IEEE: trans_range_list
                trans_item                              { $$ = $1; }
        |       trans_item yP_BRASTAR cgexpr ']'
                        { $$ = nullptr; BBUNSUP($<fl>2, "Unsupported: cover '[*'"); }
        |       trans_item yP_BRASTAR cgexpr ':' cgexpr ']'
                        { $$ = nullptr; BBUNSUP($<fl>2, "Unsupported: cover '[*'"); }
        |       trans_item yP_BRAMINUSGT cgexpr ']'
                        { $$ = nullptr; BBUNSUP($<fl>2, "Unsupported: cover '[->'"); }
        |       trans_item yP_BRAMINUSGT cgexpr ':' cgexpr ']'
                        { $$ = nullptr; BBUNSUP($<fl>2, "Unsupported: cover '[->'"); }
        |       trans_item yP_BRAEQ cgexpr ']'
                        { $$ = nullptr; BBUNSUP($<fl>2, "Unsupported: cover '[='"); }
        |       trans_item yP_BRAEQ cgexpr ':' cgexpr ']'
                        { $$ = nullptr; BBUNSUP($<fl>2, "Unsupported: cover '[='"); }
        ;

trans_item<nodep>:  // ==IEEE: range_list
                covergroup_range_list                   { $$ = $1; }
        ;

covergroup_range_list<nodep>:  // ==IEEE: covergroup_range_list
                covergroup_value_range                  { $$ = $1; }
        |       covergroup_range_list ',' covergroup_value_range        { $$ = addNextNull($1, $3); }
        ;


cover_cross<nodep>:  // ==IEEE: cover_cross
                id/*cover_point_identifier*/ ':' yCROSS list_of_cross_items iffE cross_body
                        { $$ = nullptr; BBUNSUP($<fl>3, "Unsupported: cross"); }
        |       yCROSS list_of_cross_items iffE cross_body
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: cross"); }
        ;

list_of_cross_items<nodep>:  // ==IEEE: list_of_cross_items
                cross_item ',' cross_item               { $$ = addNextNull($1, $3); }
        |       cross_item ',' cross_item ',' cross_itemList
                        { $$ = addNextNull(addNextNull($1, $3), $5); }
        ;

cross_itemList<nodep>:  // IEEE: part of list_of_cross_items
                cross_item                              { $$ = $1; }
        |       cross_itemList ',' cross_item           { $$ = addNextNull($1, $3); }
        ;

cross_item<nodep>:  // ==IEEE: cross_item
                idAny/*cover_point_identifier or variable_identifier*/  { $$ = nullptr; /*UNSUP*/ }
        ;

cross_body<nodep>:  // ==IEEE: cross_body
                '{' '}'                                 { $$ = nullptr; }
        //                      // IEEE-2012: No semicolon here, mistake in spec
        |       '{' cross_body_itemSemiList '}'         { $$ = $2; }
        |       ';'                                     { $$ = nullptr; }
        ;

cross_body_itemSemiList<nodep>:  // IEEE: part of cross_body
                cross_body_item ';'                     { $$ = $1; }
        |       cross_body_itemSemiList cross_body_item ';'  { $$ = addNextNull($1, $2); }
        ;

cross_body_item<nodep>:  // ==IEEE: cross_body_item
        //                      // IEEE: our semicolon is in the list
        //                      // IEEE: bins_selection_or_option
                coverage_option                         { $$ = $1; }
        //                      // IEEE: bins_selection
        |       function_declaration
                        { $$ = $1; BBUNSUP($1->fileline(), "Unsupported: coverage cross 'function' declaration"); }
        |       bins_keyword idAny/*new-bin_identifier*/ '=' select_expression iffE
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: coverage cross bin"); }
        ;

select_expression<nodep>:  // ==IEEE: select_expression
        //                      // IEEE: select_condition expanded here
                yBINSOF '(' bins_expression ')'
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: coverage select expression 'binsof'"); }
        |       '!' yBINSOF '(' bins_expression ')'
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: coverage select expression 'binsof'"); }
        |       yBINSOF '(' bins_expression ')' yINTERSECT '{' covergroup_range_list '}'
                        { $$ = nullptr; BBUNSUP($5, "Unsupported: coverage select expression 'intersect'"); }
        |       '!' yBINSOF '(' bins_expression ')' yINTERSECT '{' covergroup_range_list '}'    { }
                        { $$ = nullptr; BBUNSUP($5, "Unsupported: coverage select expression 'intersect'"); }
        |       yWITH__PAREN '(' cgexpr ')'
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: coverage select expression with"); }
        |       '!' yWITH__PAREN '(' cgexpr ')'
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: coverage select expression with"); }
        //                      // IEEE-2012: Need clarification as to precedence
        //UNSUP yWITH__PAREN '(' cgexpr ')' yMATCHES cgexpr    { }
        //                      // IEEE-2012: Need clarification as to precedence
        //UNSUP '!' yWITH__PAREN '(' cgexpr ')' yMATCHES cgexpr { }
        //
        |       '(' select_expression ')'                       { $$ = $2; }
        |       select_expression yP_ANDAND select_expression
                        { $$ = nullptr; BBUNSUP($2, "Unsupported: coverage select expression '&&'"); }
        |       select_expression yP_OROR   select_expression
                        { $$ = nullptr; BBUNSUP($2, "Unsupported: coverage select expression '||'"); }
        //                      // IEEE-2012: cross_identifier
        //                      // Part of covergroup_expression - generic identifier
        //                      // IEEE-2012: Need clarification as to precedence
        //UNSUP  cgexpr  { $$ = nullptr; BBUNSUP($1, "Unsupported: coverage select expression"); }
        //
        //                      // Need precedence fix
        //UNSUP  cgexpr yMATCHES cgexpr    {..}
        ;

bins_expression<nodep>:  // ==IEEE: bins_expression
        //                      // "cover_point_identifier" and "variable_identifier" look identical
                id/*variable_identifier or cover_point_identifier*/        { $$ = nullptr; /*UNSUP*/ }
        |       id/*cover_point_identifier*/ '.' idAny/*bins_identifier*/  { $$ = nullptr; /*UNSUP*/ }
        ;

coverage_eventE<nodep>:  // IEEE: [ coverage_event ]
                /* empty */                             { $$ = nullptr; }
        |       clocking_event
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: coverage clocking event"); }
        |       yWITH__ETC yFUNCTION idAny/*"sample"*/ '(' tf_port_listE ')'
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: coverage 'with' 'function'"); }
        |       yP_ATAT '(' block_event_expression ')'
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: coverage '@@' events"); }
        ;

block_event_expression<nodep>:  // ==IEEE: block_event_expression
                block_event_expressionTerm              { $$ = nullptr; /*UNSUP @@*/ }
        |       block_event_expression yOR block_event_expressionTerm   { $$ = nullptr; /*UNSUP @@*/ }
        ;

block_event_expressionTerm<nodep>:  // IEEE: part of block_event_expression
                yBEGIN hierarchical_btf_identifier      { $$ = nullptr; /*UNSUP @@*/ }
        |       yEND   hierarchical_btf_identifier      { $$ = nullptr; /*UNSUP @@*/ }
        ;

hierarchical_btf_identifier<nodep>:  // ==IEEE: hierarchical_btf_identifier
        //                      // hierarchical_tf_identifier + hierarchical_block_identifier
        //                      // method_identifier
                packageClassScopeE idAny                { $$ = nullptr; /*UNSUP*/ }
        ;

//**********************************************************************
// Randsequence

randsequence_statement<nodep>:  // ==IEEE: randsequence_statement
                yRANDSEQUENCE '(' ')' productionList yENDSEQUENCE
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: randsequence"); }
        |       yRANDSEQUENCE '(' id/*production_identifier*/ ')' productionList yENDSEQUENCE
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: randsequence"); }
        ;

productionList<nodep>:  // IEEE: production+
                production                              { $$ = $1; }
        |       productionList production               { $$ = addNextNull($1, $2); }
        ;

production<nodep>:  // ==IEEE: production
                productionFront ':' rs_ruleList ';'
                        { // TODO makes a function, probably want a new Ast type instead
                          SYMP->popScope($$);
                          $$ = nullptr; BBUNSUP($<fl>2, "Unsupported: randsequence production"); }
        ;

productionFront<nodeFTaskp>:  // IEEE: part of production
                funcId/*production_identifier*/         { $$ = $1; }
        |       funcId '(' tf_port_listE ')'            { $$ = $1; $$->addStmtsp($3); }
        ;

rs_ruleList<nodep>:  // IEEE: rs_rule+ part of production
                rs_rule                                 { $$ = $1; }
        |       rs_ruleList '|' rs_rule                 { $$ = addNextNull($1, $3); }
        ;

rs_rule<nodep>:  // ==IEEE: rs_rule
                rs_production_list                      { $$ = $1; }
        |       rs_production_list yP_COLONEQ weight_specification
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: randsequence rule"); }
        |       rs_production_list yP_COLONEQ weight_specification rs_code_block
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: randsequence rule"); }
        ;

rs_production_list<nodep>:  // ==IEEE: rs_production_list
                rs_prodList                             { $$ = $1; }
        |       yRAND yJOIN /**/         production_item production_itemList
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: randsequence production list"); }
        |       yRAND yJOIN '(' expr ')' production_item production_itemList
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: randsequence production list"); }
        ;

weight_specification<nodeExprp>:  // ==IEEE: weight_specification
                intnumAsConst                           { $$ = $1; }
        |       idClassSel/*ps_identifier*/             { $$ = $1; }
        |       '(' expr ')'                            { $$ = $2; }
        ;

rs_code_block<nodep>:  // ==IEEE: rs_code_block
                '{' '}'                                 { $$ = nullptr; }
        |       '{' rs_code_blockItemList '}'           { $$ = $2; }
        ;

rs_code_blockItemList<nodep>:  // IEEE: part of rs_code_block
                rs_code_blockItem                       { $$ = $1; }
        |       rs_code_blockItemList rs_code_blockItem         { $$ = addNextNull($1, $2); }
        ;

rs_code_blockItem<nodep>:  // IEEE: part of rs_code_block
                data_declaration                        { $$ = $1; }
        |       stmt                                    { $$ = $1; }
        ;

rs_prodList<nodep>:  // IEEE: rs_prod+
                rs_prod                                 { $$ = $1; }
        |       rs_prodList rs_prod                     { $$ = addNextNull($1, $2); }
        ;

rs_prod<nodep>:  // ==IEEE: rs_prod
                production_item                         { $$ = $1; }
        |       rs_code_block                           { $$ = $1; }
        //                      // IEEE: rs_if_else
        |       yIF '(' expr ')' production_item %prec prLOWER_THAN_ELSE
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: randsequence if"); }
        |       yIF '(' expr ')' production_item yELSE production_item
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: randsequence if"); }
        //                      // IEEE: rs_repeat
        |       yREPEAT '(' expr ')' production_item
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: randsequence repeat"); }
        //                      // IEEE: rs_case
        |       yCASE '(' expr ')' rs_case_itemList yENDCASE
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: randsequence case"); }
        ;

production_itemList<nodep>:  // IEEE: production_item+
                production_item                         { $$ = $1; }
        |       production_itemList production_item     { $$ = addNextNull($1, $2); }
        ;

production_item<nodep>:  // ==IEEE: production_item
                id/*production_identifier*/
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: randsequence production id"); }
        |       id/*production_identifier*/ '(' list_of_argumentsE ')'
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: randsequence production id"); }
        ;

rs_case_itemList<nodep>:  // IEEE: rs_case_item+
                rs_case_item                            { $$ = $1; }
        |       rs_case_itemList rs_case_item           { $$ = addNextNull($1, $2); }
        ;

rs_case_item<nodep>:  // ==IEEE: rs_case_item
                caseCondList ':' production_item ';'
                        { $$ = nullptr; BBUNSUP($<fl>2, "Unsupported: randsequence case item"); }
        |       yDEFAULT production_item ';'
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: randsequence case item"); }
        |       yDEFAULT ':' production_item ';'
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: randsequence case item"); }
        ;

//**********************************************************************
// Checker

checker_declaration<nodep>:  // ==IEEE: part of checker_declaration
                checkerFront checker_port_listE ';'
                        checker_or_generate_itemListE yENDCHECKER endLabelE
                        { $$ = $1;
                          $1->modTrace(GRAMMARP->allTracingOn($1->fileline()));
                          if ($2) $1->addStmtsp($2);
                          if ($4) $1->addStmtsp($4);
                          SYMP->popScope($1);
                          GRAMMARP->endLabel($<fl>6, $1, $6); }
        ;

checkerFront<nodeModulep>:  // IEEE: part of checker_declaration
                yCHECKER idAny/*checker_identifier*/
                        { BBUNSUP($<fl>1, "Unsupported: checker");
                          // TODO should be AstChecker not AstModule
                          $$ = new AstModule{$<fl>2, *$2};
                          $$->modTrace(GRAMMARP->allTracingOn($$->fileline()));
                          $$->timeunit(PARSEP->timeLastUnit());
                          $$->unconnectedDrive(PARSEP->unconnectedDrive());
                          SYMP->pushNew($$); }
        ;

checker_port_listE<nodep>:  // IEEE: [ ( [ checker_port_list ] ) ]
        //                      // checker_port_item is basically the same as property_port_item, minus yLOCAL::
        //                      // Want to bet 1800-2012 adds local to checkers?
                property_port_listE                     { $$ = $1; }
        ;

checker_or_generate_itemListE<nodep>:  // IEEE: [{ checker_or_generate_itemList }]
                /* empty */                             { $$ = nullptr; }
        |       checker_or_generate_itemList            { $$ = $1; }
        ;

checker_or_generate_itemList<nodep>:  // IEEE: { checker_or_generate_itemList }
                checker_or_generate_item                { $$ = $1; }
        |       checker_or_generate_itemList checker_or_generate_item   { $$ = addNextNull($1, $2); }
        ;

checker_or_generate_item<nodep>:  // ==IEEE: checker_or_generate_item
                checker_or_generate_item_declaration    { $$ = $1; }
        |       initial_construct                       { $$ = $1; }
        //                      // IEEE: checker_construct
        |       always_construct                        { $$ = $1; }
        |       final_construct                         { $$ = $1; }
        |       assertion_item                          { $$ = $1; }
        |       continuous_assign                       { $$ = $1; }
        |       checker_generate_item                   { $$ = $1; }
        ;

checker_or_generate_item_declaration<nodep>:  // ==IEEE: checker_or_generate_item_declaration
                data_declaration
                        { $$ = $1; BBUNSUP($1, "Unsupported: checker data declaration"); }
        |       yRAND data_declaration
                        { $$ = $2; BBUNSUP($1, "Unsupported: checker rand"); }
        |       function_declaration                    { $$ = $1; }
        |       checker_declaration
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: recursive checker"); }
        |       assertion_item_declaration              { $$ = $1; }
        |       covergroup_declaration                  { $$ = $1; }
        //      // IEEE deprecated: overload_declaration
        |       genvar_declaration                      { $$ = $1; }
        |       clocking_declaration                    { $$ = $1; }
        |       yDEFAULT yCLOCKING id/*clocking_identifier*/ ';'        { }
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: checker default clocking"); }
        |       yDEFAULT yDISABLE yIFF expr/*expression_or_dist*/ ';'   { }
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: checker default disable iff"); }
        |       ';'                                     { $$ = nullptr; }
        ;

checker_generate_item<nodep>:  // ==IEEE: checker_generate_item
        //                      // Specialized for checker so need "c_" prefixes here
                c_loop_generate_construct               { $$ = $1; }
        |       c_conditional_generate_construct        { $$ = $1; }
        |       c_generate_region                       { $$ = $1; }
        //
        |       elaboration_system_task                 { $$ = $1; }
        ;

//UNSUPchecker_instantiation<nodep>:
//UNSUP //                      // Only used for procedural_assertion_item's
//UNSUP //                      // Version in concurrent_assertion_item looks like etcInst
//UNSUP //                      // Thus instead of *_checker_port_connection we can use etcInst's cellpinListE
//UNSUP         id/*checker_identifier*/ id '(' cellpinListE ')' ';'     { }
//UNSUP ;

//**********************************************************************
// Class

class_declaration<nodep>:       // ==IEEE: part of class_declaration
        //                      // IEEE-2012: using this also for interface_class_declaration
        //                      // The classExtendsE rule relys on classFront having the
        //                      // new class scope correct via classFront
                classFront parameter_port_listE classExtendsE classImplementsE ';'
        /*mid*/         { // Allow resolving types declared in base extends class
                          if ($<scp>3) SYMP->importExtends($<scp>3);
                        }
        /*cont*/    class_itemListE yENDCLASS endLabelE
                        { $$ = $1; $1->addMembersp($2);
                          if ($2) $1->isParameterized(true);
                          $1->addExtendsp($3);
                          $1->addExtendsp($4);
                          $1->addMembersp($7);
                          SYMP->popScope($$);
                          GRAMMARP->endLabel($<fl>9, $1, $9); }
        ;

classFront<classp>:             // IEEE: part of class_declaration
                classVirtualE yCLASS lifetimeE idAny/*class_identifier*/
                        { $$ = new AstClass{$2, *$4};
                          $$->isVirtual($1);
                          $$->lifetime($3);
                          SYMP->pushNew($<classp>$);
                          v3Global.setHasClasses(); }
        //                      // IEEE: part of interface_class_declaration
        |       yINTERFACE yCLASS lifetimeE idAny/*class_identifier*/
                        { $$ = new AstClass{$2, *$4};
                          $$->isInterfaceClass(true);
                          $$->lifetime($3);
                          SYMP->pushNew($<classp>$);
                          v3Global.setHasClasses(); }
        ;

classVirtualE<cbool>:
                /* empty */                             { $$ = false; }
        |       yVIRTUAL__CLASS                         { $$ = true; }
        ;

classExtendsE<classExtendsp>:           // IEEE: part of class_declaration
        //                      // The classExtendsE rule relys on classFront having the
        //                      // new class scope correct via classFront
                /* empty */                             { $$ = nullptr; $<scp>$ = nullptr; }
        |       yEXTENDS classExtendsList               { $$ = $2; $<scp>$ = $<scp>2; }
        ;

classExtendsList<classExtendsp>:        // IEEE: part of class_declaration
                classExtendsOne                         { $$ = $1; $<scp>$ = $<scp>1; }
        |       classExtendsList ',' classExtendsOne    { $$ = addNextNull($1, $3); $<scp>$ = $<scp>3; }
        ;

classExtendsOne<classExtendsp>:         // IEEE: part of class_declaration
                class_typeExtImpList
                        { $$ = new AstClassExtends{$1->fileline(), $1, GRAMMARP->m_inImplements};
                          $<scp>$ = $<scp>1; }
        ;

classImplementsE<classExtendsp>:        // IEEE: part of class_declaration
        //                      // All 1800-2012
                /* empty */                             { $$ = nullptr; $<scp>$ = nullptr; }
        |       yIMPLEMENTS
        /*mid*/        { GRAMMARP->m_inImplements = true; $<scp>$ = nullptr; }
        /*cont*/    classImplementsList
                       { $$ = $3; $<scp>$ = $<scp>3;
                         GRAMMARP->m_inImplements = false; }
        ;

classImplementsList<classExtendsp>:     // IEEE: part of class_declaration
        //                      // All 1800-2012
                classExtendsOne                         { $$ = $1; $<scp>$ = $<scp>1; }
        |       classImplementsList ',' classExtendsOne
                       { $$ = addNextNull($1, $3); $<scp>$ = $<scp>3; }
        ;

class_typeExtImpList<nodeExprp>:  // IEEE: class_type: "[package_scope] id [ parameter_value_assignment ]"
        //                      // but allow yaID__aTYPE for extends/implements
        //                      // If you follow the rules down, class_type is really a list via ps_class_identifier
                class_typeExtImpOne                     { $$ = $1; $<scp>$ = $<scp>1; }
        |       class_typeExtImpList yP_COLONCOLON class_typeExtImpOne
                        { $$ = new AstDot{$<fl>1, true, $1, $3};
                          $<scp>$ = $<scp>3; }
        ;

class_typeExtImpOne<nodeExprp>:  // part of IEEE: class_type, where we either get a package_scope component or class
        //                      // If you follow the rules down, class_type is really a list via ps_class_identifier
        //                      // Not listed in IEEE, but see bug627 any parameter type maybe a class
        //                      // If idAny below is a class, parameter_value is legal
        //                      // If idAny below is a package, parameter_value is not legal
        //                      // If idAny below is otherwise, not legal
                idAny
        /*mid*/         { /* no nextId as not refing it above this*/ }
        /*cont*/    parameter_value_assignmentE
                        { $$ = new AstClassOrPackageRef{$<fl>1, *$1, $<scp>1, $3};
                          $<scp>$ = $<scp>1; }
        |       idCC
        /*mid*/         { /* no nextId as not refing it above this*/ }
        /*cont*/    parameter_value_assignmentE
                        { $$ = new AstClassOrPackageRef{$<fl>1, *$1, $<scp>1, $3};
                          $<scp>$ = $<scp>1; }
        //
        //                      // package_sopeIdFollows expanded
        |       yD_UNIT yP_COLONCOLON
                        { $$ = new AstClassOrPackageRef{$<fl>1, "$unit", nullptr, nullptr};
                          $<scp>$ = nullptr;  // No purpose otherwise, every symtab can see root
                          SYMP->nextId(PARSEP->rootp()); }
        //
        |       yLOCAL__COLONCOLON yP_COLONCOLON
                        { $$ = new AstClassOrPackageRef{$<fl>1, "local::", nullptr, nullptr};
                          $<scp>$ = nullptr;  // UNSUP
                          SYMP->nextId(PARSEP->rootp());
                          BBUNSUP($1, "Unsupported: Randomize 'local::'"); }
        ;

//=========
// Package scoping - to traverse the symbol table properly, the final identifer
// must be included in the rules below.
// Each of these must end with {symsPackageDone | symsClassDone}

//=== Below rules assume special scoping per above

packageClassScopeNoId<nodep>:   // IEEE: [package_scope] not followed by yaID
                packageClassScope                       { $$ = $1; $<scp>$ = $<scp>1; SYMP->nextId(nullptr); }
        ;

packageClassScopeE<nodeExprp>:  // IEEE: [package_scope]
        //                      // IMPORTANT: The lexer will parse the following ID to be in the found package
        //                      //     if not needed must use packageClassScopeNoId
        //                      // TODO: To support classes should return generic type, not packagep
        //                      // class_qualifier := [ yLOCAL '::'  ] [ implicit_class_handle '.'  class_scope ]
                /* empty */                             { $$ = nullptr; $<scp>$ = nullptr; }
        |       packageClassScope                       { $$ = $1; $<scp>$ = $<scp>1; }
        ;

packageClassScope<nodeExprp>:   // IEEE: class_scope
        //                      // IEEE: "class_type yP_COLONCOLON"
        //                      // IMPORTANT: The lexer will parse the following ID to be in the found package
        //                      //     if not needed must use packageClassScopeNoId
        //                      // In this parser <package_identifier>:: and <class_identifier>:: are indistinguishible
        //                      // This copies <scp> to document it is important
                packageClassScopeList                   { $$ = $1; $<scp>$ = $<scp>1; }
        |       localNextId yP_COLONCOLON               { $$ = $1; $<scp>$ = $<scp>1; }
        |       dollarUnitNextId yP_COLONCOLON          { $$ = $1; $<scp>$ = $<scp>1; }
        |       dollarUnitNextId yP_COLONCOLON packageClassScopeList
                        { $$ = new AstDot{$2, true, $1, $3}; $<scp>$ = $<scp>3; }
        ;

packageClassScopeList<nodeExprp>:   // IEEE: class_type: "id [ parameter_value_assignment ]" but allow yaID__aTYPE
        //                      // Or IEEE: [package_scope]
        //                      // IMPORTANT: The lexer will parse the following ID to be in the found package
        //                      //     if not needed must use packageClassScopeNoId
        //                      // In this parser <package_identifier>:: and <class_identifier>:: are indistinguishible
        //                      // If you follow the rules down, class_type is really a list via ps_class_identifier
                packageClassScopeItem                   { $$ = $1; $<scp>$ = $<scp>1; }
        |       packageClassScopeList packageClassScopeItem
                        { $$ = new AstDot{$<fl>2, true, $1, $2}; $<scp>$ = $<scp>2; }
        ;

packageClassScopeItem<nodeExprp>:   // IEEE: package_scope or [package_scope]::[class_scope]
        //                      // IMPORTANT: The lexer will parse the following ID to be in the found package
        //                      //     if not needed must use packageClassScopeNoId
        //                      // IEEE: class_type: "id [ parameter_value_assignment ]" but allow yaID__aTYPE
        //                      //vv mid rule action needed otherwise we might not have NextId in time to parse the id token
                idCC
        /*mid*/         { SYMP->nextId($<scp>1); }
        /*cont*/    yP_COLONCOLON
                        { $$ = new AstClassOrPackageRef{$<fl>1, *$1, $<scp>1, nullptr}; $<scp>$ = $<scp>1; }
        //
        |       idCC parameter_value_assignment
        /*mid*/         { SYMP->nextId($<scp>1); }   // Change next *after* we handle parameters, not before
        /*cont*/    yP_COLONCOLON
                        { $$ = new AstClassOrPackageRef{$<fl>1, *$1, $<scp>1, $2}; $<scp>$ = $<scp>1; }
        ;

dollarUnitNextId<nodeExprp>:    // $unit
        //                      // IMPORTANT: The lexer will parse the following ID to be in the found package
        //                      //     if not needed must use packageClassScopeNoId
        //                      // Must call nextId without any additional tokens following
                yD_UNIT
                        { $$ = new AstClassOrPackageRef{$1, "$unit", PARSEP->unitPackage($<fl>1), nullptr};
                          SYMP->nextId(PARSEP->rootp()); }
        ;

localNextId<nodeExprp>:         // local
        //                      // IMPORTANT: The lexer will parse the following ID to be in the found package
        //                      //     if not needed must use packageClassScopeNoId
        //                      // Must call nextId without any additional tokens following
                yLOCAL__COLONCOLON
                        { $$ = new AstClassOrPackageRef{$1, "local::", PARSEP->unitPackage($<fl>1), nullptr};
                          SYMP->nextId(PARSEP->rootp());
                          BBUNSUP($<fl>1, "Unsupported: Randomize 'local::'"); }
        ;

//^^^=========

class_itemListE<nodep>:
                /* empty */                             { $$ = nullptr; }
        |       class_itemList                          { $$ = $1; }
        ;

class_itemList<nodep>:
                class_item                              { $$ = $1; }
        |       class_itemList class_item               { $$ = addNextNull($1, $2); }
        ;

class_item<nodep>:                      // ==IEEE: class_item
                class_property                          { $$ = $1; }
        |       class_method                            { $$ = $1; }
        |       class_constraint                        { $$ = $1; }
        //
        |       class_declaration
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: class within class"); }
        |       timeunits_declaration                   { $$ = $1; }
        |       covergroup_declaration
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: covergroup within class"); }
        //                      // local_parameter_declaration under parameter_declaration
        |       parameter_declaration ';'               { $$ = $1; }
        |       ';'                                     { $$ = nullptr; }
        //
        |       error ';'                               { $$ = nullptr; }
        ;

class_method<nodep>:            // ==IEEE: class_method
                memberQualListE task_declaration        { $$ = $2; $1.applyToNodes($2); }
        |       memberQualListE function_declaration    { $$ = $2; $1.applyToNodes($2); }
        |       yPURE yVIRTUAL__ETC memberQualListE method_prototype ';'
                        { $$ = $4; $3.applyToNodes($4); $4->pureVirtual(true); $4->isVirtual(true); }
        |       yEXTERN memberQualListE method_prototype ';'
                        { $$ = $3; $2.applyToNodes($3); $3->isExternProto(true); }
        //                      // IEEE: "method_qualifierE class_constructor_declaration"
        //                      // part of function_declaration
        |       yEXTERN memberQualListE class_constructor_prototype
                        { $$ = $3; $2.applyToNodes($3); $3->isExternProto(true); }
        ;

// IEEE: class_constructor_prototype
// See function_declaration

memberQualListE<qualifiers>:    // Called from class_property for all qualifiers before yVAR
        //                      // Also before method declarations, to prevent grammar conflict
        //                      // Thus both types of qualifiers (method/property) are here
                /*empty*/                               { $$ = VMemberQualifiers::none(); }
        |       memberQualList                          { $$ = $1; }
        ;

memberQualList<qualifiers>:
                memberQualOne                           { $$ = $1; }
        |       memberQualList memberQualOne            { $$ = VMemberQualifiers::combine($1, $2); }
        ;

memberQualOne<qualifiers>:                      // IEEE: property_qualifier + method_qualifier
        //                      // Part of method_qualifier and property_qualifier
        //                      // IMPORTANT: yPROTECTED | yLOCAL is in a lex rule
                yPROTECTED                              { $$ = VMemberQualifiers::none(); $$.m_protected = true; }
        |       yLOCAL__ETC                             { $$ = VMemberQualifiers::none(); $$.m_local = true; }
        |       ySTATIC__ETC                            { $$ = VMemberQualifiers::none(); $$.m_static = true; }
        //                      // Part of method_qualifier only
        |       yVIRTUAL__ETC                           { $$ = VMemberQualifiers::none(); $$.m_virtual = true; }
        //                      // Part of property_qualifier only
        |       random_qualifier                        { $$ = $1; }
        //                      // Part of lifetime, but here as ySTATIC can be in different positions
        |       yAUTOMATIC                              { $$ = VMemberQualifiers::none(); $$.m_automatic = true; }
        //                      // Part of data_declaration, but not in data_declarationVarFrontClass
        |       yCONST__ETC                             { $$ = VMemberQualifiers::none(); $$.m_const = true; }
        ;

//**********************************************************************
// Constraints

class_constraint<nodep>:  // ==IEEE: class_constraint
        //                      // IEEE: constraint_declaration
        //                      // UNSUP: We have the unsupported warning on the randomize() call, so don't bother on
        //                      // constraint blocks. When we support randomize we need to make AST nodes for below rules
                constraintStaticE yCONSTRAINT idAny constraint_block
                        { // Variable so we can link and later ignore constraint_mode() methods
                          $$ = new AstVar{$<fl>3, VVarType::MEMBER, *$3, VFlagBitPacked{}, 1};
                          $2->v3warn(CONSTRAINTIGN, "Constraint ignored (unsupported)"); }
        //                      // IEEE: constraint_prototype + constraint_prototype_qualifier
        |       constraintStaticE yCONSTRAINT idAny ';'
                        { $$ = nullptr; }
        |       yEXTERN constraintStaticE yCONSTRAINT idAny ';'
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: extern constraint"); }
        |       yPURE constraintStaticE yCONSTRAINT idAny ';'
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: pure constraint"); }
        ;

constraint_block<nodep>:  // ==IEEE: constraint_block
                '{' constraint_block_itemList '}'               { $$ = $2; }
        ;

constraint_block_itemList<nodep>:  // IEEE: { constraint_block_item }
                constraint_block_item                           { $$ = $1; }
        |       constraint_block_itemList constraint_block_item { $$ = addNextNull($1, $2); }
        ;

constraint_block_item<nodep>:  // ==IEEE: constraint_block_item
                constraint_expression                           { $$ = $1; }
        |       ySOLVE solve_before_list yBEFORE solve_before_list ';'
                        { $$ = nullptr; BBUNSUP($2, "Unsupported: solve before"); }
        ;

solve_before_list<nodep>:  // ==IEEE: solve_before_list
                constraint_primary                              { $$ = $1; }
        |       solve_before_list ',' constraint_primary        { $$ = addNextNull($1, $3); }
        ;

constraint_primary<nodep>:  // ==IEEE: constraint_primary
        //                      // exprScope more general than:
        //                      // [ implicit_class_handle '.' | class_scope ] hierarchical_identifier select
                exprScope                                       { $$ = $1; }
        ;

constraint_expressionList<nodep>:  // ==IEEE: { constraint_expression }
                constraint_expression                           { $$ = $1; }
        |       constraint_expressionList constraint_expression { $$ = addNextNull($1, $2); }
        ;

constraint_expression<nodep>:  // ==IEEE: constraint_expression
                expr/*expression_or_dist*/ ';'          { $$ = $1; }
        //                      // 1800-2012:
        |       ySOFT expr/*expression_or_dist*/ ';'    { $$ = nullptr; /*UNSUP-no-UVM*/ }
        //                      // 1800-2012:
        //                      // IEEE: uniqueness_constraint ';'
        |       yUNIQUE '{' open_range_list '}'         { $$ = nullptr; /*UNSUP-no-UVM*/ }
        //                      // IEEE: expr yP_MINUSGT constraint_set
        //                      // Conflicts with expr:"expr yP_MINUSGT expr"; rule moved there
        //
        |       yIF '(' expr ')' constraint_set %prec prLOWER_THAN_ELSE { $$ = nullptr; /*UNSUP-UVM*/ }
        |       yIF '(' expr ')' constraint_set yELSE constraint_set    { $$ = nullptr; /*UNSUP-UVM*/ }
        //                      // IEEE says array_identifier here, but dotted accepted in VMM + 1800-2009
        |       yFOREACH '(' idClassSelForeach ')' constraint_set       { $$ = nullptr; /*UNSUP-UVM*/ }
        //                      // soft is 1800-2012
        |       yDISABLE ySOFT expr/*constraint_primary*/ ';'   { $$ = nullptr; /*UNSUP-no-UVM*/ }
        ;

constraint_set<nodep>:  // ==IEEE: constraint_set
                constraint_expression                   { $$ = $1; }
        |       '{' constraint_expressionList '}'       { $$ = $2; }
        ;

dist_list<nodep>:  // ==IEEE: dist_list
                dist_item                               { $$ = $1; }
        |       dist_list ',' dist_item                 { $$ = addNextNull($1, $3); }
        ;

dist_item<nodep>:  // ==IEEE: dist_item + dist_weight
                value_range                             { $$ = $1; /* Same as := 1 */ }
        |       value_range yP_COLONEQ  expr            { $$ = $1; /*UNSUP-no-UVM*/ }
        |       value_range yP_COLONDIV expr            { $$ = $1; /*UNSUP-no-UVM*/ }
        ;

extern_constraint_declaration<nodep>:  // ==IEEE: extern_constraint_declaration
                constraintStaticE yCONSTRAINT packageClassScopeE idAny
                        { $$ = nullptr; BBUNSUP($<fl>2, "Unsupported: extern constraint"); }
        ;

constraintStaticE<cbool>:  // IEEE: part of extern_constraint_declaration
                /* empty */                             { $$ = false; }
        |       ySTATIC__CONSTRAINT                     { $$ = true; }
        ;

//**********************************************************************
// Constants

timeNumAdjusted<nodeExprp>:         // Time constant, adjusted to module's time units/precision
                yaTIMENUM
                        { $$ = new AstTimeImport{$<fl>1, new AstConst{$<fl>1, AstConst::RealDouble{}, $1}}; }
        ;

//**********************************************************************
// Generic tokens

colon<fl>:                      // Generic colon that isn't making a label (e.g. in a case_item)
                ':'                                     { $$ = $1; }
        |       yP_COLON__BEGIN                         { $$ = $1; }
        |       yP_COLON__FORK                          { $$ = $1; }
        ;

//**********************************************************************
// VLT Files

vltItem:

                vltOffFront
                        { V3Config::addIgnore($1, false, "*", 0, 0); }
        |       vltOffFront yVLT_D_FILE yaSTRING
                        { V3Config::addIgnore($1, false, *$3, 0, 0); }
        |       vltOffFront yVLT_D_FILE yaSTRING yVLT_D_LINES yaINTNUM
                        { V3Config::addIgnore($1, false, *$3, $5->toUInt(), $5->toUInt() + 1); }
        |       vltOffFront yVLT_D_FILE yaSTRING yVLT_D_LINES yaINTNUM '-' yaINTNUM
                        { V3Config::addIgnore($1, false, *$3, $5->toUInt(), $7->toUInt() + 1); }
        |       vltOffFront yVLT_D_SCOPE yaSTRING
                        { if ($1 != V3ErrorCode::I_TRACING) {
                              $<fl>1->v3error("Argument -scope only supported for tracing_on/off");
                          } else {
                              V3Config::addScopeTraceOn(false, *$3, 0);
                          }}
        |       vltOffFront yVLT_D_SCOPE yaSTRING yVLT_D_LEVELS yaINTNUM
                        { if ($1 != V3ErrorCode::I_TRACING) {
                              $<fl>1->v3error("Argument -scope only supported for tracing_on/off_off");
                          } else {
                              V3Config::addScopeTraceOn(false, *$3, $5->toUInt());
                          }}
        |       vltOffFront yVLT_D_FILE yaSTRING yVLT_D_MATCH yaSTRING
                        { if (($1 == V3ErrorCode::I_COVERAGE) || ($1 == V3ErrorCode::I_TRACING)) {
                              $<fl>1->v3error("Argument -match only supported for lint_off");
                          } else {
                              V3Config::addIgnoreMatch($1, *$3, *$5);
                          }}
        |       vltOnFront
                        { V3Config::addIgnore($1, true, "*", 0, 0); }
        |       vltOnFront yVLT_D_FILE yaSTRING
                        { V3Config::addIgnore($1, true, *$3, 0, 0); }
        |       vltOnFront yVLT_D_FILE yaSTRING yVLT_D_LINES yaINTNUM
                        { V3Config::addIgnore($1, true, *$3, $5->toUInt(), $5->toUInt() + 1); }
        |       vltOnFront yVLT_D_FILE yaSTRING yVLT_D_LINES yaINTNUM '-' yaINTNUM
                        { V3Config::addIgnore($1, true, *$3, $5->toUInt(), $7->toUInt() + 1); }
        |       vltOnFront yVLT_D_SCOPE yaSTRING
                        { if ($1 != V3ErrorCode::I_TRACING) {
                              $<fl>1->v3error("Argument -scope only supported for tracing_on/off");
                          } else {
                              V3Config::addScopeTraceOn(true, *$3, 0);
                          }}
        |       vltOnFront yVLT_D_SCOPE yaSTRING yVLT_D_LEVELS yaINTNUM
                        { if ($1 != V3ErrorCode::I_TRACING) {
                              $<fl>1->v3error("Argument -scope only supported for tracing_on/off_off");
                          } else {
                              V3Config::addScopeTraceOn(true, *$3, $5->toUInt());
                          }}
        |       vltVarAttrFront vltDModuleE vltDFTaskE vltVarAttrVarE attr_event_controlE
                        { V3Config::addVarAttr($<fl>1, *$2, *$3, *$4, $1, $5); }
        |       vltInlineFront vltDModuleE vltDFTaskE
                        { V3Config::addInline($<fl>1, *$2, *$3, $1); }
        |       yVLT_COVERAGE_BLOCK_OFF yVLT_D_FILE yaSTRING
                        { V3Config::addCoverageBlockOff(*$3, 0); }
        |       yVLT_COVERAGE_BLOCK_OFF yVLT_D_FILE yaSTRING yVLT_D_LINES yaINTNUM
                        { V3Config::addCoverageBlockOff(*$3, $5->toUInt()); }
        |       yVLT_COVERAGE_BLOCK_OFF yVLT_D_MODULE yaSTRING yVLT_D_BLOCK yaSTRING
                        { V3Config::addCoverageBlockOff(*$3, *$5); }
        |       yVLT_FULL_CASE yVLT_D_FILE yaSTRING
                        { V3Config::addCaseFull(*$3, 0); }
        |       yVLT_FULL_CASE yVLT_D_FILE yaSTRING yVLT_D_LINES yaINTNUM
                        { V3Config::addCaseFull(*$3, $5->toUInt()); }
        |       yVLT_HIER_BLOCK vltDModuleE
                        { V3Config::addModulePragma(*$2, VPragmaType::HIER_BLOCK); }
        |       yVLT_PARALLEL_CASE yVLT_D_FILE yaSTRING
                        { V3Config::addCaseParallel(*$3, 0); }
        |       yVLT_PARALLEL_CASE yVLT_D_FILE yaSTRING yVLT_D_LINES yaINTNUM
                        { V3Config::addCaseParallel(*$3, $5->toUInt()); }
        |       yVLT_PROFILE_DATA yVLT_D_MODEL yaSTRING yVLT_D_MTASK yaSTRING yVLT_D_COST yaINTNUM
                        { V3Config::addProfileData($<fl>1, *$3, *$5, $7->toUQuad()); }
        ;

vltOffFront<errcodeen>:
                yVLT_COVERAGE_OFF                       { $$ = V3ErrorCode::I_COVERAGE; }
        |       yVLT_TIMING_OFF                         { $$ = V3ErrorCode::I_TIMING; }
        |       yVLT_TRACING_OFF                        { $$ = V3ErrorCode::I_TRACING; }
        |       yVLT_LINT_OFF                           { $$ = V3ErrorCode::I_LINT; }
        |       yVLT_LINT_OFF yVLT_D_RULE idAny
                        { const char *codemsg = (*$3).c_str();
                          if (V3ErrorCode::unusedMsg(codemsg)) {$$ = V3ErrorCode::I_UNUSED; }
                          else {$$ = V3ErrorCode{codemsg}; }
                          if ($$ == V3ErrorCode::EC_ERROR) { $1->v3error("Unknown error code: '" << *$3 << "'"); } }
        ;

vltOnFront<errcodeen>:
                yVLT_COVERAGE_ON                        { $$ = V3ErrorCode::I_COVERAGE; }
        |       yVLT_TIMING_ON                          { $$ = V3ErrorCode::I_TIMING; }
        |       yVLT_TRACING_ON                         { $$ = V3ErrorCode::I_TRACING; }
        |       yVLT_LINT_ON                            { $$ = V3ErrorCode::I_LINT; }
        |       yVLT_LINT_ON yVLT_D_RULE idAny
                        { const char *codemsg = (*$3).c_str();
                          if (V3ErrorCode::unusedMsg(codemsg)) {$$ = V3ErrorCode::I_UNUSED; }
                          else {$$ = V3ErrorCode{codemsg}; }
                          if ($$ == V3ErrorCode::EC_ERROR) { $1->v3error("Unknown error code: '" << *$3 << "'"); } }
        ;

vltDModuleE<strp>:
                /* empty */                             { static string unit = "__024unit"; $$ = &unit; }
        |       yVLT_D_MODULE str                       { $$ = $2; }
        ;

vltDFTaskE<strp>:
                /* empty */                             { static string empty; $$ = &empty; }
        |       yVLT_D_FUNCTION str                     { $$ = $2; }
        |       yVLT_D_TASK str                         { $$ = $2; }
        ;

vltInlineFront<cbool>:
                yVLT_INLINE                             { $$ = true; }
        |       yVLT_NO_INLINE                          { $$ = false; }
        ;

vltVarAttrVarE<strp>:
                /* empty */                             { static string empty; $$ = &empty; }
        |       yVLT_D_VAR str                          { $$ = $2; }
        ;

vltVarAttrFront<attrtypeen>:
                yVLT_CLOCK_ENABLE           { $$ = VAttrType::VAR_CLOCK_ENABLE; }
        |       yVLT_CLOCKER                { $$ = VAttrType::VAR_CLOCKER; }
        |       yVLT_ISOLATE_ASSIGNMENTS    { $$ = VAttrType::VAR_ISOLATE_ASSIGNMENTS; }
        |       yVLT_NO_CLOCKER             { $$ = VAttrType::VAR_NO_CLOCKER; }
        |       yVLT_FORCEABLE              { $$ = VAttrType::VAR_FORCEABLE; }
        |       yVLT_PUBLIC                 { $$ = VAttrType::VAR_PUBLIC; v3Global.dpi(true); }
        |       yVLT_PUBLIC_FLAT            { $$ = VAttrType::VAR_PUBLIC_FLAT; v3Global.dpi(true); }
        |       yVLT_PUBLIC_FLAT_RD         { $$ = VAttrType::VAR_PUBLIC_FLAT_RD; v3Global.dpi(true); }
        |       yVLT_PUBLIC_FLAT_RW         { $$ = VAttrType::VAR_PUBLIC_FLAT_RW; v3Global.dpi(true); }
        |       yVLT_SC_BV                  { $$ = VAttrType::VAR_SC_BV; }
        |       yVLT_SFORMAT                { $$ = VAttrType::VAR_SFORMAT; }
        |       yVLT_SPLIT_VAR              { $$ = VAttrType::VAR_SPLIT_VAR; }
        ;

//**********************************************************************
%%
// For implementation functions see V3ParseGrammar.cpp

//YACC = /kits/sources/bison-2.4.1/src/bison --report=lookahead
// --report=lookahead
// --report=itemset
// --graph
