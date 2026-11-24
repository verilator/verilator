// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Language rules
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2005-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3LANGUAGEWORDS_H_
#define VERILATOR_V3LANGUAGEWORDS_H_

#include "config_build.h"
#include "verilatedos.h"

#include <map>

//============================================================================

class V3LanguageWords final {
    // List of common reserved keywords
private:
    struct Word final {
        std::string why;  // Why it is reserved in C++ or the preprocessor, empty if not
        bool verilog;  // Is a SystemVerilog keyword, IEEE 1800-2023 Table B.1
    };
    using KeywordMap = std::map<const string, Word>;
    struct Singleton final {
        KeywordMap s_kwdMap;  // List of keywords, and what language applies
        Singleton() { init(); }
        void addKwd(const string& kwd, const string& why, bool verilog = false) {
            s_kwdMap.emplace(kwd, Word{why, verilog});
        }
        void init();
    };

public:
    using const_iterator = KeywordMap::const_iterator;
    // METHODS
    static const_iterator begin() { return s().s_kwdMap.begin(); }
    static const_iterator end() { return s().s_kwdMap.end(); }
    static string isKeyword(const string& kwd) {
        const auto it = vlstd::as_const(s().s_kwdMap).find(kwd);
        if (it == s().s_kwdMap.end()) return "";
        return it->second.why;
    }
    static bool isVerilogKeyword(const string& kwd) {
        const auto it = vlstd::as_const(s().s_kwdMap).find(kwd);
        return it != s().s_kwdMap.end() && it->second.verilog;
    }

private:
    static Singleton& s() {
        static Singleton s_s;  // LCOV_EXCL_BR_LINE
        return s_s;
    }
};

inline void V3LanguageWords::Singleton::init() {
    constexpr bool SV = true;  // Also a SystemVerilog keyword
    // C++ keywords
    // clang-format off
    addKwd("abort",                 "C++ common word");
    addKwd("alignas",               "C++11 keyword");
    addKwd("alignof",               "C++11 keyword");
    addKwd("and",                   "C++11 keyword", SV);
    addKwd("and_eq",                "C++11 keyword");
    addKwd("asm",                   "C++ common word");
    addKwd("atomic_cancel",         "C++ TM TS keyword");
    addKwd("atomic_commit",         "C++ TM TS keyword");
    addKwd("atomic_noexcept",       "C++ TM TS keyword");
    addKwd("auto",                  "C++ keyword");
    addKwd("bit_vector",            "C++ common word");
    addKwd("bitand",                "C++ keyword");
    addKwd("bitor",                 "C++ keyword");
    addKwd("bool",                  "C++ keyword");
    addKwd("break",                 "C++ keyword", SV);
    addKwd("case",                  "C++ keyword", SV);
    addKwd("catch",                 "C++ keyword");
    addKwd("cdecl",                 "C++ common word");
    addKwd("char",                  "C++ keyword");
    addKwd("char16_t",              "C++11 keyword");
    addKwd("char32_t",              "C++11 keyword");
    addKwd("class",                 "C++11 keyword", SV);
    addKwd("compl",                 "C++11 keyword");
    addKwd("complex",               "C++ common word");
    addKwd("concept",               "C++20 keyword");
    addKwd("const",                 "C++ keyword", SV);
    addKwd("const_cast",            "C++ common word");
    addKwd("const_iterator",        "C++ common word");
    addKwd("const_reference ",      "C++ common word");
    addKwd("constexpr",             "C++11 keyword");
    addKwd("continue",              "C++ keyword", SV);
    addKwd("decltype",              "C++11 keyword");
    addKwd("default",               "C++ keyword", SV);
    addKwd("delete",                "C++ keyword");
    addKwd("do",                    "C++ keyword", SV);
    addKwd("double",                "C++ keyword");
    addKwd("dynamic_cast",          "C++ keyword");
    addKwd("else",                  "C++ keyword", SV);
    addKwd("enum",                  "C++ keyword", SV);
    addKwd("explicit",              "C++ keyword");
    addKwd("export",                "C++ keyword", SV);
    addKwd("extern",                "C++ keyword", SV);
    addKwd("false",                 "C++ keyword");
    addKwd("far",                   "C++ common word");
    addKwd("float",                 "C++ keyword");
    addKwd("for",                   "C++ keyword", SV);
    addKwd("friend",                "C++ keyword");
    addKwd("goto",                  "C++ keyword");
    addKwd("huge",                  "C++ keyword");
    addKwd("if",                    "C++ keyword", SV);
    addKwd("import",                "C++ modules TS keyword", SV);
    addKwd("inline",                "C++ keyword");
    addKwd("int",                   "C++ keyword", SV);
    addKwd("interrupt",             "C++ common word");
    addKwd("iterator",              "C++ common word");
    addKwd("long",                  "C++ keyword");
    addKwd("module",                "C++ modules TS keyword", SV);
    addKwd("mutable",               "C++ keyword");
    addKwd("namespace",             "C++ keyword");
    addKwd("near",                  "C++ common word");
    addKwd("new",                   "C++ keyword", SV);
    addKwd("noexcept",              "C++11 keyword");
    addKwd("not",                   "C++ keyword", SV);
    addKwd("not_eq",                "C++ keyword");
    addKwd("nullptr",               "C++ common word");
    addKwd("nullptr",               "C++11 keyword");
    addKwd("operator",              "C++ keyword");
    addKwd("or",                    "C++ keyword", SV);
    addKwd("or_eq",                 "C++ keyword");
    addKwd("override",              "C++ common word");
    addKwd("pascal",                "C++ keyword");
    addKwd("private",               "C++ keyword");
    addKwd("protected",             "C++ keyword", SV);
    addKwd("public",                "C++ keyword");
    addKwd("queue",                 "C++ common word");
    addKwd("reference",             "C++ common word");
    addKwd("register",              "C++ keyword");
    addKwd("reinterpret_cast ",     "C++ keyword");
    addKwd("requires",              "C++20 keyword");
    addKwd("restrict",              "C++ keyword", SV);
    addKwd("return",                "C++ keyword", SV);
    addKwd("short",                 "C++ keyword");
    addKwd("signed",                "C++ keyword", SV);
    addKwd("sizeof",                "C++ keyword");
    addKwd("stack",                 "C++ common word");
    addKwd("static",                "C++ keyword", SV);
    addKwd("static_assert",         "C++11 keyword");
    addKwd("static_cast",           "C++ keyword");
    addKwd("std::deque",            "C++ common word");
    addKwd("std::list",             "C++ common word");
    addKwd("std::map",              "C++ common word");
    addKwd("std::multimap",         "C++ common word");
    addKwd("std::multiset",         "C++ common word");
    addKwd("std::set",              "C++ common word");
    addKwd("std::vector",           "C++ common word");
    addKwd("struct",                "C++ keyword", SV);
    addKwd("switch",                "C++ keyword");
    addKwd("synchronized",          "C++ TM TS keyword");
    addKwd("template",              "C++ keyword");
    addKwd("this",                  "C++ keyword", SV);
    addKwd("thread_local",          "C++11 keyword");
    addKwd("throw",                 "C++ keyword");
    addKwd("transaction_safe",      "C++ common word");
    addKwd("transaction_safe_dynamic",      "C++ common word");
    addKwd("true",                  "C++ keyword");
    addKwd("try",                   "C++ keyword");
    addKwd("type_info",             "C++ common word");
    addKwd("typedef",               "C++ keyword", SV);
    addKwd("typeid",                "C++ keyword");
    addKwd("typename",              "C++ keyword");
    addKwd("uint16_t",              "C++ common word");
    addKwd("uint32_t",              "C++ common word");
    addKwd("uint8_t",               "C++ common word");
    addKwd("union",                 "C++ keyword", SV);
    addKwd("unsigned",              "C++ keyword", SV);
    addKwd("using",                 "C++ keyword");
    addKwd("virtual",               "C++ keyword", SV);
    addKwd("void",                  "C++ keyword", SV);
    addKwd("volatile",              "C++ keyword");
    addKwd("wchar_t",               "C++ keyword");
    addKwd("while",                 "C++ keyword", SV);
    addKwd("xor",                   "C++ keyword", SV);
    addKwd("xor_eq",                "C++ keyword");
    // This conflicts with header functions, so is ignored
    //dKwd("final",                 "C++11 keyword");
    // SystemC
    addKwd("sc_clock",              "SystemC common word");
    addKwd("sc_in",                 "SystemC common word");
    addKwd("sc_inout",              "SystemC common word");
    addKwd("sc_out",                "SystemC common word");
    addKwd("sc_signal",             "SystemC common word");
    addKwd("sensitive",             "SystemC common word");
    addKwd("sensitive_neg",         "SystemC common word");
    addKwd("sensitive_pos",         "SystemC common word");
    // Preprocessor defined words
    addKwd("`__FILE__",                 "Verilog preprocessor directive");
    addKwd("`__LINE__",                 "Verilog preprocessor directive");
    addKwd("`accelerate",               "Verilog-XL preprocessor directive");
    addKwd("`autoexpand_vectornets",    "Verilog-XL preprocessor directive");
    addKwd("`begin_keywords",           "Verilog preprocessor directive");
    addKwd("`celldefine",               "Verilog preprocessor directive");
    addKwd("`default_decay_time",       "Verilog preprocessor directive");
    addKwd("`default_nettype",          "Verilog preprocessor directive");
    addKwd("`default_trireg_strength",  "Verilog preprocessor directive");
    addKwd("`define",                   "Verilog preprocessor directive");
    addKwd("`delay_mode_distributed",   "Verilog preprocessor directive");
    addKwd("`delay_mode_path",          "Verilog preprocessor directive");
    addKwd("`delay_mode_unit",          "Verilog preprocessor directive");
    addKwd("`delay_mode_zero",          "Verilog preprocessor directive");
    addKwd("`disable_portfaults",       "Verilog-XL preprocessor directive");
    addKwd("`else",                     "Verilog preprocessor directive");
    addKwd("`elsif",                    "Verilog preprocessor directive");
    addKwd("`enable_portfaults",        "Verilog-XL preprocessor directive");
    addKwd("`end_keywords",             "Verilog preprocessor directive");
    addKwd("`endcelldefine",            "Verilog preprocessor directive");
    addKwd("`endif",                    "Verilog preprocessor directive");
    addKwd("`endprotect",               "Verilog preprocessor directive");
    addKwd("`endprotected",             "Verilog preprocessor directive");
    addKwd("`error",                    "Verilog preprocessor directive");
    addKwd("`expand_vectornets",        "Verilog-XL preprocessor directive");
    addKwd("`ifdef",                    "Verilog preprocessor directive");
    addKwd("`ifndef",                   "Verilog preprocessor directive");
    addKwd("`include",                  "Verilog preprocessor directive");
    addKwd("`inline",                   "Verilog preprocessor directive");
    addKwd("`line",                     "Verilog preprocessor directive");
    addKwd("`noaccelerate",             "Verilog-XL preprocessor directive");
    addKwd("`noexpand_vectornets",      "Verilog-XL preprocessor directive");
    addKwd("`noremove_gatenames",       "Verilog-XL preprocessor directive");
    addKwd("`noremove_netnames",        "Verilog-XL preprocessor directive");
    addKwd("`nosuppress_faults",        "Verilog-XL preprocessor directive");
    addKwd("`nounconnected_drive",      "Verilog-XL preprocessor directive");
    addKwd("`portcoerce",               "Verilog preprocessor directive");
    addKwd("`pragma",                   "Verilog preprocessor directive");
    addKwd("`protect",                  "Verilog preprocessor directive");
    addKwd("`protected",                "Verilog preprocessor directive");
    addKwd("`remove_gatenames",         "Verilog-XL preprocessor directive");
    addKwd("`remove_netnames",          "Verilog-XL preprocessor directive");
    addKwd("`resetall",                 "Verilog preprocessor directive");
    addKwd("`suppress_faults",          "Verilog-XL preprocessor directive");
    addKwd("`systemc_ctor",             "Verilator preprocessor directive");
    addKwd("`systemc_dtor",             "Verilator preprocessor directive");
    addKwd("`systemc_header",           "Verilator preprocessor directive");
    addKwd("`systemc_header_post",      "Verilator preprocessor directive");
    addKwd("`systemc_imp_header",       "Verilator preprocessor directive");
    addKwd("`systemc_implementation",   "Verilator preprocessor directive");
    addKwd("`systemc_interface",        "Verilator preprocessor directive");
    addKwd("`timescale",                "Verilog preprocessor directive");
    addKwd("`undef",                    "Verilog preprocessor directive");
    addKwd("`undefineall",              "Verilog preprocessor directive");
    addKwd("`verilator_config",         "Verilator preprocessor directive");
    addKwd("`verilog",                  "Verilator preprocessor directive");
    // SystemVerilog keywords that are not also C++ words above
    addKwd("accept_on",             "", SV);
    addKwd("alias",                 "", SV);
    addKwd("always",                "", SV);
    addKwd("always_comb",           "", SV);
    addKwd("always_ff",             "", SV);
    addKwd("always_latch",          "", SV);
    addKwd("assert",                "", SV);
    addKwd("assign",                "", SV);
    addKwd("assume",                "", SV);
    addKwd("automatic",             "", SV);
    addKwd("before",                "", SV);
    addKwd("begin",                 "", SV);
    addKwd("bind",                  "", SV);
    addKwd("bins",                  "", SV);
    addKwd("binsof",                "", SV);
    addKwd("bit",                   "", SV);
    addKwd("buf",                   "", SV);
    addKwd("bufif0",                "", SV);
    addKwd("bufif1",                "", SV);
    addKwd("byte",                  "", SV);
    addKwd("casex",                 "", SV);
    addKwd("casez",                 "", SV);
    addKwd("cell",                  "", SV);
    addKwd("chandle",               "", SV);
    addKwd("checker",               "", SV);
    addKwd("clocking",              "", SV);
    addKwd("cmos",                  "", SV);
    addKwd("config",                "", SV);
    addKwd("constraint",            "", SV);
    addKwd("context",               "", SV);
    addKwd("cover",                 "", SV);
    addKwd("covergroup",            "", SV);
    addKwd("coverpoint",            "", SV);
    addKwd("cross",                 "", SV);
    addKwd("deassign",              "", SV);
    addKwd("defparam",              "", SV);
    addKwd("design",                "", SV);
    addKwd("disable",               "", SV);
    addKwd("dist",                  "", SV);
    addKwd("edge",                  "", SV);
    addKwd("end",                   "", SV);
    addKwd("endcase",               "", SV);
    addKwd("endchecker",            "", SV);
    addKwd("endclass",              "", SV);
    addKwd("endclocking",           "", SV);
    addKwd("endconfig",             "", SV);
    addKwd("endfunction",           "", SV);
    addKwd("endgenerate",           "", SV);
    addKwd("endgroup",              "", SV);
    addKwd("endinterface",          "", SV);
    addKwd("endmodule",             "", SV);
    addKwd("endpackage",            "", SV);
    addKwd("endprimitive",          "", SV);
    addKwd("endprogram",            "", SV);
    addKwd("endproperty",           "", SV);
    addKwd("endsequence",           "", SV);
    addKwd("endspecify",            "", SV);
    addKwd("endtable",              "", SV);
    addKwd("endtask",               "", SV);
    addKwd("event",                 "", SV);
    addKwd("eventually",            "", SV);
    addKwd("expect",                "", SV);
    addKwd("extends",               "", SV);
    addKwd("final",                 "", SV);
    addKwd("first_match",           "", SV);
    addKwd("force",                 "", SV);
    addKwd("foreach",               "", SV);
    addKwd("forever",               "", SV);
    addKwd("fork",                  "", SV);
    addKwd("forkjoin",              "", SV);
    addKwd("function",              "", SV);
    addKwd("generate",              "", SV);
    addKwd("genvar",                "", SV);
    addKwd("global",                "", SV);
    addKwd("highz0",                "", SV);
    addKwd("highz1",                "", SV);
    addKwd("iff",                   "", SV);
    addKwd("ifnone",                "", SV);
    addKwd("ignore_bins",           "", SV);
    addKwd("illegal_bins",          "", SV);
    addKwd("implements",            "", SV);
    addKwd("implies",               "", SV);
    addKwd("incdir",                "", SV);
    addKwd("include",               "", SV);
    addKwd("initial",               "", SV);
    addKwd("inout",                 "", SV);
    addKwd("input",                 "", SV);
    addKwd("inside",                "", SV);
    addKwd("instance",              "", SV);
    addKwd("integer",               "", SV);
    addKwd("interconnect",          "", SV);
    addKwd("interface",             "", SV);
    addKwd("intersect",             "", SV);
    addKwd("join",                  "", SV);
    addKwd("join_any",              "", SV);
    addKwd("join_none",             "", SV);
    addKwd("large",                 "", SV);
    addKwd("let",                   "", SV);
    addKwd("liblist",               "", SV);
    addKwd("library",               "", SV);
    addKwd("local",                 "", SV);
    addKwd("localparam",            "", SV);
    addKwd("logic",                 "", SV);
    addKwd("longint",               "", SV);
    addKwd("macromodule",           "", SV);
    addKwd("matches",               "", SV);
    addKwd("medium",                "", SV);
    addKwd("modport",               "", SV);
    addKwd("nand",                  "", SV);
    addKwd("negedge",               "", SV);
    addKwd("nettype",               "", SV);
    addKwd("nexttime",              "", SV);
    addKwd("nmos",                  "", SV);
    addKwd("nor",                   "", SV);
    addKwd("noshowcancelled",       "", SV);
    addKwd("notif0",                "", SV);
    addKwd("notif1",                "", SV);
    addKwd("null",                  "", SV);
    addKwd("output",                "", SV);
    addKwd("package",               "", SV);
    addKwd("packed",                "", SV);
    addKwd("parameter",             "", SV);
    addKwd("pmos",                  "", SV);
    addKwd("posedge",               "", SV);
    addKwd("primitive",             "", SV);
    addKwd("priority",              "", SV);
    addKwd("program",               "", SV);
    addKwd("property",              "", SV);
    addKwd("pull0",                 "", SV);
    addKwd("pull1",                 "", SV);
    addKwd("pulldown",              "", SV);
    addKwd("pullup",                "", SV);
    addKwd("pulsestyle_ondetect",   "", SV);
    addKwd("pulsestyle_onevent",    "", SV);
    addKwd("pure",                  "", SV);
    addKwd("rand",                  "", SV);
    addKwd("randc",                 "", SV);
    addKwd("randcase",              "", SV);
    addKwd("randsequence",          "", SV);
    addKwd("rcmos",                 "", SV);
    addKwd("real",                  "", SV);
    addKwd("realtime",              "", SV);
    addKwd("ref",                   "", SV);
    addKwd("reg",                   "", SV);
    addKwd("reject_on",             "", SV);
    addKwd("release",               "", SV);
    addKwd("repeat",                "", SV);
    addKwd("rnmos",                 "", SV);
    addKwd("rpmos",                 "", SV);
    addKwd("rtran",                 "", SV);
    addKwd("rtranif0",              "", SV);
    addKwd("rtranif1",              "", SV);
    addKwd("s_always",              "", SV);
    addKwd("s_eventually",          "", SV);
    addKwd("s_nexttime",            "", SV);
    addKwd("s_until",               "", SV);
    addKwd("s_until_with",          "", SV);
    addKwd("scalared",              "", SV);
    addKwd("sequence",              "", SV);
    addKwd("shortint",              "", SV);
    addKwd("shortreal",             "", SV);
    addKwd("showcancelled",         "", SV);
    addKwd("small",                 "", SV);
    addKwd("soft",                  "", SV);
    addKwd("solve",                 "", SV);
    addKwd("specify",               "", SV);
    addKwd("specparam",             "", SV);
    addKwd("string",                "", SV);
    addKwd("strong",                "", SV);
    addKwd("strong0",               "", SV);
    addKwd("strong1",               "", SV);
    addKwd("super",                 "", SV);
    addKwd("supply0",               "", SV);
    addKwd("supply1",               "", SV);
    addKwd("sync_accept_on",        "", SV);
    addKwd("sync_reject_on",        "", SV);
    addKwd("table",                 "", SV);
    addKwd("tagged",                "", SV);
    addKwd("task",                  "", SV);
    addKwd("throughout",            "", SV);
    addKwd("time",                  "", SV);
    addKwd("timeprecision",         "", SV);
    addKwd("timeunit",              "", SV);
    addKwd("tran",                  "", SV);
    addKwd("tranif0",               "", SV);
    addKwd("tranif1",               "", SV);
    addKwd("tri",                   "", SV);
    addKwd("tri0",                  "", SV);
    addKwd("tri1",                  "", SV);
    addKwd("triand",                "", SV);
    addKwd("trior",                 "", SV);
    addKwd("trireg",                "", SV);
    addKwd("type",                  "", SV);
    addKwd("unique",                "", SV);
    addKwd("unique0",               "", SV);
    addKwd("until",                 "", SV);
    addKwd("until_with",            "", SV);
    addKwd("untyped",               "", SV);
    addKwd("use",                   "", SV);
    addKwd("uwire",                 "", SV);
    addKwd("var",                   "", SV);
    addKwd("vectored",              "", SV);
    addKwd("wait",                  "", SV);
    addKwd("wait_order",            "", SV);
    addKwd("wand",                  "", SV);
    addKwd("weak",                  "", SV);
    addKwd("weak0",                 "", SV);
    addKwd("weak1",                 "", SV);
    addKwd("wildcard",              "", SV);
    addKwd("wire",                  "", SV);
    addKwd("with",                  "", SV);
    addKwd("within",                "", SV);
    addKwd("wor",                   "", SV);
    addKwd("xnor",                  "", SV);
    // clang-format on
}

#endif  // Guard
