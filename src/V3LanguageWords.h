// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Language rules
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2005-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef _V3LANGUAGEWORDS_H_
#define _V3LANGUAGEWORDS_H_ 1

#include "config_build.h"
#include "verilatedos.h"

#include <map>

//============================================================================

class V3LanguageWords {
    // List of common reserved keywords
  private:
    typedef std::map<string,string> KeywordMap;
    struct Singleton {
        KeywordMap s_kwdMap;  // List of keywords, and what language applies
        Singleton() { init(); }
        void addKwd(const string& kwd, const string& why) {
            s_kwdMap.insert(make_pair(kwd, why));
        }
        void init();
    };
  public:
    typedef KeywordMap::const_iterator const_iterator;
    // METHODS
    static const_iterator begin() { return s().s_kwdMap.begin(); }
    static const_iterator end() { return s().s_kwdMap.end(); }
    static string isKeyword(const string& kwd) {
        KeywordMap::const_iterator it = s().s_kwdMap.find(kwd);
        if (it == s().s_kwdMap.end()) return "";
        return it->second;
    }
private:
    static Singleton& s() { static Singleton s_s; return s_s; }
};

inline void V3LanguageWords::Singleton::init() {
    // C++ keywords
    addKwd("NULL",                  "C++ common word");
    addKwd("abort",                 "C++ common word");
    addKwd("alignas",               "C++11 keyword");
    addKwd("alignof",               "C++11 keyword");
    addKwd("and",                   "C++11 keyword");
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
    addKwd("break",                 "C++ keyword");
    addKwd("case",                  "C++ keyword");
    addKwd("catch",                 "C++ keyword");
    addKwd("cdecl",                 "C++ common word");
    addKwd("char",                  "C++ keyword");
    addKwd("char16_t",              "C++11 keyword");
    addKwd("char32_t",              "C++11 keyword");
    addKwd("class",                 "C++11 keyword");
    addKwd("compl",                 "C++11 keyword");
    addKwd("complex",               "C++ common word");
    addKwd("concept",               "C++20 keyword");
    addKwd("const",                 "C++ keyword");
    addKwd("const_cast",            "C++ common word");
    addKwd("const_iterator",        "C++ common word");
    addKwd("const_reference ",      "C++ common word");
    addKwd("constexpr",             "C++11 keyword");
    addKwd("continue",              "C++ keyword");
    addKwd("decltype",              "C++11 keyword");
    addKwd("default",               "C++ keyword");
    addKwd("delete",                "C++ keyword");
    addKwd("deque",                 "C++ common word");
    addKwd("do",                    "C++ keyword");
    addKwd("double",                "C++ keyword");
    addKwd("dynamic_cast",          "C++ keyword");
    addKwd("else",                  "C++ keyword");
    addKwd("enum",                  "C++ keyword");
    addKwd("explicit",              "C++ keyword");
    addKwd("export",                "C++ keyword");
    addKwd("extern",                "C++ keyword");
    addKwd("false",                 "C++ keyword");
    addKwd("far",                   "C++ common word");
    addKwd("float",                 "C++ keyword");
    addKwd("for",                   "C++ keyword");
    addKwd("friend",                "C++ keyword");
    addKwd("goto",                  "C++ keyword");
    addKwd("huge",                  "C++ keyword");
    addKwd("if",                    "C++ keyword");
    addKwd("import",                "C++ modules TS keyword");
    addKwd("inline",                "C++ keyword");
    addKwd("int",                   "C++ keyword");
    addKwd("interrupt",             "C++ common word");
    addKwd("iterator",              "C++ common word");
    addKwd("list",                  "C++ common word");
    addKwd("long",                  "C++ keyword");
    addKwd("map",                   "C++ common word");
    addKwd("module",                "C++ modules TS keyword");
    addKwd("std::multimap",         "C++ common word");
    addKwd("std::multiset",         "C++ common word");
    addKwd("mutable",               "C++ keyword");
    addKwd("namespace",             "C++ keyword");
    addKwd("near",                  "C++ common word");
    addKwd("new",                   "C++ keyword");
    addKwd("noexcept",              "C++11 keyword");
    addKwd("not",                   "C++ keyword");
    addKwd("not_eq",                "C++ keyword");
    addKwd("nullptr",               "C++11 keyword");
    addKwd("operator",              "C++ keyword");
    addKwd("or",                    "C++ keyword");
    addKwd("or_eq",                 "C++ keyword");
    addKwd("override",              "C++ common word");
    addKwd("pascal",                "C++ keyword");
    addKwd("private",               "C++ keyword");
    addKwd("protected",             "C++ keyword");
    addKwd("public",                "C++ keyword");
    addKwd("queue",                 "C++ common word");
    addKwd("reference",             "C++ common word");
    addKwd("register",              "C++ keyword");
    addKwd("reinterpret_cast ",     "C++ keyword");
    addKwd("requires",              "C++20 keyword");
    addKwd("restrict",              "C++ keyword");
    addKwd("return",                "C++ keyword");
    addKwd("set",                   "C++ common word");
    addKwd("short",                 "C++ keyword");
    addKwd("signed",                "C++ keyword");
    addKwd("sizeof",                "C++ keyword");
    addKwd("stack",                 "C++ common word");
    addKwd("static",                "C++ keyword");
    addKwd("static_assert",         "C++11 keyword");
    addKwd("static_cast",           "C++ keyword");
    addKwd("struct",                "C++ keyword");
    addKwd("switch",                "C++ keyword");
    addKwd("synchronized",          "C++ TM TS keyword");
    addKwd("template",              "C++ keyword");
    addKwd("this",                  "C++ keyword");
    addKwd("thread_local",          "C++11 keyword");
    addKwd("throw",                 "C++ keyword");
    addKwd("transaction_safe",      "C++ common word");
    addKwd("transaction_safe_dynamic",      "C++ common word");
    addKwd("true",                  "C++ keyword");
    addKwd("try",                   "C++ keyword");
    addKwd("type_info",             "C++ common word");
    addKwd("typedef",               "C++ keyword");
    addKwd("typeid",                "C++ keyword");
    addKwd("typename",              "C++ keyword");
    addKwd("uint16_t",              "C++ common word");
    addKwd("uint32_t",              "C++ common word");
    addKwd("uint8_t",               "C++ common word");
    addKwd("union",                 "C++ keyword");
    addKwd("unsigned",              "C++ keyword");
    addKwd("using",                 "C++ keyword");
    addKwd("vector",                "C++ common word");
    addKwd("virtual",               "C++ keyword");
    addKwd("void",                  "C++ keyword");
    addKwd("volatile",              "C++ keyword");
    addKwd("wchar_t",               "C++ keyword");
    addKwd("while",                 "C++ keyword");
    addKwd("xor",                   "C++ keyword");
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
    addKwd("`systemc_imp_header",       "Verilator preprocessor directive");
    addKwd("`systemc_implementation",   "Verilator preprocessor directive");
    addKwd("`systemc_interface",        "Verilator preprocessor directive");
    addKwd("`timescale",                "Verilog preprocessor directive");
    addKwd("`undef",                    "Verilog preprocessor directive");
    addKwd("`undefineall",              "Verilog preprocessor directive");
    addKwd("`verilator_config",         "Verilator preprocessor directive");
    addKwd("`verilog",                  "Verilator preprocessor directive");
}

#endif  // Guard
