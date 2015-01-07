// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Language rules
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2005-2015 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
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
    map<string,string>	m_kwdMap;	// List of keywords, and what language applies

    void addKwd(const string& kwd, const string& why) {
	m_kwdMap.insert(make_pair(kwd,why));
    }
  public:
    string isKeyword(const string& kwd) {
	map<string,string>::iterator it = m_kwdMap.find(kwd);
	if (it == m_kwdMap.end()) return "";
	return it->second;
    }

  public:
    V3LanguageWords() {
	// C++ keywords
	addKwd("asm",			"C++ reserved word");
	addKwd("auto",			"C++ reserved word");
	addKwd("catch",			"C++ reserved word");
	addKwd("cdecl",			"C++ reserved word");
	addKwd("char",			"C++ reserved word");
	addKwd("const_cast",		"C++ reserved word");
	addKwd("delete",		"C++ reserved word");
	addKwd("double",		"C++ reserved word");
	addKwd("dynamic_cast",		"C++ reserved word");
	addKwd("explicit",		"C++ reserved word");
	addKwd("far",			"C++ reserved word");
	addKwd("float",			"C++ reserved word");
	addKwd("friend",		"C++ reserved word");
	addKwd("goto",			"C++ reserved word");
	addKwd("huge",			"C++ reserved word");
	addKwd("inline",		"C++ reserved word");
	addKwd("interrupt",		"C++ reserved word");
	addKwd("long",			"C++ reserved word");
	addKwd("mutable",		"C++ reserved word");
	addKwd("near",			"C++ reserved word");
	addKwd("operator",		"C++ reserved word");
	addKwd("pascal",		"C++ reserved word");
	addKwd("private",		"C++ reserved word");
	addKwd("public",		"C++ reserved word");
	addKwd("register",		"C++ reserved word");
	addKwd("reinterpret_cast ",	"C++ reserved word");
	addKwd("restrict",		"C++ reserved word");
	addKwd("short",			"C++ reserved word");
	addKwd("sizeof",		"C++ reserved word");
	addKwd("static_cast",		"C++ reserved word");
	addKwd("switch",		"C++ reserved word");
	addKwd("template",		"C++ reserved word");
	addKwd("throw",			"C++ reserved word");
	addKwd("try",			"C++ reserved word");
	addKwd("typeid",		"C++ reserved word");
	addKwd("typename",		"C++ reserved word");
	addKwd("unsigned",		"C++ reserved word");
	addKwd("using",			"C++ reserved word");
	addKwd("volatile",		"C++ reserved word");
	// C++
	addKwd("NULL",			"C++ common word");
	addKwd("abort",			"C++ common word");
	addKwd("bit_vector",		"C++ common word");
	addKwd("bool",			"C++ common word");
	addKwd("complex",		"C++ common word");
	addKwd("const_iterator",	"C++ common word");
	addKwd("const_reference ",	"C++ common word");
	addKwd("deque",			"C++ common word");
	addKwd("false",			"C++ common word");
	addKwd("iterator",		"C++ common word");
	addKwd("list",			"C++ common word");
	addKwd("map",			"C++ common word");
	addKwd("multimap",		"C++ common word");
	addKwd("multiset",		"C++ common word");
	addKwd("queue",			"C++ common word");
	addKwd("reference",		"C++ common word");
	addKwd("set",			"C++ common word");
	addKwd("stack",			"C++ common word");
	addKwd("true",			"C++ common word");
	addKwd("type_info",		"C++ common word");
	addKwd("uint16_t",		"C++ common word");
	addKwd("uint32_t",		"C++ common word");
	addKwd("uint8_t",		"C++ common word");
	addKwd("vector",		"C++ common word");
	// SystemC
	addKwd("sc_clock",		"SystemC common word");
	addKwd("sc_in",			"SystemC common word");
	addKwd("sc_inout",		"SystemC common word");
	addKwd("sc_out",		"SystemC common word");
	addKwd("sc_signal",		"SystemC common word");
	addKwd("sensitive",		"SystemC common word");
	addKwd("sensitive_neg",		"SystemC common word");
	addKwd("sensitive_pos",		"SystemC common word");
    }
};

#endif // Guard


