// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Language code class
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2015 by Wilson Snyder.  This program is free software; you can
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

#ifndef _V3LANGCODE_H_
#define _V3LANGCODE_H_ 1

#include "config_build.h"
#include "verilatedos.h"
#include <string>
#include <vector>
#include <map>
#include <set>

//######################################################################
//! Class for the different languages supported.
//! A separate file, since used both in V3Options (globally) and FileLine 9per
//! file).
class V3LangCode {
public:
    enum en {
	L_ERROR,  // Must be first.
	L1364_1995,
	L1364_2001,
	L1364_2005,
	L1800_2005,
	L1800_2009,
	L1800_2012,
	// ***Add new elements below also***
	_ENUM_END
    };
    const char* ascii() const {
	const char* names[] = {
	    // These must match the `begin_keywords values.
	    " ERROR",
	    "1364-1995",
	    "1364-2001",
	    "1364-2005",
	    "1800-2005",
	    "1800-2009",
	    "1800-2012"
	};
	return names[m_e];
    };
    static V3LangCode mostRecent() { return V3LangCode(L1800_2012); }
    bool systemVerilog() const { return m_e == L1800_2005 || m_e == L1800_2009 || m_e == L1800_2012; }
    bool legal() const { return m_e != L_ERROR; }
    //
    enum en m_e;
    inline V3LangCode () : m_e(L_ERROR) {}
    inline V3LangCode (en _e) : m_e(_e) {}
    V3LangCode (const char* textp);
    explicit inline V3LangCode (int _e) : m_e(static_cast<en>(_e)) {}
    operator en () const { return m_e; }
};

//######################################################################

#endif // guard
