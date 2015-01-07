// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Options parsing
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

#include "config_build.h"
#include "verilatedos.h"

#include "V3String.h"

//######################################################################
// Wildcard

// Double procedures, inlined, unrolls loop much better
inline bool VString::wildmatchi(const char* s, const char* p) {
    for ( ; *p; s++, p++) {
	if (*p!='*') {
	    if (((*s)!=(*p)) && *p != '?')
		return false;
	}
	else {
	    // Trailing star matches everything.
	    if (!*++p) return true;
	    while (wildmatch(s, p) == false)
		if (*++s == '\0')
		    return false;
	    return true;
	}
    }
    return (*s == '\0');
}

bool VString::wildmatch(const char* s, const char* p) {
    for ( ; *p; s++, p++) {
	if (*p!='*') {
	    if (((*s)!=(*p)) && *p != '?')
		return false;
	}
	else {
	    // Trailing star matches everything.
	    if (!*++p) return true;
	    while (wildmatchi(s, p) == false)
		if (*++s == '\0')
		    return false;
	    return true;
	}
    }
    return (*s == '\0');
}

string VString::downcase(const string& str) {
    string out = str;
    for (string::iterator pos = out.begin(); pos != out.end(); ++pos) {
	*pos = tolower(*pos);
    }
    return out;
}
