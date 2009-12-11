// -*- C++ -*-
//*************************************************************************
//
// Copyright 2009-2009 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License.
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//=========================================================================
///
/// \file
/// \brief Verilator: Implementation Header, only for verilated.cpp internals.
///
/// Code available from: http://www.veripool.org/verilator
///
//=========================================================================


#ifndef _VERILATEDIMP_H_
#define _VERILATEDIMP_H_ 1 ///< Header Guard

#if !defined(_VERILATED_CPP_) && !defined(_VERILATEDDPI_CPP_)
# error "verilatedimp.h only to be included by verilated*.cpp internals"
#endif

#include "verilatedos.h"
#include "verilated.h"

#include <map>
#include <vector>

class VerilatedScope;

//======================================================================
// Types

struct VerilatedCStrCmp {
    // For ordering maps keyed by const char*'s
    bool operator() (const char *a, const char *b) const {
	return std::strcmp(a, b) < 0;
    }
};

class VerilatedImp {
    // Whole class is internal use only - Global information shared between verilated*.cpp files.

    // TYPES
    typedef vector<string> ArgVec;
    typedef map<pair<const void*,void*>,void*> UserMap;
    typedef map<const char*, const VerilatedScope*, VerilatedCStrCmp>  ScopeNameMap;

    // MEMBERS
    static VerilatedImp	s_s;		///< Static Singleton; One and only static this

    ArgVec		m_argVec;	// Argument list
    bool		m_argVecLoaded;	// Ever loaded argument list
    UserMap	 	m_userMap;	///< Map of <(scope,userkey), userData>
    ScopeNameMap	m_nameMap;	///< Map of <scope name, scope pointer>

public: // But only for verilated*.cpp
    // CONSTRUCTORS
    VerilatedImp() : m_argVecLoaded(false) {}
    ~VerilatedImp() {}

    // METHODS - arguments
    static void commandArgs(int argc, const char** argv) {
	s_s.m_argVec.clear();
	for (int i=0; i<argc; i++) s_s.m_argVec.push_back(argv[i]);
	s_s.m_argVecLoaded = true; // Can't just test later for empty vector, no arguments is ok
    }
    static string argPlusMatch(const char* prefixp) {
	int len = strlen(prefixp);
	if (VL_UNLIKELY(!s_s.m_argVecLoaded)) {
	    s_s.m_argVecLoaded = true;  // Complain only once
	    vl_fatal("unknown",0,"",
		     "%Error: Verilog called $test$plusargs or $value$plusargs without"
		     " testbench C first calling Verilated::commandArgs(argc,argv).");
	}
	for (ArgVec::iterator it=s_s.m_argVec.begin(); it!=s_s.m_argVec.end(); ++it) {
	    if ((*it)[0]=='+') {
		if (0==strncmp(prefixp, it->c_str()+1, len)) return *it;
	    }
	}
	return "";
    }

    // METHODS - user scope tracking
    // We implement this as a single large map instead of one map per scope
    // There's often many more scopes than userdata's and thus having a ~48byte
    // per map overhead * N scopes would take much more space and cache thrashing.
    static inline void userInsert(const void* scopep, void* userKey, void* userData) {
	UserMap::iterator it=s_s.m_userMap.find(make_pair(scopep,userKey));
	if (it != s_s.m_userMap.end()) it->second = userData;
	// When we support VL_THREADs, we need a lock around this insert, as it's runtime
	else s_s.m_userMap.insert(it, make_pair(make_pair(scopep,userKey),userData));
    }
    static inline void* userFind(const void* scopep, void* userKey) {
	UserMap::iterator it=s_s.m_userMap.find(make_pair(scopep,userKey));
	if (VL_LIKELY(it != s_s.m_userMap.end())) return it->second;
	else return NULL;
    }
private:
    /// Symbol table destruction cleans up the entries for each scope.
    static void userEraseScope(const VerilatedScope* scopep) {
	// Slow ok - called once/scope on destruction, so we simply iterate.
	for (UserMap::iterator it=s_s.m_userMap.begin(); it!=s_s.m_userMap.end(); ) {
	    if (it->first.first == scopep) {
		s_s.m_userMap.erase(it++);
	    } else {
		++it;
	    }
	}
    }

public: // But only for verilated*.cpp
    // METHODS - scope name
    static void scopeInsert(const VerilatedScope* scopep) {
	// Slow ok - called once/scope at construction
	ScopeNameMap::iterator it=s_s.m_nameMap.find(scopep->name());
	if (it == s_s.m_nameMap.end()) {
	    s_s.m_nameMap.insert(it, make_pair(scopep->name(),scopep));
	}
    }
    static inline const VerilatedScope* scopeFind(const char* namep) {
	ScopeNameMap::iterator it=s_s.m_nameMap.find(namep);
	if (it != s_s.m_nameMap.end()) return it->second;
	else return NULL;
    }
    static void scopeErase(const VerilatedScope* scopep) {
	// Slow ok - called once/scope at destruction
	userEraseScope(scopep);
	ScopeNameMap::iterator it=s_s.m_nameMap.find(scopep->name());
	if (it != s_s.m_nameMap.end()) s_s.m_nameMap.erase(it);
    }
    static void scopesDump() {
	VL_PRINTF("scopesDump:\n");
	for (ScopeNameMap::iterator it=s_s.m_nameMap.begin();
	     it!=s_s.m_nameMap.end(); ++it) {
	    const VerilatedScope* scopep = it->second;
	    VL_PRINTF("    %s\n", scopep->name());
	}
	VL_PRINTF("\n");
    }
};

#endif  // Guard
