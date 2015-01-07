// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2009-2015 by Wilson Snyder. This program is free software; you can
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


#ifndef _VERILATED_IMP_H_
#define _VERILATED_IMP_H_ 1 ///< Header Guard

#if !defined(_VERILATED_CPP_) && !defined(_VERILATED_DPI_CPP_)
# error "verilated_imp.h only to be included by verilated*.cpp internals"
#endif

#include "verilatedos.h"
#include "verilated.h"
#include "verilated_heavy.h"
#include "verilated_syms.h"

#include <map>
#include <vector>
#include <deque>
#include <string>

class VerilatedScope;

//======================================================================
// Types

class VerilatedImp {
    // Whole class is internal use only - Global information shared between verilated*.cpp files.

    // TYPES
    typedef vector<string> ArgVec;
    typedef map<pair<const void*,void*>,void*> UserMap;
    typedef map<const char*, const VerilatedScope*, VerilatedCStrCmp>  ScopeNameMap;
    typedef map<const char*, int, VerilatedCStrCmp>  ExportNameMap;

    // MEMBERS
    static VerilatedImp	s_s;		///< Static Singleton; One and only static this

    // Nothing here is save-restored; users expected to re-register appropriately

    ArgVec		m_argVec;	///< Argument list (NOT save-restored, may want different results)
    bool		m_argVecLoaded;	///< Ever loaded argument list
    UserMap	 	m_userMap;	///< Map of <(scope,userkey), userData>
    ScopeNameMap	m_nameMap;	///< Map of <scope_name, scope pointer>
    // Slow - somewhat static:
    ExportNameMap	m_exportMap;	///< Map of <export_func_proto, func number>
    int			m_exportNext;	///< Next export funcnum

    // File I/O
    vector<FILE*>	m_fdps;		///< File descriptors
    deque<IData>	m_fdFree;	///< List of free descriptors (SLOW - FOPEN/CLOSE only)

public: // But only for verilated*.cpp
    // CONSTRUCTORS
    VerilatedImp() : m_argVecLoaded(false), m_exportNext(0) {
	m_fdps.resize(3);
	m_fdps[0] = stdin;
	m_fdps[1] = stdout;
	m_fdps[2] = stderr;
    }
    ~VerilatedImp() {}
    static void internalsDump() {
	VL_PRINTF("internalsDump:\n");
	VL_PRINTF("  Argv:");
	for (ArgVec::iterator it=s_s.m_argVec.begin(); it!=s_s.m_argVec.end(); ++it) {
	    VL_PRINTF(" %s",it->c_str());
	}
	VL_PRINTF("\n");
	VL_PRINTF("  Version: %s %s\n", Verilated::productName(), Verilated::productVersion());
	scopesDump();
	exportsDump();
	userDump();
    }

    // METHODS - arguments
    static void commandArgs(int argc, const char** argv) {
	s_s.m_argVec.clear();
	for (int i=0; i<argc; i++) s_s.m_argVec.push_back(argv[i]);
	s_s.m_argVecLoaded = true; // Can't just test later for empty vector, no arguments is ok
    }
    static string argPlusMatch(const char* prefixp) {
	// Note prefixp does not include the leading "+"
	size_t len = strlen(prefixp);
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
    static void userDump() {
	bool first = true;
	for (UserMap::iterator it=s_s.m_userMap.begin(); it!=s_s.m_userMap.end(); ++it) {
	    if (first) { VL_PRINTF("  userDump:\n"); first=false; }
	    VL_PRINTF("    DPI_USER_DATA scope %p key %p: %p\n",
		      it->first.first, it->first.second, it->second);
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
	if (VL_LIKELY(it != s_s.m_nameMap.end())) return it->second;
	else return NULL;
    }
    static void scopeErase(const VerilatedScope* scopep) {
	// Slow ok - called once/scope at destruction
	userEraseScope(scopep);
	ScopeNameMap::iterator it=s_s.m_nameMap.find(scopep->name());
	if (it != s_s.m_nameMap.end()) s_s.m_nameMap.erase(it);
    }
    static void scopesDump() {
	VL_PRINTF("  scopesDump:\n");
	for (ScopeNameMap::iterator it=s_s.m_nameMap.begin(); it!=s_s.m_nameMap.end(); ++it) {
	    const VerilatedScope* scopep = it->second;
	    scopep->scopeDump();
	}
	VL_PRINTF("\n");
    }

public: // But only for verilated*.cpp
    // METHODS - export names

    // Each function prototype is converted to a function number which we
    // then use to index a 2D table also indexed by scope number, because we
    // can't know at Verilation time what scopes will exist in other modules
    // in the design that also happen to have our same callback function.
    // Rather than a 2D map, the integer scheme saves 500ish ns on a likely
    // miss at the cost of a multiply, and all lookups move to slowpath.
    static int exportInsert(const char* namep) {
	// Slow ok - called once/function at creation
	ExportNameMap::iterator it=s_s.m_exportMap.find(namep);
	if (it == s_s.m_exportMap.end()) {
	    s_s.m_exportMap.insert(it, make_pair(namep, s_s.m_exportNext++));
	    return s_s.m_exportNext++;
	} else {
	    return it->second;
	}
    }
    static int exportFind(const char* namep) {
	ExportNameMap::iterator it=s_s.m_exportMap.find(namep);
	if (VL_LIKELY(it != s_s.m_exportMap.end())) return it->second;
	string msg = (string("%Error: Testbench C called ")+namep
		      +" but no such DPI export function name exists in ANY model");
	vl_fatal("unknown",0,"", msg.c_str());
	return -1;
    }
    static const char* exportName(int funcnum) {
	// Slowpath; find name for given export; errors only so no map to reverse-map it
	for (ExportNameMap::iterator it=s_s.m_exportMap.begin(); it!=s_s.m_exportMap.end(); ++it) {
	    if (it->second == funcnum) return it->first;
	}
	return "*UNKNOWN*";
    }
    static void exportsDump() {
	bool first = true;
	for (ExportNameMap::iterator it=s_s.m_exportMap.begin(); it!=s_s.m_exportMap.end(); ++it) {
	    if (first) { VL_PRINTF("  exportDump:\n"); first=false; }
	    VL_PRINTF("    DPI_EXPORT_NAME %05d: %s\n", it->second, it->first);
	}
    }
    // We don't free up m_exportMap until the end, because we can't be sure
    // what other models are using the assigned funcnum's.

public: // But only for verilated*.cpp
    // METHODS - file IO
    static IData fdNew(FILE* fp) {
	if (VL_UNLIKELY(!fp)) return 0;
	// Bit 31 indicates it's a descriptor not a MCD
	if (s_s.m_fdFree.empty()) {
	    // Need to create more space in m_fdps and m_fdFree
	    size_t start = s_s.m_fdps.size();
	    s_s.m_fdps.resize(start*2);
	    for (size_t i=start; i<start*2; i++) s_s.m_fdFree.push_back((IData)i);
	}
	IData idx = s_s.m_fdFree.back(); s_s.m_fdFree.pop_back();
	s_s.m_fdps[idx] = fp;
	return (idx | (1UL<<31));  // bit 31 indicates not MCD
    }
    static void fdDelete(IData fdi) {
	IData idx = VL_MASK_I(31) & fdi;
	if (VL_UNLIKELY(!(fdi & (1ULL<<31)) || idx >= s_s.m_fdps.size())) return;
	if (VL_UNLIKELY(!s_s.m_fdps[idx])) return;  // Already free
	s_s.m_fdps[idx] = NULL;
	s_s.m_fdFree.push_back(idx);
    }
    static inline FILE* fdToFp(IData fdi) {
	IData idx = VL_MASK_I(31) & fdi;
	if (VL_UNLIKELY(!(fdi & (1ULL<<31)) || idx >= s_s.m_fdps.size())) return NULL;
	return s_s.m_fdps[idx];
    }
};

#endif  // Guard
