// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Command line options
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

#ifndef _V3OPTIONS_H_
#define _V3OPTIONS_H_ 1

#include "config_build.h"
#include "verilatedos.h"
#include <string>
#include <vector>
#include <map>
#include <set>

#include "V3Global.h"
#include "V3LangCode.h"

//######################################################################
// V3Options - Command line options

class V3OptionsImp;
class FileLine;
struct stat;

typedef vector<string> V3StringList;
typedef set<string> V3StringSet;

class V3Options {
    // TYPES
    typedef map<string,int> DebugSrcMap;

    // MEMBERS (general options)
    V3OptionsImp*	m_impp;		// Slow hidden options

    V3StringSet	m_cppFiles;	// argument: C++ files to link against
    V3StringSet	m_cFlags;	// argument: user CFLAGS
    V3StringSet	m_ldLibs;	// argument: user LDFLAGS
    V3StringSet	m_futures;	// argument: -Wfuture- list
    V3StringSet	m_libraryFiles;	// argument: Verilog -v files
    V3StringSet	m_clockers;	// argument: Verilog -clk signals
    V3StringSet	m_noClockers;	// argument: Verilog -noclk signals
    V3StringList m_vFiles;	// argument: Verilog files to read
    DebugSrcMap m_debugSrcs;	// argument: --debugi-<srcfile>=<level>
    DebugSrcMap m_dumpTrees;	// argument: --dump-treei-<srcfile>=<level>

    bool	m_preprocOnly;	// main switch: -E
    bool	m_makeDepend;	// main switch: -MMD
    bool	m_makePhony;	// main switch: -MP
    bool	m_preprocNoLine;// main switch: -P
    bool	m_assert;	// main switch: --assert
    bool	m_autoflush;	// main switch: --autoflush
    bool	m_bboxSys;	// main switch: --bbox-sys
    bool	m_bboxUnsup;	// main switch: --bbox-unsup
    bool	m_cdc;		// main switch: --cdc
    bool	m_coverageLine;	// main switch: --coverage-block
    bool	m_coverageToggle;// main switch: --coverage-toggle
    bool	m_coverageUnderscore;// main switch: --coverage-underscore
    bool	m_coverageUser;	// main switch: --coverage-func
    bool	m_debugCheck;	// main switch: --debug-check
    bool	m_exe;		// main switch: --exe
    bool	m_ignc;		// main switch: --ignc
    bool	m_inhibitSim;	// main switch: --inhibit-sim
    bool	m_l2Name;	// main switch: --l2name
    bool	m_lintOnly;	// main switch: --lint-only
    bool	m_orderClockDly;// main switch: --order-clock-delay
    bool	m_outFormatOk;	// main switch: --cc, --sc or --sp was specified
    bool	m_pinsScUint;   // main switch: --pins-sc-uint
    bool	m_pinsScBigUint;// main switch: --pins-sc-biguint
    bool	m_pinsUint8;	// main switch: --pins-uint8
    bool	m_profileCFuncs;// main switch: --profile-cfuncs
    bool	m_public;	// main switch: --public
    bool	m_savable;	// main switch: --savable
    bool	m_systemC;	// main switch: --sc: System C instead of simple C++
    bool	m_skipIdentical;// main switch: --skip-identical
    bool	m_systemPerl;	// main switch: --sp: System Perl instead of SystemC (m_systemC also set)
    bool	m_stats;	// main switch: --stats
    bool	m_statsVars;	// main switch: --stats-vars
    bool	m_trace;	// main switch: --trace
    bool	m_traceDups;	// main switch: --trace-dups
    bool	m_traceParams;	// main switch: --trace-params
    bool	m_traceStructs;	// main switch: --trace-structs
    bool	m_traceUnderscore;// main switch: --trace-underscore
    bool	m_underlineZero;// main switch: --underline-zero; undocumented old Verilator 2
    bool	m_reportUnoptflat; // main switch: --report-unoptflat
    bool	m_xInitialEdge;	// main switch: --x-initial-edge
    bool	m_xmlOnly;	// main switch: --xml-netlist

    int		m_convergeLimit;// main switch: --converge-limit
    int		m_dumpTree;	// main switch: --dump-tree
    int		m_ifDepth;	// main switch: --if-depth
    int		m_inlineMult;	// main switch: --inline-mult
    int		m_outputSplit;	// main switch: --output-split
    int		m_outputSplitCFuncs;// main switch: --output-split-cfuncs
    int		m_outputSplitCTrace;// main switch: --output-split-ctrace
    int		m_pinsBv;	// main switch: --pins-bv
    int		m_traceDepth;	// main switch: --trace-depth
    int		m_traceMaxArray;// main switch: --trace-max-array
    int		m_traceMaxWidth;// main switch: --trace-max-width
    int		m_unrollCount;	// main switch: --unroll-count
    int		m_unrollStmts;	// main switch: --unroll-stmts

    int		m_compLimitBlocks;	// compiler selection options
    int		m_compLimitParens;	// compiler selection options

    string	m_bin;		// main switch: --bin {binary}
    string	m_exeName;	// main switch: -o {name}
    string	m_flags;	// main switch: -f {name}
    string	m_makeDir;	// main switch: -Mdir
    string	m_modPrefix;	// main switch: --mod-prefix
    string	m_pipeFilter;	// main switch: --pipe-filter
    string	m_prefix;	// main switch: --prefix
    string	m_topModule;	// main switch: --top-module
    string	m_unusedRegexp;	// main switch: --unused-regexp
    string	m_xAssign;	// main switch: --x-assign

    // Language is now held in FileLine, on a per-node basis. However we still
    // have a concept of the default language at a global level.
    V3LangCode	m_defaultLanguage;	// main switch: --language

    // MEMBERS (optimizations)
    //				// main switch: -Op: --public
    bool	m_oAcycSimp;	// main switch: -Oy: acyclic pre-optimizations
    bool	m_oCase;	// main switch: -Oe: case tree conversion
    bool	m_oCombine;	// main switch: -Ob: common icode packing
    bool	m_oConst;	// main switch: -Oc: constant folding
    bool	m_oDedupe;	// main switch: -Od: logic deduplication
    bool	m_oAssemble;	// main switch: -Om: assign assemble 
    bool	m_oExpand;	// main switch: -Ox: expansion of C macros
    bool	m_oFlopGater;	// main switch: -Of: flop gater detection
    bool	m_oGate;	// main switch: -Og: gate wire elimination
    bool	m_oLife;	// main switch: -Ol: variable lifetime
    bool	m_oLifePost;	// main switch: -Ot: delayed assignment elimination
    bool	m_oLocalize;	// main switch: -Oz: convert temps to local variables
    bool	m_oInline;	// main switch: -Oi: module inlining
    bool	m_oReorder;	// main switch: -Or: reorder assignments in blocks
    bool	m_oSplit;	// main switch: -Os: always assignment splitting
    bool	m_oSubst;	// main switch: -Ou: substitute expression temp values
    bool	m_oSubstConst;	// main switch: -Ok: final constant substitution
    bool	m_oTable;	// main switch: -Oa: lookup table creation

  private:
    // METHODS
    void addArg(const string& flag);
    void addDefine(const string& defline, bool allowPlus);
    void addFuture(const string& flag);
    void addIncDirUser(const string& incdir);  // User requested
    void addIncDirFallback(const string& incdir);  // Low priority if not found otherwise
    void addLangExt(const string& langext, const V3LangCode& lc);
    void addLibExtV(const string& libext);
    void optimize(int level);
    void showVersion(bool verbose);
    void coverage(bool flag) { m_coverageLine = m_coverageToggle = m_coverageUser = flag; }
    bool onoff(const char* sw, const char* arg, bool& flag);
    bool suffixed(const char* sw, const char* arg);
    string parseFileArg(const string& optdir, const string& relfilename);
    bool parseLangExt(const char* swp, const char* langswp, const V3LangCode& lc);
    string filePathCheckOneDir(const string& modname, const string& dirname);

    static string getenvSYSTEMPERLGuts();

  public:
    // CREATORS
    V3Options();
    ~V3Options();
    void setDebugMode(int level);
    void setDebugSrcLevel(const string& srcfile, int level);
    int debugSrcLevel(const string& srcfile, int default_level=V3Error::debugDefault());
    void setDumpTreeLevel(const string& srcfile, int level);
    int dumpTreeLevel(const string& srcfile);

    // METHODS
    void addCppFile(const string& filename);
    void addCFlags(const string& filename);
    void addLdLibs(const string& filename);
    void addLibraryFile(const string& filename);
    void addClocker(const string& signame);
    void addNoClocker(const string& signame);
    void addVFile(const string& filename);

    // ACCESSORS (options)
    bool preprocOnly() const { return m_preprocOnly; }
    bool makeDepend() const { return m_makeDepend; }
    bool makePhony() const { return m_makePhony; }
    bool preprocNoLine() const { return m_preprocNoLine; }
    bool underlineZero() const { return m_underlineZero; }
    string bin() const { return m_bin; }
    string flags() const { return m_flags; }
    bool systemC() const { return m_systemC; }
    bool systemPerl() const { return m_systemPerl; }
    bool usingSystemCLibs() const { return !lintOnly() && (systemPerl() || systemC()); }
    bool usingSystemPerlLibs() const { return !lintOnly() && systemPerl(); }
    bool savable() const { return m_savable; }
    bool skipIdentical() const { return m_skipIdentical; }
    bool stats() const { return m_stats; }
    bool statsVars() const { return m_statsVars; }
    bool assertOn() const { return m_assert; }  // assertOn as __FILE__ may be defined
    bool autoflush() const { return m_autoflush; }
    bool bboxSys() const { return m_bboxSys; }
    bool bboxUnsup() const { return m_bboxUnsup; }
    bool cdc() const { return m_cdc; }
    bool coverage() const { return m_coverageLine || m_coverageToggle || m_coverageUser; }
    bool coverageLine() const { return m_coverageLine; }
    bool coverageToggle() const { return m_coverageToggle; }
    bool coverageUnderscore() const { return m_coverageUnderscore; }
    bool coverageUser() const { return m_coverageUser; }
    bool debugCheck() const { return m_debugCheck; }
    bool exe() const { return m_exe; }
    bool trace() const { return m_trace; }
    bool traceDups() const { return m_traceDups; }
    bool traceParams() const { return m_traceParams; }
    bool traceStructs() const { return m_traceStructs; }
    bool traceUnderscore() const { return m_traceUnderscore; }
    bool orderClockDly() const { return m_orderClockDly; }
    bool outFormatOk() const { return m_outFormatOk; }
    bool keepTempFiles() const { return (V3Error::debugDefault()!=0); }
    bool pinsScUint() const { return m_pinsScUint; }
    bool pinsScBigUint() const { return m_pinsScBigUint; }
    bool pinsUint8() const { return m_pinsUint8; }
    bool profileCFuncs() const { return m_profileCFuncs; }
    bool allPublic() const { return m_public; }
    bool l2Name() const { return m_l2Name; }
    bool lintOnly() const { return m_lintOnly; }
    bool ignc() const { return m_ignc; }
    bool inhibitSim() const { return m_inhibitSim; }
    bool reportUnoptflat() const { return m_reportUnoptflat; }
    bool xInitialEdge() const { return m_xInitialEdge; }
    bool xmlOnly() const { return m_xmlOnly; }

    int	   convergeLimit() const { return m_convergeLimit; }
    int    dumpTree() const { return m_dumpTree; }
    int	   ifDepth() const { return m_ifDepth; }
    int	   inlineMult() const { return m_inlineMult; }
    int	   outputSplit() const { return m_outputSplit; }
    int	   outputSplitCFuncs() const { return m_outputSplitCFuncs; }
    int	   outputSplitCTrace() const { return m_outputSplitCTrace; }
    int	   pinsBv() const { return m_pinsBv; }
    int	   traceDepth() const { return m_traceDepth; }
    int	   traceMaxArray() const { return m_traceMaxArray; }
    int	   traceMaxWidth() const { return m_traceMaxWidth; }
    int	   unrollCount() const { return m_unrollCount; }
    int	   unrollStmts() const { return m_unrollStmts; }

    int    compLimitBlocks() const { return m_compLimitBlocks; }
    int    compLimitParens() const { return m_compLimitParens; }

    string exeName() const { return m_exeName!="" ? m_exeName : prefix(); }
    string makeDir() const { return m_makeDir; }
    string modPrefix() const { return m_modPrefix; }
    string pipeFilter() const { return m_pipeFilter; }
    string prefix() const { return m_prefix; }
    string topModule() const { return m_topModule; }
    string unusedRegexp() const { return m_unusedRegexp; }
    string xAssign() const { return m_xAssign; }

    const V3StringSet& cppFiles() const { return m_cppFiles; }
    const V3StringSet& cFlags() const { return m_cFlags; }
    const V3StringSet& ldLibs() const { return m_ldLibs; }
    const V3StringSet& libraryFiles() const { return m_libraryFiles; }
    const V3StringList& vFiles() const { return m_vFiles; }
    const V3LangCode& defaultLanguage() const { return m_defaultLanguage; }

    bool isFuture(const string& flag) const;
    bool isLibraryFile(const string& filename) const;
    bool isClocker(const string& signame) const;
    bool isNoClocker(const string& signame) const;

    // ACCESSORS (optimization options)
    bool oAcycSimp() const { return m_oAcycSimp; }
    bool oCase() const { return m_oCase; }
    bool oCombine() const { return m_oCombine; }
    bool oConst() const { return m_oConst; }
    bool oDedupe() const { return m_oDedupe; }
    bool oAssemble() const { return m_oAssemble; }
    bool oExpand() const { return m_oExpand; }
    bool oFlopGater() const { return m_oFlopGater; }
    bool oGate() const { return m_oGate; }
    bool oDup() const { return oLife(); }
    bool oLife() const { return m_oLife; }
    bool oLifePost() const { return m_oLifePost; }
    bool oLocalize() const { return m_oLocalize; }
    bool oInline() const { return m_oInline; }
    bool oReorder() const { return m_oReorder; }
    bool oSplit() const { return m_oSplit; }
    bool oSubst() const { return m_oSubst; }
    bool oSubstConst() const { return m_oSubstConst; }
    bool oTable() const { return m_oTable; }

    // METHODS (uses above)
    string traceClassBase() const { return systemPerl() ? "SpTraceVcd" : "VerilatedVcd"; }

    // METHODS (from main)
    static string version();
    static string argString(int argc, char** argv);	///< Return list of arguments as simple string
    string allArgsString();	///< Return all passed arguments as simple string
    void bin(const string& flag) { m_bin = flag; }
    void parseOpts(FileLine* fl, int argc, char** argv);
    void parseOptsList (FileLine* fl, const string& optdir, int argc, char** argv);
    void parseOptsFile (FileLine* fl, const string& filename, bool rel);

    // METHODS (environment)
    // Most of these may be built into the executable with --enable-defenv,
    // see the README.  If adding new variables, also see src/Makefile_obj.in
    // Also add to V3Options::showVersion()
    static string getenvPERL();
    static string getenvSYSTEMC();
    static string getenvSYSTEMC_ARCH();
    static string getenvSYSTEMC_INCLUDE();
    static string getenvSYSTEMC_LIBDIR();
    static string getenvSYSTEMPERL();
    static string getenvSYSTEMPERL_INCLUDE();
    static string getenvVERILATOR_ROOT();

    // METHODS (file utilities using these options)
    string fileExists (const string& filename);
    string filePath (FileLine* fl, const string& modname, const string& errmsg);
    void filePathLookedMsg(FileLine* fl, const string& modname);
    V3LangCode fileLanguage(const string &filename);
    static bool fileStatDir (const string& filename);
    static bool fileStatNormal (const string& filename);
    static void fileNfsFlush(const string& filename);

    // METHODS (other OS)
    static void throwSigsegv();
};

//######################################################################

#endif // guard
