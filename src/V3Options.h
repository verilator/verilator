// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Command line options
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef _V3OPTIONS_H_
#define _V3OPTIONS_H_ 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3LangCode.h"

#include <map>
#include <set>
#include <string>
#include <vector>

class V3OptionsImp;
class FileLine;

//######################################################################

class VOptionBool {
    // Class to track options that are either not specified (and default
    // true/false), versus user setting the option to true or false
public:
    enum en {
        OPT_DEFAULT_FALSE = 0,
        OPT_DEFAULT_TRUE,
        OPT_TRUE,
        OPT_FALSE,
        _ENUM_END
    };
    enum en m_e;
    inline VOptionBool() : m_e(OPT_DEFAULT_FALSE) {}
    // cppcheck-suppress noExplicitConstructor
    inline VOptionBool(en _e) : m_e(_e) {}
    explicit inline VOptionBool(int _e) : m_e(static_cast<en>(_e)) {}
    operator en() const { return m_e; }
    bool isDefault() const { return m_e == OPT_DEFAULT_FALSE || m_e == OPT_DEFAULT_TRUE; }
    bool isTrue() const { return m_e == OPT_TRUE || m_e == OPT_DEFAULT_TRUE; }
    bool isFalse() const { return m_e == OPT_FALSE || m_e == OPT_DEFAULT_FALSE; }
    void setTrueOrFalse(bool flag) { m_e = flag ? OPT_TRUE : OPT_FALSE; }
    const char* ascii() const {
        static const char* const names[] = {
            "DEFAULT_FALSE", "DEFAULT_TRUE", "TRUE", "FALSE"};
        return names[m_e]; }
};
inline bool operator==(const VOptionBool& lhs, const VOptionBool& rhs) {
    return lhs.m_e == rhs.m_e;
}
inline bool operator==(const VOptionBool& lhs, VOptionBool::en rhs) { return lhs.m_e == rhs; }
inline bool operator==(VOptionBool::en lhs, const VOptionBool& rhs) { return lhs == rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const VOptionBool& rhs) {
    return os << rhs.ascii();
}

//######################################################################

class TraceFormat {
public:
    enum en {
        VCD = 0,
        FST,
        FST_THREAD
    } m_e;
    inline TraceFormat(en _e = VCD) : m_e(_e) {}
    explicit inline TraceFormat(int _e) : m_e(static_cast<en>(_e)) {}
    operator en() const { return m_e; }
    bool fstFlavor() const { return m_e == FST || m_e == FST_THREAD; }
    bool threaded() const { return m_e == FST_THREAD; }
    string classBase() const {
        static const char* const names[] = {
            "VerilatedVcd",
            "VerilatedFst",
            "VerilatedFst"
        };
        return names[m_e];
    }
    string sourceName() const {
        static const char* const names[] = {
            "verilated_vcd",
            "verilated_fst",
            "verilated_fst"
        };
        return names[m_e];
    }
};
inline bool operator==(const TraceFormat& lhs, const TraceFormat& rhs) {
    return lhs.m_e == rhs.m_e;
}
inline bool operator==(const TraceFormat& lhs, TraceFormat::en rhs) { return lhs.m_e == rhs; }
inline bool operator==(TraceFormat::en lhs, const TraceFormat& rhs) { return lhs == rhs.m_e; }

typedef std::vector<string> V3StringList;
typedef std::set<string> V3StringSet;

//######################################################################
// V3Options - Command line options

class V3Options {
  public:

  private:
    // TYPES
    typedef std::map<string,int> DebugSrcMap;

    // MEMBERS (general options)
    V3OptionsImp*       m_impp;         // Slow hidden options

    V3StringSet m_cppFiles;     // argument: C++ files to link against
    V3StringList m_cFlags;      // argument: user CFLAGS
    V3StringList m_ldLibs;      // argument: user LDFLAGS
    V3StringSet m_futures;      // argument: -Wfuture- list
    V3StringSet m_libraryFiles; // argument: Verilog -v files
    V3StringSet m_clockers;     // argument: Verilog -clk signals
    V3StringSet m_noClockers;   // argument: Verilog -noclk signals
    V3StringList m_vFiles;      // argument: Verilog files to read
    V3StringList m_forceIncs;   // argument: -FI
    DebugSrcMap m_debugSrcs;    // argument: --debugi-<srcfile>=<level>
    DebugSrcMap m_dumpTrees;    // argument: --dump-treei-<srcfile>=<level>
    std::map<string,string> m_parameters;  // Parameters


    bool        m_preprocOnly;  // main switch: -E
    bool        m_makePhony;    // main switch: -MP
    bool        m_preprocNoLine;// main switch: -P
    bool        m_assert;       // main switch: --assert
    bool        m_autoflush;    // main switch: --autoflush
    bool        m_bboxSys;      // main switch: --bbox-sys
    bool        m_bboxUnsup;    // main switch: --bbox-unsup
    bool        m_cdc;          // main switch: --cdc
    bool        m_cmake;        // main switch: --make cmake
    bool        m_context;      // main switch: --Wcontext
    bool        m_coverageLine; // main switch: --coverage-block
    bool        m_coverageToggle;// main switch: --coverage-toggle
    bool        m_coverageUnderscore;// main switch: --coverage-underscore
    bool        m_coverageUser; // main switch: --coverage-func
    bool        m_debugCheck;   // main switch: --debug-check
    bool        m_debugCollision;  // main switch: --debug-collision
    bool        m_debugLeak;    // main switch: --debug-leak
    bool        m_debugNondeterminism;  // main switch: --debug-nondeterminism
    bool        m_debugPartition;  // main switch: --debug-partition
    bool        m_debugProtect;  // main switch: --debug-protect
    bool        m_debugSelfTest;  // main switch: --debug-self-test
    bool        m_decoration;   // main switch: --decoration
    bool        m_dpiHdrOnly;   // main switch: --dpi-hdr-only
    bool        m_dumpDefines;  // main switch: --dump-defines
    bool        m_exe;          // main switch: --exe
    bool        m_ignc;         // main switch: --ignc
    bool        m_inhibitSim;   // main switch: --inhibit-sim
    bool        m_lintOnly;     // main switch: --lint-only
    bool        m_gmake;        // main switch: --make gmake
    bool        m_orderClockDly;// main switch: --order-clock-delay
    bool        m_outFormatOk;  // main switch: --cc, --sc or --sp was specified
    bool        m_pedantic;     // main switch: --Wpedantic
    bool        m_pinsScUint;   // main switch: --pins-sc-uint
    bool        m_pinsScBigUint;// main switch: --pins-sc-biguint
    bool        m_pinsUint8;    // main switch: --pins-uint8
    bool        m_ppComments;   // main switch: --pp-comments
    bool        m_profCFuncs;   // main switch: --prof-cfuncs
    bool        m_profThreads;  // main switch: --prof-threads
    bool        m_protectIds;   // main switch: --protect-ids
    bool        m_public;       // main switch: --public
    bool        m_publicFlatRW;  // main switch: --public-flat-rw
    bool        m_quietExit;  // main switch: --quiet-exit
    bool        m_relativeCFuncs; // main switch: --relative-cfuncs
    bool        m_relativeIncludes; // main switch: --relative-includes
    bool        m_reportUnoptflat; // main switch: --report-unoptflat
    bool        m_savable;      // main switch: --savable
    bool        m_structsPacked;  // main switch: --structs-packed
    bool        m_systemC;      // main switch: --sc: System C instead of simple C++
    bool        m_stats;        // main switch: --stats
    bool        m_statsVars;    // main switch: --stats-vars
    bool        m_threadsCoarsen;  // main switch: --threads-coarsen
    bool        m_threadsDpiPure;  // main switch: --threads-dpi all/pure
    bool        m_threadsDpiUnpure;  // main switch: --threads-dpi all
    bool        m_trace;        // main switch: --trace
    bool        m_traceCoverage;  // main switch: --trace-coverage
    bool        m_traceDups;    // main switch: --trace-dups
    bool        m_traceParams;  // main switch: --trace-params
    bool        m_traceStructs; // main switch: --trace-structs
    bool        m_traceUnderscore;// main switch: --trace-underscore
    bool        m_underlineZero;// main switch: --underline-zero; undocumented old Verilator 2
    bool        m_vpi;          // main switch: --vpi
    bool        m_xInitialEdge; // main switch: --x-initial-edge
    bool        m_xmlOnly;      // main switch: --xml-netlist

    int         m_convergeLimit;// main switch: --converge-limit
    int         m_dumpTree;     // main switch: --dump-tree
    int         m_gateStmts;    // main switch: --gate-stmts
    int         m_ifDepth;      // main switch: --if-depth
    int         m_inlineMult;   // main switch: --inline-mult
    VOptionBool m_makeDepend;  // main switch: -MMD
    int         m_maxNumWidth;  // main switch: --max-num-width
    int         m_moduleRecursion;// main switch: --module-recursion-depth
    int         m_outputSplit;  // main switch: --output-split
    int         m_outputSplitCFuncs;// main switch: --output-split-cfuncs
    int         m_outputSplitCTrace;// main switch: --output-split-ctrace
    int         m_pinsBv;       // main switch: --pins-bv
    VOptionBool m_skipIdentical;  // main switch: --skip-identical
    int         m_threads;      // main switch: --threads (0 == --no-threads)
    int         m_threadsMaxMTasks;  // main switch: --threads-max-mtasks
    int         m_traceDepth;   // main switch: --trace-depth
    TraceFormat m_traceFormat;  // main switch: --trace or --trace-fst
    int         m_traceMaxArray;// main switch: --trace-max-array
    int         m_traceMaxWidth;// main switch: --trace-max-width
    int         m_unrollCount;  // main switch: --unroll-count
    int         m_unrollStmts;  // main switch: --unroll-stmts

    int         m_compLimitBlocks;  // compiler selection; number of nested blocks
    int         m_compLimitMembers;  // compiler selection; number of members in struct before make anon array
    int         m_compLimitParens;  // compiler selection; number of nested parens

    string      m_bin;          // main switch: --bin {binary}
    string      m_exeName;      // main switch: -o {name}
    string      m_flags;        // main switch: -f {name}
    string      m_l2Name;       // main switch: --l2name; "" for top-module's name
    string      m_makeDir;      // main switch: -Mdir
    string      m_modPrefix;    // main switch: --mod-prefix
    string      m_pipeFilter;   // main switch: --pipe-filter
    string      m_prefix;       // main switch: --prefix
    string      m_protectKey;   // main switch: --protect-key
    string      m_protectLib;   // main switch: --protect-lib {lib_name}
    string      m_topModule;    // main switch: --top-module
    string      m_unusedRegexp; // main switch: --unused-regexp
    string      m_xAssign;      // main switch: --x-assign
    string      m_xInitial;     // main switch: --x-initial
    string      m_xmlOutput;    // main switch: --xml-output

    // Language is now held in FileLine, on a per-node basis. However we still
    // have a concept of the default language at a global level.
    V3LangCode  m_defaultLanguage;      // main switch: --language

    // MEMBERS (optimizations)
    //                          // main switch: -Op: --public
    bool        m_oAcycSimp;    // main switch: -Oy: acyclic pre-optimizations
    bool        m_oCase;        // main switch: -Oe: case tree conversion
    bool        m_oCombine;     // main switch: -Ob: common icode packing
    bool        m_oConst;       // main switch: -Oc: constant folding
    bool        m_oDedupe;      // main switch: -Od: logic deduplication
    bool        m_oAssemble;    // main switch: -Om: assign assemble
    bool        m_oExpand;      // main switch: -Ox: expansion of C macros
    bool        m_oGate;        // main switch: -Og: gate wire elimination
    bool        m_oLife;        // main switch: -Ol: variable lifetime
    bool        m_oLifePost;    // main switch: -Ot: delayed assignment elimination
    bool        m_oLocalize;    // main switch: -Oz: convert temps to local variables
    bool        m_oInline;      // main switch: -Oi: module inlining
    bool        m_oReloop;      // main switch: -Ov: reform loops
    bool        m_oReorder;     // main switch: -Or: reorder assignments in blocks
    bool        m_oSplit;       // main switch: -Os: always assignment splitting
    bool        m_oSubst;       // main switch: -Ou: substitute expression temp values
    bool        m_oSubstConst;  // main switch: -Ok: final constant substitution
    bool        m_oTable;       // main switch: -Oa: lookup table creation

  private:
    // METHODS
    void addArg(const string& arg);
    void addDefine(const string& defline, bool allowPlus);
    void addFuture(const string& flag);
    void addIncDirUser(const string& incdir);  // User requested
    void addIncDirFallback(const string& incdir);  // Low priority if not found otherwise
    void addParameter(const string& paramline, bool allowPlus);
    void addLangExt(const string& langext, const V3LangCode& lc);
    void addLibExtV(const string& libext);
    void optimize(int level);
    void showVersion(bool verbose);
    void coverage(bool flag) { m_coverageLine = m_coverageToggle = m_coverageUser = flag; }
    bool onoff(const char* sw, const char* arg, bool& flag);
    bool onoffb(const char* sw, const char* arg, VOptionBool& flag);
    bool suffixed(const string& sw, const char* arg);
    string parseFileArg(const string& optdir, const string& relfilename);
    bool parseLangExt(const char* swp, const char* langswp, const V3LangCode& lc);
    string filePathCheckOneDir(const string& modname, const string& dirname);

    // CONSTRUCTORS
    VL_UNCOPYABLE(V3Options);
  public:
    V3Options();
    ~V3Options();
    void setDebugMode(int level);
    void setDebugSrcLevel(const string& srcfile, int level);
    int debugSrcLevel(const string& srcfile_path, int default_level=V3Error::debugDefault());
    void setDumpTreeLevel(const string& srcfile, int level);
    int dumpTreeLevel(const string& srcfile_path);

    // METHODS
    void addCppFile(const string& filename);
    void addCFlags(const string& filename);
    void addLdLibs(const string& filename);
    void addLibraryFile(const string& filename);
    void addClocker(const string& signame);
    void addNoClocker(const string& signame);
    void addVFile(const string& filename);
    void addForceInc(const string& filename);
    void notify();

    // ACCESSORS (options)
    bool preprocOnly() const { return m_preprocOnly; }
    bool makePhony() const { return m_makePhony; }
    bool preprocNoLine() const { return m_preprocNoLine; }
    bool underlineZero() const { return m_underlineZero; }
    string bin() const { return m_bin; }
    string flags() const { return m_flags; }
    bool systemC() const { return m_systemC; }
    bool usingSystemCLibs() const { return !lintOnly() && systemC(); }
    bool savable() const { return m_savable; }
    bool stats() const { return m_stats; }
    bool statsVars() const { return m_statsVars; }
    bool structsPacked() const { return m_structsPacked; }
    bool assertOn() const { return m_assert; }  // assertOn as __FILE__ may be defined
    bool autoflush() const { return m_autoflush; }
    bool bboxSys() const { return m_bboxSys; }
    bool bboxUnsup() const { return m_bboxUnsup; }
    bool cdc() const { return m_cdc; }
    bool cmake() const { return m_cmake; }
    bool context() const { return m_context; }
    bool coverage() const { return m_coverageLine || m_coverageToggle || m_coverageUser; }
    bool coverageLine() const { return m_coverageLine; }
    bool coverageToggle() const { return m_coverageToggle; }
    bool coverageUnderscore() const { return m_coverageUnderscore; }
    bool coverageUser() const { return m_coverageUser; }
    bool debugCheck() const { return m_debugCheck; }
    bool debugCollision() const { return m_debugCollision; }
    bool debugLeak() const { return m_debugLeak; }
    bool debugNondeterminism() const { return m_debugNondeterminism; }
    bool debugPartition() const { return m_debugPartition; }
    bool debugProtect() const { return m_debugProtect; }
    bool debugSelfTest() const { return m_debugSelfTest; }
    bool decoration() const { return m_decoration; }
    bool dpiHdrOnly() const { return m_dpiHdrOnly; }
    bool dumpDefines() const { return m_dumpDefines; }
    bool exe() const { return m_exe; }
    bool gmake() const { return m_gmake; }
    bool threadsDpiPure() const { return m_threadsDpiPure; }
    bool threadsDpiUnpure() const { return m_threadsDpiUnpure; }
    bool threadsCoarsen() const { return m_threadsCoarsen; }
    bool trace() const { return m_trace; }
    bool traceCoverage() const { return m_traceCoverage; }
    bool traceDups() const { return m_traceDups; }
    bool traceParams() const { return m_traceParams; }
    bool traceStructs() const { return m_traceStructs; }
    bool traceUnderscore() const { return m_traceUnderscore; }
    bool orderClockDly() const { return m_orderClockDly; }
    bool outFormatOk() const { return m_outFormatOk; }
    bool keepTempFiles() const { return (V3Error::debugDefault()!=0); }
    bool pedantic() const { return m_pedantic; }
    bool pinsScUint() const { return m_pinsScUint; }
    bool pinsScBigUint() const { return m_pinsScBigUint; }
    bool pinsUint8() const { return m_pinsUint8; }
    bool ppComments() const { return m_ppComments; }
    bool profCFuncs() const { return m_profCFuncs; }
    bool profThreads() const { return m_profThreads; }
    bool protectIds() const { return m_protectIds; }
    bool allPublic() const { return m_public; }
    bool publicFlatRW() const { return m_publicFlatRW; }
    bool lintOnly() const { return m_lintOnly; }
    bool ignc() const { return m_ignc; }
    bool inhibitSim() const { return m_inhibitSim; }
    bool quietExit() const { return m_quietExit; }
    bool relativeCFuncs() const { return m_relativeCFuncs; }
    bool reportUnoptflat() const { return m_reportUnoptflat; }
    bool vpi() const { return m_vpi; }
    bool xInitialEdge() const { return m_xInitialEdge; }
    bool xmlOnly() const { return m_xmlOnly; }

    int convergeLimit() const { return m_convergeLimit; }
    int dumpTree() const { return m_dumpTree; }
    int gateStmts() const { return m_gateStmts; }
    int ifDepth() const { return m_ifDepth; }
    int inlineMult() const { return m_inlineMult; }
    VOptionBool makeDepend() const { return m_makeDepend; }
    int maxNumWidth() const { return m_maxNumWidth; }
    int moduleRecursionDepth() const { return m_moduleRecursion; }
    int outputSplit() const { return m_outputSplit; }
    int outputSplitCFuncs() const { return m_outputSplitCFuncs; }
    int outputSplitCTrace() const { return m_outputSplitCTrace; }
    int pinsBv() const { return m_pinsBv; }
    VOptionBool skipIdentical() const { return m_skipIdentical; }
    int threads() const { return m_threads; }
    int threadsMaxMTasks() const { return m_threadsMaxMTasks; }
    bool mtasks() const { return (m_threads > 1); }
    int traceDepth() const { return m_traceDepth; }
    TraceFormat traceFormat() const { return m_traceFormat; }
    int traceMaxArray() const { return m_traceMaxArray; }
    int traceMaxWidth() const { return m_traceMaxWidth; }
    int unrollCount() const { return m_unrollCount; }
    int unrollStmts() const { return m_unrollStmts; }

    int compLimitBlocks() const { return m_compLimitBlocks; }
    int compLimitMembers() const { return m_compLimitMembers; }
    int compLimitParens() const { return m_compLimitParens; }

    string exeName() const { return m_exeName!="" ? m_exeName : prefix(); }
    string l2Name() const { return m_l2Name; }
    string makeDir() const { return m_makeDir; }
    string modPrefix() const { return m_modPrefix; }
    string pipeFilter() const { return m_pipeFilter; }
    string prefix() const { return m_prefix; }
    string protectKey() const { return m_protectKey; }
    string protectKeyDefaulted();  // Set default key if not set by user
    string protectLib() const { return m_protectLib; }
    string protectLibName(bool shared) {
        string libName = "lib"+protectLib();
        if (shared) {
            libName += ".so";
        } else {
            libName += ".a";
        }
        return libName;
    }
    string topModule() const { return m_topModule; }
    string unusedRegexp() const { return m_unusedRegexp; }
    string xAssign() const { return m_xAssign; }
    string xInitial() const { return m_xInitial; }
    string xmlOutput() const { return m_xmlOutput; }

    const V3StringSet& cppFiles() const { return m_cppFiles; }
    const V3StringList& cFlags() const { return m_cFlags; }
    const V3StringList& ldLibs() const { return m_ldLibs; }
    const V3StringSet& libraryFiles() const { return m_libraryFiles; }
    const V3StringList& vFiles() const { return m_vFiles; }
    const V3StringList& forceIncs() const { return m_forceIncs; }
    const V3LangCode& defaultLanguage() const { return m_defaultLanguage; }

    bool hasParameter(const string& name);
    string parameter(const string& name);
    void checkParameters();

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
    bool oGate() const { return m_oGate; }
    bool oDup() const { return oLife(); }
    bool oLife() const { return m_oLife; }
    bool oLifePost() const { return m_oLifePost; }
    bool oLocalize() const { return m_oLocalize; }
    bool oInline() const { return m_oInline; }
    bool oReloop() const { return m_oReloop; }
    bool oReorder() const { return m_oReorder; }
    bool oSplit() const { return m_oSplit; }
    bool oSubst() const { return m_oSubst; }
    bool oSubstConst() const { return m_oSubstConst; }
    bool oTable() const { return m_oTable; }

    string traceClassBase() const { return m_traceFormat.classBase(); }
    string traceClassLang() const { return m_traceFormat.classBase() + (systemC() ? "Sc" : "C"); }
    string traceSourceBase() const { return m_traceFormat.sourceName(); }
    string traceSourceLang() const {
        return m_traceFormat.sourceName() + (systemC() ? "_sc" : "_c");
    }

    // METHODS (from main)
    static string version();
    static string argString(int argc, char** argv);  ///< Return list of arguments as simple string
    string allArgsString();  ///< Return all passed arguments as simple string
    void bin(const string& flag) { m_bin = flag; }
    void parseOpts(FileLine* fl, int argc, char** argv);
    void parseOptsList(FileLine* fl, const string& optdir, int argc, char** argv);
    void parseOptsFile(FileLine* fl, const string& filename, bool rel);

    // METHODS (environment)
    // Most of these may be built into the executable with --enable-defenv,
    // see the README.  If adding new variables, also see src/Makefile_obj.in
    // Also add to V3Options::showVersion()
    static string getenvBuiltins(const string& var);
    static string getenvPERL();
    static string getenvSYSTEMC();
    static string getenvSYSTEMC_ARCH();
    static string getenvSYSTEMC_INCLUDE();
    static string getenvSYSTEMC_LIBDIR();
    static string getenvVERILATOR_ROOT();

    // METHODS (file utilities using these options)
    string fileExists(const string& filename);
    string filePath(FileLine* fl, const string& modname,
                    const string& lastpath, const string& errmsg);
    void filePathLookedMsg(FileLine* fl, const string& modname);
    V3LangCode fileLanguage(const string &filename);
    static bool fileStatDir(const string& filename);
    static bool fileStatNormal(const string& filename);
    static void fileNfsFlush(const string& filename);

    // METHODS (other OS)
    static void throwSigsegv();
};

//######################################################################

#endif  // guard
