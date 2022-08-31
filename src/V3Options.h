// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Command line options
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3OPTIONS_H_
#define VERILATOR_V3OPTIONS_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3LangCode.h"

#include <map>
#include <set>
#include <string>
#include <vector>

class V3OptionsImp;
class FileLine;

//######################################################################

class VOptionBool final {
    // Class to track options that are either not specified (and default
    // true/false), versus user setting the option to true or false
public:
    enum en : uint8_t { OPT_DEFAULT_FALSE = 0, OPT_DEFAULT_TRUE, OPT_TRUE, OPT_FALSE };
    enum en m_e;
    inline VOptionBool()
        : m_e{OPT_DEFAULT_FALSE} {}
    // cppcheck-suppress noExplicitConstructor
    inline VOptionBool(en _e)
        : m_e{_e} {}
    explicit inline VOptionBool(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    operator en() const { return m_e; }
    bool isDefault() const { return m_e == OPT_DEFAULT_FALSE || m_e == OPT_DEFAULT_TRUE; }
    bool isTrue() const { return m_e == OPT_TRUE || m_e == OPT_DEFAULT_TRUE; }
    bool isSetTrue() const { return m_e == OPT_TRUE; }
    bool isSetFalse() const { return m_e == OPT_FALSE; }
    void setTrueOrFalse(bool flag) { m_e = flag ? OPT_TRUE : OPT_FALSE; }
};
inline bool operator==(const VOptionBool& lhs, const VOptionBool& rhs) {
    return lhs.m_e == rhs.m_e;
}
inline bool operator==(const VOptionBool& lhs, VOptionBool::en rhs) { return lhs.m_e == rhs; }
inline bool operator==(VOptionBool::en lhs, const VOptionBool& rhs) { return lhs == rhs.m_e; }

//######################################################################

class VTimescale final {
public:
    enum en : uint8_t {
        // clang-format off
        TS_100S = 0, TS_10S = 1, TS_1S = 2,
        TS_100MS = 3, TS_10MS = 4, TS_1MS = 5,
        TS_100US = 6, TS_10US = 7, TS_1US = 8,
        TS_100NS = 9, TS_10NS = 10, TS_1NS = 11,
        TS_100PS = 12, TS_10PS = 13, TS_1PS = 14,
        TS_100FS = 15, TS_10FS = 16, TS_1FS = 17,
        // clang-format on
        NONE = 18,
        _ENUM_END
    };
    enum : uint8_t { TS_DEFAULT = TS_1PS };
    enum en m_e;
    // CONSTRUCTOR
    inline VTimescale()
        : m_e{NONE} {}
    // cppcheck-suppress noExplicitConstructor
    inline VTimescale(en _e)
        : m_e{_e} {}
    explicit inline VTimescale(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    // Construct from string
    VTimescale(const string& value, bool& badr);
    VTimescale(double value, bool& badr) {
        badr = false;
        for (int i = TS_100S; i < _ENUM_END; ++i) {
            m_e = static_cast<en>(i);
            if (multiplier() == value) break;
        }
        if (multiplier() != value) {
            m_e = NONE;
            badr = true;
        }
    }
    bool isNone() const { return m_e == NONE; }
    // Parse a "unit/precision" string into two VTimescales, with error checking
    static void parseSlashed(FileLine* fl, const char* textp, VTimescale& unitr, VTimescale& precr,
                             bool allowEmpty = false);
    const char* ascii() const {
        static const char* const names[]
            = {"100s", "10s", "1s",    "100ms", "10ms", "1ms",   "100us", "10us", "1us", "100ns",
               "10ns", "1ns", "100ps", "10ps",  "1ps",  "100fs", "10fs",  "1fs",  "NONE"};
        return names[m_e];
    }
    int powerOfTen() const { return 2 - static_cast<int>(m_e); }
    double multiplier() const {
        static const double values[]
            = {100,  10,   1,     1e-1,  1e-2,  1e-3,  1e-4,  1e-5,  1e-6, 1e-7,
               1e-8, 1e-9, 1e-10, 1e-11, 1e-12, 1e-13, 1e-14, 1e-15, 0};
        return values[m_e];
    }
};
inline bool operator==(const VTimescale& lhs, const VTimescale& rhs) { return lhs.m_e == rhs.m_e; }
inline bool operator==(const VTimescale& lhs, VTimescale::en rhs) { return lhs.m_e == rhs; }
inline bool operator==(VTimescale::en lhs, const VTimescale& rhs) { return lhs == rhs.m_e; }
// Comparisons are based on time, not enum values, so seconds > milliseconds
inline bool operator<(const VTimescale& lhs, const VTimescale& rhs) { return lhs.m_e > rhs.m_e; }
inline std::ostream& operator<<(std::ostream& os, const VTimescale& rhs) {
    return os << rhs.ascii();
}

//######################################################################

class TraceFormat final {
public:
    enum en : uint8_t { VCD = 0, FST } m_e;
    // cppcheck-suppress noExplicitConstructor
    inline TraceFormat(en _e = VCD)
        : m_e{_e} {}
    explicit inline TraceFormat(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    operator en() const { return m_e; }
    bool fst() const { return m_e == FST; }
    bool vcd() const { return m_e == VCD; }
    string classBase() const {
        static const char* const names[] = {"VerilatedVcd", "VerilatedFst"};
        return names[m_e];
    }
    string sourceName() const {
        static const char* const names[] = {"verilated_vcd", "verilated_fst"};
        return names[m_e];
    }
};
inline bool operator==(const TraceFormat& lhs, const TraceFormat& rhs) {
    return lhs.m_e == rhs.m_e;
}
inline bool operator==(const TraceFormat& lhs, TraceFormat::en rhs) { return lhs.m_e == rhs; }
inline bool operator==(TraceFormat::en lhs, const TraceFormat& rhs) { return lhs == rhs.m_e; }

using V3StringList = std::vector<std::string>;
using V3StringSet = std::set<std::string>;

//######################################################################

// Information given by --hierarchical-block option
class V3HierarchicalBlockOption final {
public:
    // key:parameter name, value:value (as string)
    using ParamStrMap = std::map<const std::string, std::string>;

private:
    string m_origName;  // module name
    // module name after uniquified
    // same as m_origName for non-parameterized module
    string m_mangledName;
    // overriding parameter values specified by -G option
    ParamStrMap m_parameters;

public:
    explicit V3HierarchicalBlockOption(const string& optstring);
    const string& origName() const { return m_origName; }
    const string& mangledName() const { return m_mangledName; }
    const ParamStrMap params() const { return m_parameters; }
};

using V3HierBlockOptSet = std::map<const std::string, V3HierarchicalBlockOption>;

//######################################################################
// V3Options - Command line options

class V3Options final {
public:
private:
    // TYPES
    using DebugSrcMap = std::map<const std::string, int>;

    // MEMBERS (general options)
    V3OptionsImp* m_impp;  // Slow hidden options

    // clang-format off
    V3StringSet m_cppFiles;     // argument: C++ files to link against
    V3StringList m_cFlags;      // argument: user CFLAGS
    V3StringList m_ldLibs;      // argument: user LDFLAGS
    V3StringList m_makeFlags;   // argument: user MAKEFLAGS
    V3StringSet m_futures;      // argument: -Wfuture- list
    V3StringSet m_future0s;     // argument: -future list
    V3StringSet m_future1s;     // argument: -future1 list
    V3StringSet m_libraryFiles; // argument: Verilog -v files
    V3StringSet m_clockers;     // argument: Verilog -clk signals
    V3StringSet m_noClockers;   // argument: Verilog -noclk signals
    V3StringList m_vFiles;      // argument: Verilog files to read
    V3StringList m_forceIncs;   // argument: -FI
    DebugSrcMap m_debugSrcs;    // argument: --debugi-<srcfile>=<level>
    DebugSrcMap m_dumpTrees;    // argument: --dump-treei-<srcfile>=<level>
    std::map<const string, string> m_parameters;  // Parameters
    std::map<const string, V3HierarchicalBlockOption> m_hierBlocks;  // main switch: --hierarchical-block

    bool m_preprocOnly = false;     // main switch: -E
    bool m_makePhony = false;       // main switch: -MP
    bool m_preprocNoLine = false;   // main switch: -P
    bool m_assert = false;          // main switch: --assert
    bool m_autoflush = false;       // main switch: --autoflush
    bool m_bboxSys = false;         // main switch: --bbox-sys
    bool m_bboxUnsup = false;       // main switch: --bbox-unsup
    bool m_build = false;           // main switch: --build
    bool m_cdc = false;             // main switch: --cdc
    bool m_cmake = false;           // main switch: --make cmake
    bool m_context = true;          // main switch: --Wcontext
    bool m_coverageLine = false;    // main switch: --coverage-block
    bool m_coverageToggle = false;  // main switch: --coverage-toggle
    bool m_coverageUnderscore = false;  // main switch: --coverage-underscore
    bool m_coverageUser = false;    // main switch: --coverage-func
    bool m_debugCheck = false;      // main switch: --debug-check
    bool m_debugCollision = false;  // main switch: --debug-collision
    bool m_debugEmitV = false;      // main switch: --debug-emitv
    bool m_debugExitParse = false;  // main switch: --debug-exit-parse
    bool m_debugExitUvm = false;    // main switch: --debug-exit-uvm
    bool m_debugLeak = true;        // main switch: --debug-leak
    bool m_debugNondeterminism = false;  // main switch: --debug-nondeterminism
    bool m_debugPartition = false;  // main switch: --debug-partition
    bool m_debugProtect = false;    // main switch: --debug-protect
    bool m_debugSelfTest = false;   // main switch: --debug-self-test
    bool m_decoration = true;       // main switch: --decoration
    bool m_dpiHdrOnly = false;      // main switch: --dpi-hdr-only
    bool m_dumpDefines = false;     // main switch: --dump-defines
    bool m_dumpTreeAddrids = false; // main switch: --dump-tree-addrids
    bool m_exe = false;             // main switch: --exe
    bool m_flatten = false;         // main switch: --flatten
    bool m_hierarchical = false;    // main switch: --hierarchical
    bool m_ignc = false;            // main switch: --ignc
    bool m_lintOnly = false;        // main switch: --lint-only
    bool m_gmake = false;           // main switch: --make gmake
    bool m_main = false;            // main swithc: --main
    bool m_orderClockDly = true;    // main switch: --order-clock-delay
    bool m_outFormatOk = false;     // main switch: --cc, --sc or --sp was specified
    bool m_pedantic = false;        // main switch: --Wpedantic
    bool m_pinsScUint = false;      // main switch: --pins-sc-uint
    bool m_pinsScBigUint = false;   // main switch: --pins-sc-biguint
    bool m_pinsUint8 = false;       // main switch: --pins-uint8
    bool m_ppComments = false;      // main switch: --pp-comments
    bool m_profC = false;           // main switch: --prof-c
    bool m_profCFuncs = false;      // main switch: --prof-cfuncs
    bool m_profExec = false;        // main switch: --prof-exec
    bool m_profPgo = false;         // main switch: --prof-pgo
    bool m_protectIds = false;      // main switch: --protect-ids
    bool m_public = false;          // main switch: --public
    bool m_publicFlatRW = false;    // main switch: --public-flat-rw
    bool m_quietExit = false;       // main switch: --quiet-exit
    bool m_relativeIncludes = false; // main switch: --relative-includes
    bool m_reportUnoptflat = false; // main switch: --report-unoptflat
    bool m_savable = false;         // main switch: --savable
    bool m_structsPacked = true;    // main switch: --structs-packed
    bool m_systemC = false;         // main switch: --sc: System C instead of simple C++
    bool m_stats = false;           // main switch: --stats
    bool m_statsVars = false;       // main switch: --stats-vars
    bool m_threadsCoarsen = true;   // main switch: --threads-coarsen
    bool m_threadsDpiPure = true;   // main switch: --threads-dpi all/pure
    bool m_threadsDpiUnpure = false;  // main switch: --threads-dpi all
    bool m_trace = false;           // main switch: --trace
    bool m_traceCoverage = false;   // main switch: --trace-coverage
    bool m_traceParams = true;      // main switch: --trace-params
    bool m_traceStructs = false;    // main switch: --trace-structs
    bool m_traceUnderscore = false; // main switch: --trace-underscore
    bool m_underlineZero = false;   // main switch: --underline-zero; undocumented old Verilator 2
    bool m_verilate = true;         // main swith: --verilate
    bool m_vpi = false;             // main switch: --vpi
    bool m_xInitialEdge = false;    // main switch: --x-initial-edge
    bool m_xmlOnly = false;         // main switch: --xml-only

    int         m_buildJobs = 1;    // main switch: -j
    int         m_convergeLimit = 100;  // main switch: --converge-limit
    int         m_coverageMaxWidth = 256; // main switch: --coverage-max-width
    int         m_dumpTree = 0;     // main switch: --dump-tree
    int         m_expandLimit = 64;  // main switch: --expand-limit
    int         m_gateStmts = 100;    // main switch: --gate-stmts
    int         m_hierChild = 0;      // main switch: --hierarchical-child
    int         m_ifDepth = 0;      // main switch: --if-depth
    int         m_inlineMult = 2000;   // main switch: --inline-mult
    int         m_instrCountDpi = 200;   // main switch: --instr-count-dpi
    VOptionBool m_makeDepend;  // main switch: -MMD
    int         m_maxNumWidth = 65536;  // main switch: --max-num-width
    int         m_moduleRecursion = 100;  // main switch: --module-recursion-depth
    int         m_outputSplit = 20000;  // main switch: --output-split
    int         m_outputSplitCFuncs = -1;  // main switch: --output-split-cfuncs
    int         m_outputSplitCTrace = -1;  // main switch: --output-split-ctrace
    int         m_pinsBv = 65;       // main switch: --pins-bv
    int         m_reloopLimit = 40; // main switch: --reloop-limit
    VOptionBool m_skipIdentical;  // main switch: --skip-identical
    int         m_threads = 0;      // main switch: --threads (0 == --no-threads)
    int         m_threadsMaxMTasks = 0;  // main switch: --threads-max-mtasks
    VTimescale  m_timeDefaultPrec;  // main switch: --timescale
    VTimescale  m_timeDefaultUnit;  // main switch: --timescale
    VTimescale  m_timeOverridePrec;  // main switch: --timescale-override
    VTimescale  m_timeOverrideUnit;  // main switch: --timescale-override
    int         m_traceDepth = 0;   // main switch: --trace-depth
    TraceFormat m_traceFormat;  // main switch: --trace or --trace-fst
    int         m_traceMaxArray = 32;  // main switch: --trace-max-array
    int         m_traceMaxWidth = 256; // main switch: --trace-max-width
    int         m_traceThreads = 0; // main switch: --trace-threads
    int         m_unrollCount = 64;  // main switch: --unroll-count
    int         m_unrollStmts = 30000;  // main switch: --unroll-stmts

    int         m_compLimitBlocks = 0;  // compiler selection; number of nested blocks
    int         m_compLimitMembers = 64;  // compiler selection; number of members in struct before make anon array
    int         m_compLimitParens = 240;  // compiler selection; number of nested parens

    string      m_bin;          // main switch: --bin {binary}
    string      m_exeName;      // main switch: -o {name}
    string      m_flags;        // main switch: -f {name}
    string      m_l2Name;       // main switch: --l2name; "" for top-module's name
    string      m_libCreate;    // main switch: --lib-create {lib_name}
    string      m_makeDir;      // main switch: -Mdir
    string      m_modPrefix;    // main switch: --mod-prefix
    string      m_pipeFilter;   // main switch: --pipe-filter
    string      m_prefix;       // main switch: --prefix
    string      m_protectKey;   // main switch: --protect-key
    string      m_topModule;    // main switch: --top-module
    string      m_unusedRegexp; // main switch: --unused-regexp
    string      m_waiverOutput;  // main switch: --waiver-output {filename}
    string      m_xAssign;      // main switch: --x-assign
    string      m_xInitial;     // main switch: --x-initial
    string      m_xmlOutput;    // main switch: --xml-output

    // Language is now held in FileLine, on a per-node basis. However we still
    // have a concept of the default language at a global level.
    V3LangCode  m_defaultLanguage;      // main switch: --language

    // MEMBERS (optimizations)
    bool m_fAcycSimp;    // main switch: -fno-acyc-simp: acyclic pre-optimizations
    bool m_fAssemble;    // main switch: -fno-assemble: assign assemble
    bool m_fCase;        // main switch: -fno-case: case tree conversion
    bool m_fCombine;     // main switch: -fno-combine: common icode packing
    bool m_fConst;       // main switch: -fno-const: constant folding
    bool m_fConstBitOpTree;  // main switch: -fno-const-bit-op-tree constant bit op tree
    bool m_fDedupe;      // main switch: -fno-dedupe: logic deduplication
    bool m_fExpand;      // main switch: -fno-expand: expansion of C macros
    bool m_fGate;        // main switch: -fno-gate: gate wire elimination
    bool m_fInline;      // main switch: -fno-inline: module inlining
    bool m_fLife;        // main switch: -fno-life: variable lifetime
    bool m_fLifePost;    // main switch: -fno-life-post: delayed assignment elimination
    bool m_fLocalize;    // main switch: -fno-localize: convert temps to local variables
    bool m_fMergeCond;   // main switch: -fno-merge-cond: merge conditionals
    bool m_fMergeCondMotion = true; // main switch: -fno-merge-cond-motion: perform code motion
    bool m_fMergeConstPool = true;  // main switch: -fno-merge-const-pool
    bool m_fReloop;      // main switch: -fno-reloop: reform loops
    bool m_fReorder;     // main switch: -fno-reorder: reorder assignments in blocks
    bool m_fSplit;       // main switch: -fno-split: always assignment splitting
    bool m_fSubst;       // main switch: -fno-subst: substitute expression temp values
    bool m_fSubstConst;  // main switch: -fno-subst-const: final constant substitution
    bool m_fTable;       // main switch: -fno-table: lookup table creation
    // clang-format on

    bool m_available = false;  // Set to true at the end of option parsing

private:
    // METHODS
    void addArg(const string& arg);
    void addDefine(const string& defline, bool allowPlus);
    void addFuture(const string& flag);
    void addFuture0(const string& flag);
    void addFuture1(const string& flag);
    void addIncDirUser(const string& incdir);  // User requested
    void addIncDirFallback(const string& incdir);  // Low priority if not found otherwise
    void addParameter(const string& paramline, bool allowPlus);
    void addLangExt(const string& langext, const V3LangCode& lc);
    void addLibExtV(const string& libext);
    void optimize(int level);
    void showVersion(bool verbose);
    void coverage(bool flag) { m_coverageLine = m_coverageToggle = m_coverageUser = flag; }
    static bool suffixed(const string& sw, const char* arg);
    static string parseFileArg(const string& optdir, const string& relfilename);
    string filePathCheckOneDir(const string& modname, const string& dirname);
    static int stripOptionsForChildRun(const string& opt, bool forTop);

    // CONSTRUCTORS
    VL_UNCOPYABLE(V3Options);

public:
    V3Options();
    ~V3Options();
    void setDebugMode(int level);
    void setDebugSrcLevel(const string& srcfile, int level);
    int debugSrcLevel(const string& srcfile_path, int default_level = V3Error::debugDefault());
    void setDumpTreeLevel(const string& srcfile, int level);
    int dumpTreeLevel(const string& srcfile_path);

    // METHODS
    void addCppFile(const string& filename);
    void addCFlags(const string& filename);
    void addLdLibs(const string& filename);
    void addMakeFlags(const string& filename);
    void addLibraryFile(const string& filename);
    void addClocker(const string& signame);
    void addNoClocker(const string& signame);
    void addVFile(const string& filename);
    void addForceInc(const string& filename);
    void notify();
    bool available() const { return m_available; }

    // ACCESSORS (options)
    bool preprocOnly() const { return m_preprocOnly; }
    bool makePhony() const { return m_makePhony; }
    bool preprocNoLine() const { return m_preprocNoLine; }
    bool underlineZero() const { return m_underlineZero; }
    string bin() const { return m_bin; }
    string flags() const { return m_flags; }
    bool systemC() const { return m_systemC; }
    bool savable() const { return m_savable; }
    bool stats() const { return m_stats; }
    bool statsVars() const { return m_statsVars; }
    bool structsPacked() const { return m_structsPacked; }
    bool assertOn() const { return m_assert; }  // assertOn as __FILE__ may be defined
    bool autoflush() const { return m_autoflush; }
    bool bboxSys() const { return m_bboxSys; }
    bool bboxUnsup() const { return m_bboxUnsup; }
    bool build() const { return m_build; }
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
    bool debugEmitV() const { return m_debugEmitV; }
    bool debugExitParse() const { return m_debugExitParse; }
    bool debugExitUvm() const { return m_debugExitUvm; }
    bool debugLeak() const { return m_debugLeak; }
    bool debugNondeterminism() const { return m_debugNondeterminism; }
    bool debugPartition() const { return m_debugPartition; }
    bool debugProtect() const { return m_debugProtect; }
    bool debugSelfTest() const { return m_debugSelfTest; }
    bool decoration() const { return m_decoration; }
    bool dpiHdrOnly() const { return m_dpiHdrOnly; }
    bool dumpDefines() const { return m_dumpDefines; }
    bool exe() const { return m_exe; }
    bool flatten() const { return m_flatten; }
    bool gmake() const { return m_gmake; }
    bool threadsDpiPure() const { return m_threadsDpiPure; }
    bool threadsDpiUnpure() const { return m_threadsDpiUnpure; }
    bool threadsCoarsen() const { return m_threadsCoarsen; }
    bool trace() const { return m_trace; }
    bool traceCoverage() const { return m_traceCoverage; }
    bool traceParams() const { return m_traceParams; }
    bool traceStructs() const { return m_traceStructs; }
    bool traceUnderscore() const { return m_traceUnderscore; }
    bool main() const { return m_main; }
    bool orderClockDly() const { return m_orderClockDly; }
    bool outFormatOk() const { return m_outFormatOk; }
    bool keepTempFiles() const { return (V3Error::debugDefault() != 0); }
    bool pedantic() const { return m_pedantic; }
    bool pinsScUint() const { return m_pinsScUint; }
    bool pinsScBigUint() const { return m_pinsScBigUint; }
    bool pinsUint8() const { return m_pinsUint8; }
    bool ppComments() const { return m_ppComments; }
    bool profC() const { return m_profC; }
    bool profCFuncs() const { return m_profCFuncs; }
    bool profExec() const { return m_profExec; }
    bool profPgo() const { return m_profPgo; }
    bool usesProfiler() const { return profExec() || profPgo(); }
    bool protectIds() const { return m_protectIds; }
    bool allPublic() const { return m_public; }
    bool publicFlatRW() const { return m_publicFlatRW; }
    bool lintOnly() const { return m_lintOnly; }
    bool ignc() const { return m_ignc; }
    bool quietExit() const { return m_quietExit; }
    bool reportUnoptflat() const { return m_reportUnoptflat; }
    bool verilate() const { return m_verilate; }
    bool vpi() const { return m_vpi; }
    bool xInitialEdge() const { return m_xInitialEdge; }
    bool xmlOnly() const { return m_xmlOnly; }

    int buildJobs() const { return m_buildJobs; }
    int convergeLimit() const { return m_convergeLimit; }
    int coverageMaxWidth() const { return m_coverageMaxWidth; }
    int dumpTree() const { return m_dumpTree; }
    bool dumpTreeAddrids() const { return m_dumpTreeAddrids; }
    int expandLimit() const { return m_expandLimit; }
    int gateStmts() const { return m_gateStmts; }
    int ifDepth() const { return m_ifDepth; }
    int inlineMult() const { return m_inlineMult; }
    int instrCountDpi() const { return m_instrCountDpi; }
    VOptionBool makeDepend() const { return m_makeDepend; }
    int maxNumWidth() const { return m_maxNumWidth; }
    int moduleRecursionDepth() const { return m_moduleRecursion; }
    int outputSplit() const { return m_outputSplit; }
    int outputSplitCFuncs() const { return m_outputSplitCFuncs; }
    int outputSplitCTrace() const { return m_outputSplitCTrace; }
    int pinsBv() const { return m_pinsBv; }
    int reloopLimit() const { return m_reloopLimit; }
    VOptionBool skipIdentical() const { return m_skipIdentical; }
    int threads() const { return m_threads; }
    int threadsMaxMTasks() const { return m_threadsMaxMTasks; }
    bool mtasks() const { return (m_threads > 1); }
    VTimescale timeDefaultPrec() const { return m_timeDefaultPrec; }
    VTimescale timeDefaultUnit() const { return m_timeDefaultUnit; }
    VTimescale timeOverridePrec() const { return m_timeOverridePrec; }
    VTimescale timeOverrideUnit() const { return m_timeOverrideUnit; }
    VTimescale timeComputePrec(const VTimescale& flag) const;
    VTimescale timeComputeUnit(const VTimescale& flag) const;
    int traceDepth() const { return m_traceDepth; }
    TraceFormat traceFormat() const { return m_traceFormat; }
    int traceMaxArray() const { return m_traceMaxArray; }
    int traceMaxWidth() const { return m_traceMaxWidth; }
    int traceThreads() const { return m_traceThreads; }
    bool useTraceOffload() const { return trace() && traceFormat().fst() && traceThreads() > 1; }
    bool useTraceParallel() const {
        return trace() && traceFormat().vcd() && threads() && (threads() > 1 || hierChild() > 1);
    }
    bool useFstWriterThread() const { return traceThreads() && traceFormat().fst(); }
    unsigned vmTraceThreads() const {
        return useTraceParallel() ? threads() : useTraceOffload() ? 1 : 0;
    }
    int unrollCount() const { return m_unrollCount; }
    int unrollStmts() const { return m_unrollStmts; }

    int compLimitBlocks() const { return m_compLimitBlocks; }
    int compLimitMembers() const { return m_compLimitMembers; }
    int compLimitParens() const { return m_compLimitParens; }

    string exeName() const { return m_exeName != "" ? m_exeName : prefix(); }
    string l2Name() const { return m_l2Name; }
    string libCreate() const { return m_libCreate; }
    string libCreateName(bool shared) {
        string libName = "lib" + libCreate();
        if (shared) {
            libName += ".so";
        } else {
            libName += ".a";
        }
        return libName;
    }
    string makeDir() const { return m_makeDir; }
    string modPrefix() const { return m_modPrefix; }
    string pipeFilter() const { return m_pipeFilter; }
    string prefix() const { return m_prefix; }
    // Not just called protectKey() to avoid bugs of not using protectKeyDefaulted()
    bool protectKeyProvided() const { return !m_protectKey.empty(); }
    string protectKeyDefaulted();  // Set default key if not set by user
    string topModule() const { return m_topModule; }
    string unusedRegexp() const { return m_unusedRegexp; }
    string waiverOutput() const { return m_waiverOutput; }
    bool isWaiverOutput() const { return !m_waiverOutput.empty(); }
    string xAssign() const { return m_xAssign; }
    string xInitial() const { return m_xInitial; }
    string xmlOutput() const { return m_xmlOutput; }

    const V3StringSet& cppFiles() const { return m_cppFiles; }
    const V3StringList& cFlags() const { return m_cFlags; }
    const V3StringList& ldLibs() const { return m_ldLibs; }
    const V3StringList& makeFlags() const { return m_makeFlags; }
    const V3StringSet& libraryFiles() const { return m_libraryFiles; }
    const V3StringList& vFiles() const { return m_vFiles; }
    const V3StringList& forceIncs() const { return m_forceIncs; }

    bool hasParameter(const string& name);
    string parameter(const string& name);
    void checkParameters();

    bool isFuture(const string& flag) const;
    bool isFuture0(const string& flag) const;
    bool isFuture1(const string& flag) const;
    bool isLibraryFile(const string& filename) const;
    bool isClocker(const string& signame) const;
    bool isNoClocker(const string& signame) const;

    // ACCESSORS (optimization options)
    bool fAcycSimp() const { return m_fAcycSimp; }
    bool fAssemble() const { return m_fAssemble; }
    bool fCase() const { return m_fCase; }
    bool fCombine() const { return m_fCombine; }
    bool fConst() const { return m_fConst; }
    bool fConstBitOpTree() const { return m_fConstBitOpTree; }
    bool fDedupe() const { return m_fDedupe; }
    bool fExpand() const { return m_fExpand; }
    bool fGate() const { return m_fGate; }
    bool fInline() const { return m_fInline; }
    bool fLife() const { return m_fLife; }
    bool fLifePost() const { return m_fLifePost; }
    bool fLocalize() const { return m_fLocalize; }
    bool fMergeCond() const { return m_fMergeCond; }
    bool fMergeCondMotion() const { return m_fMergeCondMotion; }
    bool fMergeConstPool() const { return m_fMergeConstPool; }
    bool fReloop() const { return m_fReloop; }
    bool fReorder() const { return m_fReorder; }
    bool fSplit() const { return m_fSplit; }
    bool fSubst() const { return m_fSubst; }
    bool fSubstConst() const { return m_fSubstConst; }
    bool fTable() const { return m_fTable; }

    string traceClassBase() const { return m_traceFormat.classBase(); }
    string traceClassLang() const { return m_traceFormat.classBase() + (systemC() ? "Sc" : "C"); }
    string traceSourceBase() const { return m_traceFormat.sourceName(); }
    string traceSourceLang() const {
        return m_traceFormat.sourceName() + (systemC() ? "_sc" : "_c");
    }

    bool hierarchical() const { return m_hierarchical; }
    int hierChild() const { return m_hierChild; }
    bool hierTop() const { return !m_hierChild && !m_hierBlocks.empty(); }
    const V3HierBlockOptSet& hierBlocks() const { return m_hierBlocks; }
    // Directory to save .tree, .dot, .dat, .vpp for hierarchical block top
    // Returns makeDir() unless top module of hierarchical verilation.
    string hierTopDataDir() const {
        return hierTop() ? (makeDir() + '/' + prefix() + "__hier.dir") : makeDir();
    }

    // METHODS (from main)
    static string version();
    static string argString(int argc, char** argv);  ///< Return list of arguments as simple string
    string allArgsString() const;  ///< Return all passed arguments as simple string
    // Return options for child hierarchical blocks when forTop==false, otherwise returns args for
    // the top module.
    string allArgsStringForHierBlock(bool forTop) const;
    void bin(const string& flag) { m_bin = flag; }
    void parseOpts(FileLine* fl, int argc, char** argv);
    void parseOptsList(FileLine* fl, const string& optdir, int argc, char** argv);
    void parseOptsFile(FileLine* fl, const string& filename, bool rel);

    // METHODS (environment)
    // Most of these may be built into the executable with --enable-defenv,
    // see the README.  If adding new variables, also see src/Makefile_obj.in
    // Also add to V3Options::showVersion()
    static string getenvBuiltins(const string& var);
    static string getenvMAKE();
    static string getenvPERL();
    static string getenvSYSTEMC();
    static string getenvSYSTEMC_ARCH();
    static string getenvSYSTEMC_INCLUDE();
    static string getenvSYSTEMC_LIBDIR();
    static string getenvVERILATOR_ROOT();
    static bool systemCSystemWide();
    static bool systemCFound();  // SystemC installed, or environment points to it

    // METHODS (file utilities using these options)
    string fileExists(const string& filename);
    string filePath(FileLine* fl, const string& modname, const string& lastpath,
                    const string& errmsg);
    void filePathLookedMsg(FileLine* fl, const string& modname);
    V3LangCode fileLanguage(const string& filename);
    static bool fileStatNormal(const string& filename);
    static void fileNfsFlush(const string& filename);

    // METHODS (other OS)
    static void throwSigsegv();
};

//######################################################################

#endif  // guard
