// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Common headers
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3GLOBAL_H_
#define VERILATOR_V3GLOBAL_H_

// clang-format off
#include "config_build.h"
#ifndef HAVE_CONFIG_PACKAGE
# error "Something failed during ./configure as config_package.h is incomplete. Perhaps you used autoreconf, don't."
#endif
// clang-format on

#include "verilatedos.h"

#include "V3Error.h"
#include "V3FileLine.h"
#include "V3Mutex.h"
#include "V3Options.h"

#include <string>
#include <thread>
#include <unordered_map>
#include <unordered_set>

class AstNetlist;
class V3HierGraph;
class V3LibMap;
class V3ThreadPool;

//======================================================================
// Restorer

/// Save a given variable's value on the stack, restoring it at end-of-scope.
// Object must be named, or it will not persist until end-of-scope.
// Constructor needs () or GCC 4.8 false warning.
#define VL_RESTORER(var) const VRestorer<typename std::decay_t<decltype(var)>> restorer_##var(var);
/// Get the copy of the variable previously saved by VL_RESTORER()
#define VL_RESTORER_PREV(var) restorer_##var.saved()

// Object used by VL_RESTORER.  This object must be an auto variable, not
// allocated on the heap or otherwise.
template <typename T>
class VRestorer final {
    T& m_ref;  // Reference to object we're saving and restoring
    const T m_saved;  // Value saved, for later restore

public:
    explicit VRestorer(T& permr)
        : m_ref{permr}
        , m_saved{permr} {}
    ~VRestorer() { m_ref = m_saved; }
    const T& saved() const { return m_saved; }
    VL_UNCOPYABLE(VRestorer);
};

//######################################################################

class VWidthMinUsage final {
public:
    enum en : uint8_t { LINT_WIDTH, MATCHES_WIDTH, VERILOG_WIDTH };
    enum en m_e;
    VWidthMinUsage()
        : m_e{LINT_WIDTH} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr VWidthMinUsage(en _e) VL_PURE : m_e{_e} {}
    constexpr VWidthMinUsage(const VWidthMinUsage& _e) VL_PURE = default;
    explicit VWidthMinUsage(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    constexpr operator en() const { return m_e; }
    constexpr VWidthMinUsage& operator=(const VWidthMinUsage& _e) VL_PURE = default;
};
constexpr bool operator==(const VWidthMinUsage& lhs, const VWidthMinUsage& rhs) {
    return lhs.m_e == rhs.m_e;
}
constexpr bool operator==(const VWidthMinUsage& lhs, VWidthMinUsage::en rhs) VL_PURE {
    return lhs.m_e == rhs;
}
constexpr bool operator==(VWidthMinUsage::en lhs, const VWidthMinUsage& rhs) {
    return lhs == rhs.m_e;
}

//######################################################################
// V3Global - The top level class for the entire program

class V3Global final {
    // Globals
    // Root of entire netlist, created by makeInitNetlist(} so static constructors run first
    AstNetlist* m_rootp = nullptr;
    // Hierarchical block graph (plan) iff hierarchical verilation is performed
    V3HierGraph* m_hierGraphp = nullptr;
    // Thread Pool, nullptr unless 'verilatedJobs' is known, set via threadPoolp(V3ThreadPool*)
    V3ThreadPool* m_threadPoolp = nullptr;
    // Library Mapping, nullptr unless --libmap is used
    V3LibMap* m_libMapp = nullptr;
    VWidthMinUsage m_widthMinUsage
        = VWidthMinUsage::LINT_WIDTH;  // What AstNode::widthMin() is used for

    std::atomic_int m_debugFileNumber{0};  // Number to append to debug files created
    bool m_assertDTypesResolved = false;  // Tree should have dtypep()'s
    bool m_assertScoped = false;  // Tree is scoped
    bool m_assignsEvents = false;  // Design uses assignments on SystemVerilog Events
    bool m_constRemoveXs = false;  // Const needs to strip any Xs
    // Experimenting with always requiring heavy, see issue #2701
    bool m_needTraceDumper = false;  // Need __Vm_dumperp in symbols
    bool m_dpi = false;  // Need __Dpi include files
    bool m_hasEvents = false;  // Design uses SystemVerilog named events
    bool m_hasClasses = false;  // Design uses SystemVerilog classes
    bool m_hasSampled = false;  // Design uses SAMPLED expresions
    bool m_hasTable = false;  // Desgin has the UDP Table.
    bool m_hasVirtIfaces = false;  // Design uses virtual interfaces
    bool m_usesProbDist = false;  // Uses $dist_*
    bool m_usesStdPackage = false;  // Design uses the std package
    bool m_usesTiming = false;  // Design uses timing constructs
    bool m_hasForceableSignals = false;  // Need to apply V3Force pass
    bool m_hasSystemCSections = false;  // Has AstSystemCSection that need to be emitted
    bool m_useParallelBuild = false;  // Use parallel build for model
    bool m_useRandSequence = false;  // Has `randsequence`
    bool m_useRandomizeMethods = false;  // Need to define randomize() class methods
    uint64_t m_currentHierBlockCost = 0;  // Total cost of this hier block, used for scheduling

    // Memory address to short string mapping (for debug)
    std::unordered_map<const void*, std::string>
        m_ptrToId;  // The actual 'address' <=> 'short string' bijection

    // Names of fields that were dumped by dumpJsonPtr()
    std::unordered_set<std::string> m_jsonPtrNames;

    // Id of the main thread
    const std::thread::id m_mainThreadId = std::this_thread::get_id();

public:
    // Options
    V3Options opt;  // All options; let user see them directly

    // CONSTRUCTORS
    V3Global() {}
    void boot();
    void shutdown();  // Release allocated resources

    void vlExit(int status);

    // ACCESSORS (general)
    AstNetlist* rootp() const VL_MT_SAFE { return m_rootp; }
    V3LibMap* libMapp() const VL_PURE { return m_libMapp; }
    V3ThreadPool* threadPoolp() const VL_PURE { return m_threadPoolp; }
    void threadPoolp(V3ThreadPool* threadPoolp) {
        UASSERT(!m_threadPoolp, "attempted to create multiple threadPool singletons");
        m_threadPoolp = threadPoolp;
    }
    VWidthMinUsage widthMinUsage() const VL_PURE { return m_widthMinUsage; }
    bool assertDTypesResolved() const { return m_assertDTypesResolved; }
    bool assertScoped() const { return m_assertScoped; }

    // METHODS
    void readFiles() VL_MT_DISABLED;
    void removeStd() VL_MT_DISABLED;
    void checkTree() const;
    static void dumpCheckGlobalTree(const string& stagename, int newNumber = 0,
                                    bool doDump = true);
    void assertDTypesResolved(bool flag) { m_assertDTypesResolved = flag; }
    void assertScoped(bool flag) { m_assertScoped = flag; }
    void widthMinUsage(const VWidthMinUsage& flag) { m_widthMinUsage = flag; }
    bool constRemoveXs() const { return m_constRemoveXs; }
    void constRemoveXs(bool flag) { m_constRemoveXs = flag; }
    string debugFilename(const string& nameComment, int newNumber = 0);
    static string digitsFilename(int number);
    bool needTraceDumper() const { return m_needTraceDumper; }
    void needTraceDumper(bool flag) { m_needTraceDumper = flag; }
    bool dpi() const VL_MT_SAFE { return m_dpi; }
    void dpi(bool flag) { m_dpi = flag; }
    bool assignsEvents() const { return m_assignsEvents; }
    void setAssignsEvents() { m_assignsEvents = true; }
    bool hasEvents() const { return m_hasEvents; }
    void setHasEvents() { m_hasEvents = true; }
    bool hasClasses() const { return m_hasClasses; }
    void setHasClasses() { m_hasClasses = true; }
    bool hasSampled() const { return m_hasSampled; }
    void setHasSampled() { m_hasSampled = true; }
    bool hasTable() const { return m_hasTable; }
    void setHasTable() { m_hasTable = true; }
    bool hasVirtIfaces() const { return m_hasVirtIfaces; }
    void setHasVirtIfaces() { m_hasVirtIfaces = true; }
    bool usesProbDist() const { return m_usesProbDist; }
    void setUsesProbDist() { m_usesProbDist = true; }
    bool usesStdPackage() const { return m_usesStdPackage; }
    void setUsesStdPackage() { m_usesStdPackage = true; }
    bool usesTiming() const { return m_usesTiming; }
    void setUsesTiming() { m_usesTiming = true; }
    bool hasForceableSignals() const { return m_hasForceableSignals; }
    void setHasForceableSignals() { m_hasForceableSignals = true; }
    bool hasSystemCSections() const VL_MT_SAFE { return m_hasSystemCSections; }
    void setHasSystemCSections() { m_hasSystemCSections = true; }
    V3HierGraph* hierGraphp() const { return m_hierGraphp; }
    void hierGraphp(V3HierGraph* graphp) { m_hierGraphp = graphp; }
    bool useParallelBuild() const { return m_useParallelBuild; }
    void useParallelBuild(bool flag) { m_useParallelBuild = flag; }
    bool useRandSequence() const { return m_useRandSequence; }
    void useRandSequence(bool flag) { m_useRandSequence = flag; }
    bool useRandomizeMethods() const { return m_useRandomizeMethods; }
    void useRandomizeMethods(bool flag) { m_useRandomizeMethods = flag; }
    void saveJsonPtrFieldName(const std::string& fieldName);
    void ptrNamesDumpJson(std::ostream& os);
    void idPtrMapDumpJson(std::ostream& os);
    const std::string& ptrToId(const void* p);
    std::thread::id mainThreadId() const { return m_mainThreadId; }
    static std::vector<std::string> verilatedCppFiles();
    uint64_t currentHierBlockCost() const { return m_currentHierBlockCost; }
    void currentHierBlockCost(uint64_t cost) { m_currentHierBlockCost = cost; }
};

extern V3Global v3Global;

//######################################################################

#endif  // guard
