// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Common headers
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
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
#include <type_traits>
#include <unordered_map>
#include <unordered_set>

class AstNetlist;
class V3HierGraph;
class V3LibMap;
class V3ThreadPool;

//======================================================================
// Restorer

// For all flavours, 'var' must be a named scalar variable (simple identifier).

// Copy given variable's value on the stack, copy saved value back at end-of-scope.
// Only usable for trivially copyable types; use VL_RESTORER_COPY/VL_RESTORER_CLEAR for
// non-trivially copyable types, which are more efficient.
#define VL_RESTORER(var) \
    const VRestorerTrivial<typename std::decay_t<decltype(var)>> restorer_##var(var);

// This is the equivalent of VL_RESTORER for non-trivially copyable types. Still more efficient
// than VL_RESTORER as uses move to restore.
#define VL_RESTORER_COPY(var) \
    const VRestorerCopy<typename std::decay_t<decltype(var)>> restorer_##var(var);

// Swap 'var' with a no-args constructed object of the same type, effectively clearing it, then
// swap back at end-of-scope. No copying involved. Use this e.g. for std containers where they
// would be .clear()'d right after the VL_RESTORER instance.
#define VL_RESTORER_CLEAR(var) \
    const VRestorerClear<typename std::decay_t<decltype(var)>> restorer_##var(var);

// Get const reference to the saved copy
#define VL_RESTORER_PREV(var) restorer_##var.saved()

// Implementation of VL_RESTORER
template <typename T>
class VRestorerTrivial final {
    static_assert(std::is_trivially_copyable<T>::value,
                  "Use VL_RESTORER_{COPY,CLEAR} for non trivially copyable types");
    T& m_ref;  // Reference to object we're saving and restoring
    const T m_saved;  // Value saved, for later restore

public:
    explicit VRestorerTrivial(T& val)
        : m_ref{val}
        , m_saved{val} {}
    ~VRestorerTrivial() { m_ref = m_saved; }
    VL_UNCOPYABLE(VRestorerTrivial);
    // Must be stack allocated
    void* operator new(size_t) = delete;
    void operator delete(void*) = delete;

    const T& saved() const { return m_saved; }
};

// Implementation of VL_RESTORER_COPY
template <typename T>
class VRestorerCopy final {
    static_assert(!std::is_trivially_copyable<T>::value,
                  "Use VL_RESTORER for trivially copyable types");
    T& m_ref;  // Reference to object we're saving and restoring
    T m_saved;  // Value saved, for later restore

public:
    explicit VRestorerCopy(T& val)
        : m_ref{val}
        , m_saved{val} {}
    ~VRestorerCopy() { m_ref = std::move(m_saved); }
    VL_UNCOPYABLE(VRestorerCopy);
    // Must be stack allocated
    void* operator new(size_t) = delete;
    void operator delete(void*) = delete;

    const T& saved() const { return m_saved; }
};

// Implementation of VL_RESTORER_CLEAR.
template <typename T>
class VRestorerClear final {
    static_assert(!std::is_trivially_copyable<T>::value,
                  "Use VL_RESTORER for trivially copyable types");
    T& m_ref;  // Reference to object we're saving and restoring
    T m_saved{};  // Owns the swapped-out value; starts empty

public:
    explicit VRestorerClear(T& val)
        : m_ref{val} {
        std::swap(m_ref, m_saved);
    }
    ~VRestorerClear() { std::swap(m_ref, m_saved); }
    VL_UNCOPYABLE(VRestorerClear);
    // Must be stack allocated
    void* operator new(size_t) = delete;
    void operator delete(void*) = delete;

    const T& saved() const { return m_saved; }
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
    bool m_usesForce = false;  // Design uses force/release statements
    bool m_usesZeroDelay = false;  // Design uses #0 delay (or non-constant delay)
    bool m_hasForceableSignals = false;  // Need to apply V3Force pass
    bool m_hasAssignDeassign = false;  // Need to apply V3Force pass for assign/deassign statements
    bool m_hasSystemCSections = false;  // Has AstSystemCSection that need to be emitted
    bool m_useParallelBuild = false;  // Use parallel build for model
    bool m_useRandSequence = false;  // Has `randsequence`
    bool m_useCovergroup = false;  // Has covergroup declarations
    bool m_useRandomizeMethods = false;  // Need to define randomize() class methods
    bool m_hasPrintedObjects = false;  // Design has format args printed with to_string()
    uint64_t m_currentHierBlockCost = 0;  // Total cost of this hier block, used for scheduling
    bool m_currentHierBlockEvalMayFinish = true;  // Hier block eval entry may execute $finish
    bool m_currentHierBlockFinalMayFinish = true;  // Hier block final entry may execute $finish

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
    V3Global() = default;
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
    static void dumpCheckGlobalTree(const string& stagename, int newNumber = 0, bool doDump = true,
                                    bool doCheck = true);
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
    bool usesZeroDelay() const { return m_usesZeroDelay; }
    void setUsesZeroDelay() { m_usesZeroDelay = true; }
    bool hasForceableSignals() const { return m_hasForceableSignals; }
    void setHasForceableSignals() { m_hasForceableSignals = true; }
    bool hasAssignDeassign() const { return m_hasAssignDeassign; }
    void setHasAssignDeassign() { m_hasAssignDeassign = true; }
    bool usesForce() const { return m_usesForce; }
    void setUsesForce() { m_usesForce = true; }
    bool hasSystemCSections() const VL_MT_SAFE { return m_hasSystemCSections; }
    void setHasSystemCSections() { m_hasSystemCSections = true; }
    V3HierGraph* hierGraphp() const { return m_hierGraphp; }
    void hierGraphp(V3HierGraph* graphp) { m_hierGraphp = graphp; }
    bool useParallelBuild() const { return m_useParallelBuild; }
    void useParallelBuild(bool flag) { m_useParallelBuild = flag; }
    bool useRandSequence() const { return m_useRandSequence; }
    void useRandSequence(bool flag) { m_useRandSequence = flag; }
    bool useCovergroup() const { return m_useCovergroup; }
    void useCovergroup(bool flag) { m_useCovergroup = flag; }
    bool useRandomizeMethods() const { return m_useRandomizeMethods; }
    void useRandomizeMethods(bool flag) { m_useRandomizeMethods = flag; }
    bool hasPrintedObjects() const { return m_hasPrintedObjects; }
    void hasPrintedObjects(bool flag) { m_hasPrintedObjects = flag; }
    void saveJsonPtrFieldName(const std::string& fieldName);
    void ptrNamesDumpJson(std::ostream& os);
    void idPtrMapDumpJson(std::ostream& os);
    const std::string& ptrToId(const void* p);
    std::thread::id mainThreadId() const { return m_mainThreadId; }
    static std::vector<std::string> verilatedCppFiles();
    uint64_t currentHierBlockCost() const { return m_currentHierBlockCost; }
    void currentHierBlockCost(uint64_t cost) { m_currentHierBlockCost = cost; }
    bool currentHierBlockEvalMayFinish() const { return m_currentHierBlockEvalMayFinish; }
    void currentHierBlockEvalMayFinish(bool flag) { m_currentHierBlockEvalMayFinish = flag; }
    bool currentHierBlockFinalMayFinish() const { return m_currentHierBlockFinalMayFinish; }
    void currentHierBlockFinalMayFinish(bool flag) { m_currentHierBlockFinalMayFinish = flag; }
};

extern V3Global v3Global;

//######################################################################

#endif  // guard
