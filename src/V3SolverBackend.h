// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Interface between randomize() lowering and constraint solvers
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
// V3Randomize is split into a solver-neutral front end (V3Randomize.cpp) and
// a constraint solver back-end. See V3SolverBackend.cpp for the contract
// between them.
//
//*************************************************************************

#ifndef VERILATOR_V3SOLVERBACKEND_H_
#define VERILATOR_V3SOLVERBACKEND_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"

#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

class V3UniqueNames;
class VMemberMap;

//######################################################################
// Definitions shared by the randomize front end and the back-ends

// Separates the levels of the name of a global constraint flattened into a class
static constexpr const char* GLOBAL_CONSTRAINT_SEPARATOR = "__DT__";

// ######################################################################
// Stores info about a variable's rand_mode state/a constraint's constraint_mode state

union RandomizeMode final {
    // MEMBERS
    struct {
        bool usesMode : 1;  // Variable/constraint uses rand_mode/constraint_mode
        uint32_t index : 31;  // Index of var/constraint in rand_mode/constraint_mode vector
    };
    uint64_t asUQuad;  // Representation as int to be stored in nodep->user*
};

// The rand_mode/constraint_mode state arrays created by the front end
class RandModeVars final {
    // MEMBERS
    // Static constraint_mode array per root class
    std::unordered_map<AstClass*, AstVar*> m_staticConstraintModeVars;
    // Static rand_mode array per root class
    std::unordered_map<AstClass*, AstVar*> m_staticRandModeVars;

public:
    // METHODS
    void addStaticConstraintModeVar(AstClass* classp, AstVar* varp) {
        m_staticConstraintModeVars.emplace(classp, varp);
    }
    void addStaticRandModeVar(AstClass* classp, AstVar* varp) {
        m_staticRandModeVars.emplace(classp, varp);
    }
    // Static constraint_mode array of classp, or of its nearest base class with one
    AstVar* staticConstraintModeVarp(AstClass* classp) const VL_MT_DISABLED;
    // Static rand_mode array of classp, or of its nearest base class with one
    AstVar* staticRandModeVarp(AstClass* classp) const VL_MT_DISABLED;
    // Per-instance constraint_mode array (AstClass::user4p) of classp or its nearest base
    static AstVar* constraintModeVarp(AstClass* classp) VL_MT_DISABLED;
    // Per-instance rand_mode array (__Vrandmode, AstNodeModule::user2p) of classp or its
    // nearest base. user2p is only set on the root class where __Vrandmode was created.
    static AstVar* randModeVarp(AstNodeModule* classp) VL_MT_DISABLED;
    // Guard stmtp by the mode bit, if the variable/constraint uses one
    static AstNodeStmt* wrapIfMode(const RandomizeMode mode, AstVar* modeVarp,
                                   AstNodeStmt* stmtp) VL_MT_DISABLED;
};

//######################################################################
// Lowering of the randomize sites of one V3Randomize pass, created by
// V3SolverBackend::newLowering()

class V3SolverLowering VL_NOT_FINAL {
protected:
    // MEMBERS, shared with the front end for one V3Randomize pass
    VMemberMap& m_memberMap;  // Member names cached for fast lookup
    V3UniqueNames& m_uniqueNames;  // Unique names of temporaries, and of blocks holding them
    const RandModeVars& m_modeVars;  // rand_mode/constraint_mode state arrays
    VNDeleter& m_deleter;  // Deferred deletion of nodes removed by the back-end

    // CONSTRUCTORS
    V3SolverLowering(VMemberMap& memberMap, V3UniqueNames& uniqueNames,
                     const RandModeVars& modeVars, VNDeleter& deleter)
        : m_memberMap{memberMap}
        , m_uniqueNames{uniqueNames}
        , m_modeVars{modeVars}
        , m_deleter{deleter} {}

    // METHODS
    void pushDeletep(AstNode* nodep) { m_deleter.pushDeletep(nodep); }

public:
    virtual ~V3SolverLowering() = default;

    // Per class. prepareClass() is called before any class is lowered, for each
    // class that has constraint blocks, declared or inherited.
    virtual void prepareClass(AstClass* classp) = 0;
    // Called when the front end starts lowering classp, and again when it
    // resumes classp after lowering another class (that of a rand member)
    virtual void startClass(AstClass* classp) = 0;
    // Called, as the front end walks the class, for each method call in a
    // constraint block of modp, e.g. to rewrite '.size()' in place
    virtual void lowerConstraintMethod(AstNodeModule* modp, AstConstraint* constrp,
                                       AstCMethodHard* nodep)
        = 0;

    // Per site
    // Class randomize(): add the solver setup to randomizep, and return the
    // solver result (also when the class has no constraints)
    virtual AstNodeExpr* lowerClassRandomize(AstClass* classp, AstFunc* randomizep,
                                             AstVar* randModeVarp)
        = 0;
    // Class randomize(): add statements that must follow the solver result,
    // after the front end has emitted the assignment that evaluates it
    virtual void addAfterClassSolve(AstClass* classp, AstFunc* randomizep) = 0;
    // randomize() with {...} called by nodep: lower the captured constraints
    // into randomizeFuncp, and assign its return value from the solver result
    // and basicRandomizeCallp (__VBasicRand()). thisVarp is the captured
    // 'this' of the caller.
    virtual void lowerInlineRandomize(AstNodeFTaskRef* nodep, AstClass* classp,
                                      AstFunc* randomizeFuncp, AstNode* capturedTreep,
                                      const AstVar* thisVarp, AstNodeExpr* basicRandomizeCallp)
        = 0;
    // std::randomize() with {...} called by nodep: lower the captured
    // constraints into randomizeFuncp, and return the solver result. stdrandp
    // is the module's std::randomize generator.
    virtual AstNodeExpr* lowerStdRandomizeWith(AstNodeFTaskRef* nodep, AstFunc* randomizeFuncp,
                                               AstNode* capturedTreep, AstVar* stdrandp)
        = 0;
    // randomize(null): add the constraint check to funcp, and return its result
    virtual AstNodeExpr* lowerCheckOnly(AstClass* classp, AstFunc* funcp) = 0;
};

//######################################################################
// Constraint solver back-end selected for the run, see V3Global::solverBackendp()

class V3SolverBackend VL_NOT_FINAL {
public:
    virtual ~V3SolverBackend() = default;

    // Header of the runtime library, included by the generated code
    virtual std::string runtimeHeader() const VL_MT_DISABLED = 0;
    // Runtime C++ files compiled with the model
    virtual std::vector<std::string> runtimeCppFiles() const VL_MT_DISABLED = 0;
    // Flags for VM_USER_CFLAGS of the generated makefile, from the environment
    virtual std::vector<std::string> runtimeCFlags() const VL_MT_DISABLED = 0;

    // Lowering for one V3Randomize pass, sharing the given state with the front end
    virtual std::unique_ptr<V3SolverLowering>
    newLowering(VMemberMap& memberMap, V3UniqueNames& uniqueNames, const RandModeVars& modeVars,
                VNDeleter& deleter) const VL_MT_DISABLED
        = 0;
};

#endif  // Guard
