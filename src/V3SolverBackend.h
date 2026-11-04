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
// a constraint solver back-end, selected per run by V3SolverBackend::create().
//
// The front end owns pre/post_randomize callbacks, rand_mode/constraint_mode
// state, __VBasicRand (randomization of unconstrained variables), argument
// handling and the capture of inline 'with' expressions. A back-end owns
// everything emitted to solve the constraints of a randomize site: a class
// randomize(), a randomize() with {...}, a std::randomize() with {...} and a
// randomize(null). Each site is lowered by a single hook, which the front end
// calls at a fixed point of its own lowering.
//
// Contract between the front end and a back-end:
//  * Input: the AST marked by RandomizeMarkVisitor (AstNodeExpr::user1() set
//    on expressions depending on a randomized variable), the constraint blocks
//    of the class, the rand_mode/constraint_mode state (RandomizeMode in
//    user1() of the variables and constraints, the mode arrays in
//    RandModeVars), and, for inline sites, the captured 'with' items.
//  * Variable ownership: __VBasicRand skips variables with AstVar::user3()
//    set. The front end sets it on variables named in a class's own
//    constraints; a back-end sets it on any other variable it assigns, before
//    the front end emits __VBasicRand for the class.
//  * Output: a site hook either returns the solver result for the front end
//    to combine with __VBasicRand, or for inline sites, where the order of
//    __VBasicRand against the solver call matters, assigns the function's
//    return value itself. All other statements go into the given function,
//    or into members the back-end creates.
//  * Constraint items are consumed: the front end deletes every AstConstraint
//    once all sites are lowered, so a back-end may unlink or rewrite items.
//  * A back-end runs within the V3Randomize pass, and may use the AstNode
//    user fields that pass documents.
//
//*************************************************************************

#ifndef VERILATOR_V3SOLVERBACKEND_H_
#define VERILATOR_V3SOLVERBACKEND_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"

#include <map>
#include <memory>
#include <string>
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
struct RandModeVars final {
    std::map<AstClass*, AstVar*> staticConstraintModeVars;  // Static constraint mode vars
    std::map<AstClass*, AstVar*> staticRandModeVars;  // Static rand mode vars per class

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
    static AstNode* wrapIfMode(const RandomizeMode mode, AstVar* modeVarp,
                               AstNode* stmtp) VL_MT_DISABLED;
};

//######################################################################
// Runtime library needed by the code a back-end generates

struct V3SolverRuntime final {
    std::string header;  // Header included by the generated code
    std::vector<std::string> sources;  // Runtime sources compiled with the model
};

//######################################################################
// Constraint solver back-end

class V3SolverBackend VL_NOT_FINAL {
protected:
    // MEMBERS, shared with the front end for one V3Randomize pass
    VMemberMap& m_memberMap;  // Member names cached for fast lookup
    V3UniqueNames& m_uniqueNames;  // Unique names of temporaries, and of blocks holding them
    const RandModeVars& m_modeVars;  // rand_mode/constraint_mode state arrays
    VNDeleter& m_deleter;  // Deferred deletion of nodes removed by the back-end

    // CONSTRUCTORS
    V3SolverBackend(VMemberMap& memberMap, V3UniqueNames& uniqueNames,
                    const RandModeVars& modeVars, VNDeleter& deleter)
        : m_memberMap{memberMap}
        , m_uniqueNames{uniqueNames}
        , m_modeVars{modeVars}
        , m_deleter{deleter} {}

    // METHODS
    void pushDeletep(AstNode* nodep) { m_deleter.pushDeletep(nodep); }

public:
    // Back-end selected for this run, for one V3Randomize pass
    static std::unique_ptr<V3SolverBackend> create(VMemberMap& memberMap,
                                                   V3UniqueNames& uniqueNames,
                                                   const RandModeVars& modeVars,
                                                   VNDeleter& deleter) VL_MT_DISABLED;
    // Runtime library of the back-end selected for this run
    static V3SolverRuntime runtime() VL_MT_DISABLED;
    // Flags for VM_USER_CFLAGS of the generated makefile, from the environment
    static std::vector<std::string> runtimeCFlags() VL_MT_DISABLED;

    virtual ~V3SolverBackend() = default;

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

#endif  // Guard
