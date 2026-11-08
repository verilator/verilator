// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: SMT-LIB constraint solver back-end
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
// V3SolverSmt's Transformations:
//
// Implements V3SolverBackend for solvers driven through SMT-LIB2 text by the
// VlRandomizer runtime (include/verilated_random.h), e.g. z3 or cvc5.
//
// Each class with constraints:
//      * gets a VlRandomizer member ('constraint'), set up in new()
//      * each constraint block becomes a <name>_setup_constraint task, which
//        registers variables (write_var) and adds SMT-LIB expressions (hard,
//        soft) built by ConstraintExprVisitor; __Vsetup_constraints calls them
//        in priority order (deepest-nested global constraints first)
//      * randomize() clears, re-runs the setup and calls the solver; arrays
//        with constrained sizes take a two-phase solve (sizes, then elements)
// Each randomize() with {...} and std::randomize() with {...}:
//      * lowers its constraints into a local VlRandomizer, derived from the
//        class one for randomize() with {...}
//
// Runs within the V3Randomize pass, and uses the AstNode user fields it
// documents; those owned by this back-end are:
//  AstVar::user3()         -> bool. Handled in constraints (shared with front end)
//  AstClass::user3p()      -> AstVar*.  Constrained randomizer variable
//  AstConstraint::user2p() -> AstTask*. Pointer to constraint setup procedure
//  AstConstraint::user3p() -> AstTask*. Pointer to resize procedure
//  AstConstraintForeach::user3p() -> AstNodeStmt*. Dist bucket preamble stmts (foreach case)
//  AstVar::user4p()        -> AstVar*.  Size variable for constrained queues
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "verilatedos.h"

#include "V3SolverSmt.h"

#include "V3Const.h"
#include "V3File.h"
#include "V3MemberMap.h"
#include "V3Randomize.h"
#include "V3Task.h"
#include "V3UniqueNames.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Helpers shared by the lowering visitors

class SmtUtil final {
public:
    // Walk up the extends chain from classp to find the nearest ancestor (starting
    // with classp itself) that has its own persistent VlRandomizer generator
    // variable (stored in AstClass::user3p()). That is normally classp itself, or
    // otherwise the base-most class, since createRandomGenerator() only creates
    // one on a class that owns class-level constraints; a purely-derived class
    // with no constraints of its own has no user3p() and defers to its base.
    static AstVar* getRandomGenerator(AstClass* const classp) {
        if (classp->user3p()) return VN_AS(classp->user3p(), Var);
        if (classp->extendsp()) return getRandomGenerator(classp->extendsp()->classp());
        return nullptr;
    }

    // Create __Vsetup_constraints function if non existant inside memberMap,
    // if existant return one already present
    static AstTask* getCreateConstraintSetupFunc(AstClass* classp, VMemberMap& memberMap) {
        static const char* const name = "__Vsetup_constraints";
        AstTask* setupAllTaskp = VN_AS(memberMap.findMember(classp, name), Task);
        if (setupAllTaskp) return setupAllTaskp;
        setupAllTaskp = new AstTask{classp->fileline(), "__Vsetup_constraints"};
        setupAllTaskp->classMethod(true);
        setupAllTaskp->isVirtual(true);
        classp->addMembersp(setupAllTaskp);
        memberMap.insert(classp, setupAllTaskp);
        return setupAllTaskp;
    }

    // Look through unpacked array dimensions to the element type
    static AstNodeDType* arrayElementDTypep(AstNodeDType* dtypep) {
        dtypep = dtypep->skipRefp();
        while (dtypep->isNonPackedArray()) dtypep = dtypep->subDTypep()->skipRefp();
        return dtypep;
    }

    // Whether dtypep is, or contains anywhere through unpacked array/struct
    // nesting, a real value. A packed struct can't hold one (IEEE disallows
    // real as a packed-struct member), so it's never worth descending into.
    static bool dtypeContainsReal(AstNodeDType* dtypep) {
        dtypep = dtypep->skipRefp();
        if (AstNodeDType* const subp = dtypep->subDTypep()) return dtypeContainsReal(subp);
        if (const AstNodeUOrStructDType* const structp = VN_CAST(dtypep, NodeUOrStructDType)) {
            if (structp->packed()) return false;
            for (AstMemberDType* const memberp : structp->memberspList()) {
                if (dtypeContainsReal(memberp->subDTypep())) return true;
            }
            return false;
        }
        const AstBasicDType* const basicp = VN_CAST(dtypep, BasicDType);
        return basicp && basicp->isDouble();
    }
};

//######################################################################
// Visitor that turns constraints into template strings for solvers

class ConstraintExprVisitor final : public VNVisitor {
    // NODE STATE
    // AstVar::user3() -> bool. Handled in constraints
    // AstNodeExpr::user1()    -> bool. Depending on a randomized variable
    // AstMemberSel::user2p()  -> AstNodeModule*. Pointer to containing module
    // VNuser3InUse m_inuser3; (Allocated for use in RandomizeVisitor)

    AstClass* const m_classp;  // Class being processed
    AstBegin* const m_inlineInitBlockp;  // Block to add write_var calls to
                                         // (may be null, then new() is used)
    AstNodeFTask* const m_memberselInitTaskp;  // Fallback for membersel write_var when
                                               // classp has no randomize() (inherited members)
    AstVar* const m_genp;  // VlRandomizer variable of the class
    AstVar* m_randModeVarp;  // Relevant randmode state variable
    bool m_wantSingle = false;  // Whether to merge constraint expressions with LOGAND
    VMemberMap& m_memberMap;  // Member names cached for fast lookup
    bool m_structSel = false;  // Marks when inside structSel
                               // (used to format "%s.%s" for struct arrays and nested structs)
    bool m_deferRandModeHoist = false;  // Wait for the complete struct member path
    std::set<std::string>& m_writtenVars;  // Track which variable paths have write_var generated
                                           // (shared across all constraints)
    std::set<std::string> m_inlineWrittenVars;  // Per-instance tracking for inline constraints
    VInsertionSet<AstVar*>* m_sizeConstrainedArraysp = nullptr;  // Arrays with size constraints
    AstNodeExpr* m_conditionp = nullptr;  // Condition under which current expression is defined
                                          // (nullptr == always defined)
    AstNodeFTask* m_prepareConstrainedArraysp = nullptr;  // Grow arrays for indexed struct access
    uint32_t* m_uniqueConstraintIdp = nullptr;  // Current ID of unique call
    V3UniqueNames& m_uniqueNames;  // Unique names of temporaries, and of blocks holding them
    std::vector<AstVar*> m_rangeConstrainedEnums;  // Enums that are already range-constrained
    // First expression found under an inside index
    AstNode* m_firstExpressionInsideIndexp = nullptr;
    AstConstraintForeach* m_foreachp = nullptr;  // Innermost constraint-foreach being processed
    std::set<const AstVar*> m_foreachIdxVars;  // Index vars of all enclosing constraint-foreaches
    // Solver variables named by constraints folded into a single expression (m_wantSingle)
    // by a top-level if; empty except between that fold and m_foldTakerp taking them over
    std::set<std::string> m_constraintVars;
    // Constraint replacing the top-level if whose folded names m_constraintVars holds
    const AstConstraintExpr* m_foldTakerp = nullptr;
    // Where the variable references being lowered record their solver names. Set by
    // visit(AstConstraintExpr*), the only visit reaching a variable reference: the other
    // constraint items either move their expressions into one or never iterate them.
    std::set<std::string>* m_constraintVarsp = nullptr;

    class NestedAccessPath final {
        AstMemberSel* m_topNestedArrayMemberSelp
            = nullptr;  // Top node of nested array/member access
        AstSFormatF* m_nestedNameFormatTopp = nullptr;  // Top node of variable's name format
        AstSFormatF* m_nestedNameFormatp = nullptr;  // Last node of variable's name format
        AstNode** m_firstExpressionInsideIndexPointerp
            = nullptr;  // First expression with no name, used for "Multiple expressions inside
                        // indices of complex expression in constraint" error

        std::string m_smtName;  // string name for shouldWriteVar checking

    public:
        void addVarNamePart(AstSFormatF* const nodep, std::string&& name) {
            if (!m_nestedNameFormatp) {
                m_nestedNameFormatTopp = nodep;
                m_nestedNameFormatp = m_nestedNameFormatTopp;
            } else {
                m_nestedNameFormatp->prependExprsp(nodep);
            }
            m_nestedNameFormatp = nodep;

            m_smtName.insert(0, "." + name);
            // Some expressions have empty name which can cause some variables to have the same
            // name and only first one will be written
            if (name == "") {
                if (*m_firstExpressionInsideIndexPointerp) {
                    (*m_firstExpressionInsideIndexPointerp)
                        ->v3warn(
                            E_UNSUPPORTED,
                            "Unsupported: Multiple expressions inside indices of complex "
                            "expression in constraint\n"
                                << (*m_firstExpressionInsideIndexPointerp)->warnContextPrimary()
                                << nodep->warnOther() << "... Location of second expression\n"
                                << nodep->warnContextSecondary());
                }
                *m_firstExpressionInsideIndexPointerp = nodep;
            }
        }

        AstMemberSel* accessTree() { return m_topNestedArrayMemberSelp; }
        const std::string& smtName() { return m_smtName; }

        AstStmtExpr* makeWriteVarStmt(AstVar* varp, AstVar* genp) {
            AstCMethodHard* const methodp = new AstCMethodHard{
                varp->fileline(),
                new AstVarRef{varp->fileline(), VN_AS(genp->user2p(), NodeModule), genp,
                              VAccess::READWRITE},
                VCMethod::RANDOMIZER_WRITE_VAR};
            methodp->dtypeSetVoid();

            methodp->addPinsp(m_topNestedArrayMemberSelp);  // Variable

            const AstNodeDType* const dtypep = varp->dtypep();  // Width
            const size_t width = m_topNestedArrayMemberSelp->varp()->dtypep()->width();
            methodp->addPinsp(new AstConst{dtypep->fileline(), AstConst::Unsized64{}, width});

            methodp->addPinsp(m_nestedNameFormatTopp);  // Solver name
            m_nestedNameFormatp = nullptr;

            methodp->addPinsp(
                new AstConst{dtypep->fileline(), AstConst::Unsized64{}, 0});  // Dimension

            m_topNestedArrayMemberSelp = nullptr;
            return methodp->makeStmt();
        }

        AstNodeExpr* cloneName() { return m_nestedNameFormatTopp->cloneTree(false); }

        void error() {
            VL_DO_DANGLING(m_topNestedArrayMemberSelp->deleteTree(), m_topNestedArrayMemberSelp);
        }

        NestedAccessPath(AstMemberSel* topMemberSelp, AstNode** pointerToFirstExprp)
            : m_topNestedArrayMemberSelp{topMemberSelp}
            , m_firstExpressionInsideIndexPointerp{pointerToFirstExprp} {}
        ~NestedAccessPath() {
            if (m_nestedNameFormatp) {
                VL_DO_CLEAR(m_nestedNameFormatTopp->deleteTree(),
                            m_nestedNameFormatTopp = nullptr);
                m_nestedNameFormatp = nullptr;
            }
        }
    };
    NestedAccessPath* m_nestedAccessp = nullptr;  // Indicates state of nested access

    // Emit enum range hard constraint for a single variable
    AstNodeExpr* createEnumConstraint(FileLine* const fl, const std::string& smtName,
                                      AstEnumDType* const enumDtp, AstVar* const genVarp) {
        AstNodeModule* const genModp = VN_AS(genVarp->user2p(), NodeModule);
        const int width = enumDtp->width();
        std::string constraint = "(__Vbv (or";
        for (AstEnumItem* const itemp : enumDtp->itemspList()) {
            const AstConst* const vconstp = VN_AS(itemp->valuep(), Const);
            constraint += " (= " + smtName + " (_ bv" + cvtToStr(vconstp->toUInt()) + " "
                          + cvtToStr(width) + "))";
        }
        constraint += "))";
        AstCMethodHard* const callp = new AstCMethodHard{
            fl, new AstVarRef{fl, genModp, genVarp, VAccess::READWRITE}, VCMethod::RANDOMIZER_HARD,
            new AstConst{fl, AstConst::String{}, constraint}};
        // hard() pin layout is asserted in EmitCFunc: the variable list is always pin 2
        callp->addPinsp(new AstCExpr{fl, AstCExpr::Pure{}, "{\"" + smtName + "\"}"});
        callp->dtypeSetVoid();
        return callp;
    };

    // Routes nested sub-objects with static rand vars when the outer class has none.
    AstVar* findStaticRandModeVarMember(AstClass* classp) const {
        while (true) {
            if (AstVar* const varp
                = VN_CAST(m_memberMap.findMember(classp, "__Vstaticrandmode"), Var)) {
                return varp;
            }
            AstClassExtends* const extendsp = classp->extendsp();
            if (!extendsp) return nullptr;
            classp = extendsp->classp();
        }
    }

    // Mark the one directly-referenced member; it must reach the solver even when it
    // carries no rand qualifier (the constraint refers to it).
    void markConstrainedRandMember(AstStructDType* const structp, const std::string& name) {
        AstMemberDType* const memberp
            = VN_CAST(m_memberMap.findMember(structp, name), MemberDType);
        UASSERT_OBJ(memberp, structp, "Constraint references unknown struct member " << name);
        memberp->markConstrainedRand(true);
    }

    // True when the aggregate is reached through rand-qualified struct members only
    bool isRandQualifiedPath(const AstNodeExpr* nodep) {
        while (nodep) {
            if (const AstStructSel* const selp = VN_CAST(nodep, StructSel)) {
                if (AstStructDType* const structp
                    = VN_CAST(selp->fromp()->dtypep()->skipRefp(), StructDType)) {
                    const AstMemberDType* const memberp
                        = VN_CAST(m_memberMap.findMember(structp, selp->name()), MemberDType);
                    if (memberp && !memberp->rand().isRandomizable()) return false;
                }
                nodep = selp->fromp();
            } else if (const AstArraySel* const selp = VN_CAST(nodep, ArraySel)) {
                nodep = selp->fromp();
            } else if (const AstCMethodHard* const methodp = VN_CAST(nodep, CMethodHard)) {
                nodep = methodp->fromp();
            } else {
                break;
            }
        }
        return true;
    }

    // IEEE 1800-2023 18.4: all rand members of a rand unpacked struct are solved
    // concurrently, so unreferenced rand members must still reach the solver.
    static void markStructConstrainedRandRecurse(AstNodeDType* const dtypep) {
        AstStructDType* const structp = VN_CAST(SmtUtil::arrayElementDTypep(dtypep), StructDType);
        if (!structp || structp->packed()) return;
        structp->markConstrainedRand(true);
        for (AstMemberDType* const memberp : structp->memberspList()) {
            // Non-rand members keep their value. TODO: randc members are solved as
            // plain rand (uniform); per-member cyclic state is not generated for structs.
            if (!memberp->rand().isRandomizable()) continue;
            memberp->markConstrainedRand(true);
            markStructConstrainedRandRecurse(memberp->subDTypep());
        }
    }

    // Build full path for a MemberSel chain (e.g., "obj.l2.l3.l4")
    std::string buildMemberPath(const AstMemberSel* const memberSelp) {
        const AstNode* fromp = memberSelp->fromp();
        if (const AstVarRef* const refp = VN_CAST(fromp, VarRef)) {
            // Base case: reached root VarRef
            return refp->name() + "." + memberSelp->name();
        } else if (const AstMemberSel* const selp = VN_CAST(fromp, MemberSel)) {
            // Recursive case: build path from outer levels
            return buildMemberPath(selp) + "." + memberSelp->name();
        }
        memberSelp->v3fatalSrc("Unexpected node type in MemberSel chain");
        return "";
    }
    // C++ initializer list of the recorded symbols
    static std::string constraintVarsList(const std::set<std::string>& vars) {
        std::string list = "{";
        for (const std::string& name : vars) {
            if (list.size() > 1) list += ", ";
            list += "\"" + name + "\"";
        }
        return list + "}";
    }

    static AstNodeExpr* getFromp(const AstNodeExpr* const nodep) {
        if (const AstCMethodHard* const cmethp = VN_CAST(nodep, CMethodHard)) {
            return cmethp->fromp();
        }
        return getSelFromp(nodep);
    }

    static std::string extractSolveBeforeBaseName(const AstNodeExpr* exprp) {
        while (const AstNodeExpr* const fromp = getFromp(exprp)) exprp = fromp;
        if (const AstVarRef* const vrefp = VN_CAST(exprp, VarRef)) return vrefp->name();
        return "";
    }

    // Solver name of the element at index 'idxp' of the array named 'namep'
    static AstNodeExpr* newElementNamep(FileLine* fl, AstNodeExpr* namep, AstNodeExpr* idxp) {
        AstCFuncHard* const hexp = new AstCFuncHard{fl, VCFunction::RANDOMIZER_TO_SOLVER_HEX,
                                                    idxp->cloneTreePure(false)};
        hexp->dtypeSetString();
        AstNodeExpr* const prefixp
            = new AstConcatN{fl, namep, new AstConst{fl, AstConst::String{}, "."}};
        return new AstConcatN{fl, prefixp, hexp};
    }

    // Solver name of the variable referenced by the selects and array elements in 'nodep'
    static AstNodeExpr* buildNamePrefix(FileLine* fl, const AstNodeExpr* const nodep) {
        if (const AstVarRef* const refp = VN_CAST(nodep, VarRef)) {
            return new AstConst{fl, AstConst::String{}, refp->name()};
        }

        // Empty if not rooted in a variable, as under an unsupported MemberSel reported below
        const AstNodeExpr* const fromp = getFromp(nodep);
        AstNodeExpr* const namep
            = fromp ? buildNamePrefix(fl, fromp) : new AstConst{fl, AstConst::String{}, ""};

        if (const AstStructSel* const selp = VN_CAST(nodep, StructSel)) {
            return new AstConcatN{fl, namep,
                                  new AstConst{fl, AstConst::String{}, "." + selp->name()}};
        } else if (VN_IS(nodep, MemberSel)) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: Nested array element access in global constraint");
        } else if (const AstCMethodHard* const cmethp = VN_CAST(nodep, CMethodHard)) {
            UASSERT_OBJ(cmethp->method() == VCMethod::ARRAY_AT, cmethp,
                        "Unexpected CMethodHard: " << cmethp->prettyTypeName());
            return newElementNamep(fl, namep, cmethp->pinsp());
        }
        return namep;
    }

    // Solver name of a solve-before variable reference, as a string expression.
    // Handles simple vars, struct selects, and array element selects (for foreach).
    static AstNodeExpr* buildPathExpr(FileLine* const fl, const AstNodeExpr* nodep,
                                      const std::string selName) {
        AstNodeExpr* const namep = buildNamePrefix(fl, nodep);
        if (selName.empty()) return namep;
        return new AstConcatN{fl, namep, new AstConst{fl, AstConst::String{}, "." + selName}};
    }

    // Helper: get fromp from MemberSel or StructSel
    static AstNodeExpr* getSelFromp(const AstNodeExpr* exprp) {
        if (const AstMemberSel* const mp = VN_CAST(exprp, MemberSel)) return mp->fromp();
        if (const AstStructSel* const sp = VN_CAST(exprp, StructSel)) return sp->fromp();
        return nullptr;
    }

    // Solver name of a solve-before variable reference, as a string expression.
    // Returns nullptr for unsupported expression types.
    AstNodeExpr* buildSolveBeforeNameExpr(FileLine* fl, AstNodeExpr* exprp) {
        if (const AstVarRef* const varrefp = VN_CAST(exprp, VarRef)) {
            return new AstConst{fl, AstConst::String{}, varrefp->name()};
        }
        // Handle MemberSel or StructSel (V3Width converts MemberSel -> StructSel for structs)
        if (AstNodeExpr* const selFromp = getSelFromp(exprp)) {
            const std::string selName = exprp->name();
            // Check if fromp chain contains ArraySel (e.g., cfg[i].w)
            if (const AstArraySel* const arrSelp = VN_CAST(selFromp, ArraySel)) {
                std::string baseName;
                if (const AstVarRef* const vp = VN_CAST(arrSelp->fromp(), VarRef)) {
                    baseName = vp->name();
                } else if (const AstMemberSel* const mp = VN_CAST(arrSelp->fromp(), MemberSel)) {
                    baseName = buildMemberPath(mp);
                }
                if (baseName.empty()) return nullptr;
                return newElementNamep(fl, new AstConst{fl, AstConst::String{}, baseName},
                                       arrSelp->bitp());
            }
            // Static member path (obj.field)
            if (const AstVarRef* const vp = VN_CAST(selFromp, VarRef)) {
                return new AstConst{fl, AstConst::String{}, vp->name() + "." + selName};
            }
            if (VN_IS(selFromp, MemberSel) || VN_IS(selFromp, StructSel)
                || VN_IS(selFromp, CMethodHard)) {
                return buildPathExpr(fl, selFromp, selName);
            }
            return nullptr;
        }
        if (VN_IS(exprp, CMethodHard)) return buildPathExpr(fl, exprp, "");
        const AstNodeSel* selp = VN_CAST(exprp, ArraySel);
        if (!selp) selp = VN_CAST(exprp, AssocSel);
        if (selp) {
            // arr[i] -> dynamic name
            std::string baseName;
            if (const AstVarRef* const vp = VN_CAST(selp->fromp(), VarRef)) {
                baseName = vp->name();
            } else if (const AstMemberSel* const mp = VN_CAST(selp->fromp(), MemberSel)) {
                baseName = buildMemberPath(mp);
            }
            if (baseName.empty()) return nullptr;
            return newElementNamep(fl, new AstConst{fl, AstConst::String{}, baseName},
                                   selp->bitp());
        }
        // Packed struct member: SEL(ARRAYSEL(...)) -- bit select on array element.
        // Solver registers the whole element, so promote to array element level.
        if (const AstSel* const bitSelp = VN_CAST(exprp, Sel)) {
            return buildSolveBeforeNameExpr(fl, bitSelp->fromp());
        }
        return nullptr;
    }

    AstSFormatF* getConstFormat(AstNodeExpr* nodep) {
        return new AstSFormatF{nodep->fileline(), (nodep->width() & 3) ? "#b%b" : "#x%x", false,
                               nodep};
    }
    bool editFormat(AstNodeExpr* nodep) {
        if (nodep->user1()) return false;
        // Replace computable expression with SMT constant
        VNRelinker handle;
        nodep->unlinkFrBack(&handle);
        handle.relink(getConstFormat(nodep));
        return true;
    }
    AstNodeExpr* wrapWithCond(AstNodeExpr* const exprp, AstNodeExpr* const condp,
                              const int width) {
        if (condp) {
            FileLine* const flp = exprp->fileline();
            return new AstCond{
                flp, condp, exprp,
                getConstFormat(new AstConst{flp, AstConst::WidthedValue{}, width, 0})};
        }
        return exprp;
    }
    AstSFormatF* editSMT(AstNodeExpr* nodep, AstNodeExpr* lhsp = nullptr,
                         AstNodeExpr* rhsp = nullptr, AstNodeExpr* thsp = nullptr) {
        // Replace incomputable (result-dependent) expression with SMT expression
        std::string smtExpr = nodep->emitSMT();  // Might need child width (AstExtend)
        if (smtExpr == "") {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported expression inside constraint");
            return nullptr;
        }

        const int lhsWidth = lhsp ? lhsp->width() : 0;
        const int rhsWidth = rhsp ? rhsp->width() : 0;
        const int thsWidth = thsp ? thsp->width() : 0;
        AstNodeExpr* lhsCondp = nullptr;
        AstNodeExpr* rhsCondp = nullptr;
        AstNodeExpr* thsCondp = nullptr;

        if (lhsp) {
            VL_RESTORER(m_conditionp);
            m_conditionp = nullptr;
            lhsp = VN_AS(iterateSubtreeReturnEdits(lhsp->backp() ? lhsp->unlinkFrBack() : lhsp),
                         NodeExpr);
            lhsCondp = m_conditionp;
        }
        if (rhsp) {
            VL_RESTORER(m_conditionp);
            m_conditionp = nullptr;
            rhsp = VN_AS(iterateSubtreeReturnEdits(rhsp->backp() ? rhsp->unlinkFrBack() : rhsp),
                         NodeExpr);
            rhsCondp = m_conditionp;
        }
        if (thsp) {
            VL_RESTORER(m_conditionp);
            m_conditionp = nullptr;
            thsp = VN_AS(iterateSubtreeReturnEdits(thsp->backp() ? thsp->unlinkFrBack() : thsp),
                         NodeExpr);
            thsCondp = m_conditionp;
        }

        AstNodeExpr* argsp = nullptr;
        for (string::iterator pos = smtExpr.begin(); pos != smtExpr.end(); ++pos) {
            if (pos[0] == '%') {
                ++pos;
                switch (pos[0]) {
                case '%': break;
                case 'l':
                    pos[0] = 's';
                    UASSERT_OBJ(lhsp, nodep, "emitSMT() references undef node");
                    argsp = AstNode::addNext(argsp, wrapWithCond(lhsp, lhsCondp, lhsWidth));
                    lhsp = nullptr;
                    break;
                case 'r':
                    pos[0] = 's';
                    UASSERT_OBJ(rhsp, nodep, "emitSMT() references undef node");
                    argsp = AstNode::addNext(argsp, wrapWithCond(rhsp, rhsCondp, rhsWidth));
                    rhsp = nullptr;
                    break;
                case 't':
                    pos[0] = 's';
                    UASSERT_OBJ(thsp, nodep, "emitSMT() references undef node");
                    argsp = AstNode::addNext(argsp, wrapWithCond(thsp, thsCondp, thsWidth));
                    thsp = nullptr;
                    break;
                default: nodep->v3fatalSrc("Unknown emitSMT format code: %" << pos[0]); break;
                }
            }
        }
        UASSERT_OBJ(!lhsp, nodep, "Missing emitSMT %l for " << lhsp);
        UASSERT_OBJ(!rhsp, nodep, "Missing emitSMT %r for " << rhsp);
        UASSERT_OBJ(!thsp, nodep, "Missing emitSMT %t for " << thsp);
        AstSFormatF* const newp = new AstSFormatF{nodep->fileline(), smtExpr, false, argsp};

        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
        return newp;
    }

    AstNodeExpr* editSingle(FileLine* fl, AstNode* itemsp) {
        if (!itemsp) return nullptr;

        VL_RESTORER(m_wantSingle);
        m_wantSingle = true;

        {
            AstBegin* const tempp = new AstBegin{fl, "[EditWrapper]", nullptr, false};
            tempp->addDeclsp(itemsp->unlinkFrBackWithNext());
            VL_DO_DANGLING(iterateAndNextNull(tempp->declsp()), itemsp);
            itemsp = tempp->declsp();
            if (itemsp) itemsp->unlinkFrBackWithNext();
            VL_DO_DANGLING(tempp->deleteTree(), tempp);
        }
        if (!itemsp) return nullptr;

        AstNodeExpr* const exprsp = VN_CAST(itemsp, NodeExpr);
        UASSERT_OBJ(exprsp, itemsp, "Single not expression?");

        if (!exprsp->nextp()) return exprsp;

        std::ostringstream fmt;
        fmt << "(bvand";
        for (AstNode* itemp = exprsp; itemp; itemp = itemp->nextp()) fmt << " %s";
        fmt << ')';
        return new AstSFormatF{fl, fmt.str(), false, exprsp};
    }

    AstNodeExpr* newSel(FileLine* fl, AstNodeExpr* arrayp, AstNodeExpr* idxp) {
        // similar to V3WidthSel.cpp
        // skipRefp() unwraps typedef wrappers (AstRefDType) so the dtype kind
        // checks below recognize types spelled as `typedef <scalar> <name>[$]`.
        AstNodeDType* const arrDtp = arrayp->unlinkFrBack()->dtypep()->skipRefp();
        AstNodeExpr* selp = nullptr;
        if (VN_IS(arrDtp, QueueDType) || VN_IS(arrDtp, DynArrayDType))
            selp = new AstCMethodHard{fl, arrayp, VCMethod::ARRAY_AT, idxp};
        else if (VN_IS(arrDtp, UnpackArrayDType))
            selp = new AstArraySel{fl, arrayp, idxp};
        else if (VN_IS(arrDtp, AssocArrayDType))
            selp = new AstAssocSel{fl, arrayp, idxp};
        UASSERT_OBJ(selp, arrayp, "Selecting from non-array?");
        selp->dtypep(arrDtp->subDTypep());
        return selp;
    }

    // Convert expression to target width using extend or truncate as needed
    AstNodeExpr* adjustWidth(FileLine* fl, AstNodeExpr* exprp, int targetWidth,
                             VSigning targetSigning) {
        const int exprWidth = exprp->width();
        if (targetWidth > exprWidth) {
            // Extend to match target width
            AstNodeExpr* const resultp = new AstExtend{fl, exprp, targetWidth};
            resultp->dtypeChgSigned(targetSigning);
            return resultp;
        } else if (targetWidth < exprWidth) {
            // Truncate to match target width
            AstNodeExpr* const resultp = new AstSel{fl, exprp, 0, targetWidth};
            resultp->dtypeChgSigned(targetSigning);
            return resultp;
        } else {
            // Width already matches
            return exprp;
        }
    }

    // Extract return expression from a simple function body, or nullptr if too complex.
    // Uses foreach to walk all assigns regardless of body organization (JumpBlock nesting etc.).
    // Takes the last assignment to the return variable -- the first is the initializer.
    AstNodeExpr* extractReturnExpr(AstFunc* funcp) {
        AstVar* const retVarp = funcp->fvarp();
        if (!retVarp) return nullptr;
        AstNodeExpr* retExprp = nullptr;
        int assignCount = 0;
        funcp->foreach([&](AstAssign* assignp) {
            AstVarRef* const lhsp = VN_CAST(assignp->lhsp(), VarRef);
            if (!lhsp || lhsp->varp() != retVarp) return;
            retExprp = assignp->rhsp();
            ++assignCount;
        });
        // Simple function: initializer + return (2) or just return (1)
        if (assignCount > 2 || !retExprp) return nullptr;
        return retExprp;
    }

    // Bottom-up user1 propagation on inlined expression tree
    void propagateUser1InlineRecurse(AstNodeExpr* nodep) {
        if (VN_IS(nodep, NodeVarRef)) {
            nodep->user1(VN_AS(nodep, NodeVarRef)->varp()->rand().isRandomizable());
            return;
        }
        if (VN_IS(nodep, Const)) {
            nodep->user1(false);
            return;
        }
        int anyChild = false;  // Used as bool
        if (AstNodeExpr* const cp = VN_CAST(nodep->op1p(), NodeExpr)) {
            propagateUser1InlineRecurse(cp);
            anyChild |= cp->user1();
        }
        if (AstNodeExpr* const cp = VN_CAST(nodep->op2p(), NodeExpr)) {
            propagateUser1InlineRecurse(cp);
            anyChild |= cp->user1();
        }
        if (AstNodeExpr* const cp = VN_CAST(nodep->op3p(), NodeExpr)) {
            propagateUser1InlineRecurse(cp);
            anyChild |= cp->user1();
        }
        if (AstNodeExpr* const cp = VN_CAST(nodep->op4p(), NodeExpr)) {
            propagateUser1InlineRecurse(cp);
            anyChild |= cp->user1();
        }
        nodep->user1(anyChild);
    }

    // Prepend the bucket preamble stmts stored on user3p by lowerDistConstraints to the
    // statements that will become the body of the generated AstForeach, so the per-element
    // bucket draw is evaluated in the same scope as its references.
    static AstNodeStmt* prependDistPreamble(AstConstraintForeach* nodep, AstNodeStmt* bodyp) {
        AstNodeStmt* const preamblep = VN_AS(nodep->user3p(), NodeStmt);
        if (!preamblep) return bodyp;
        nodep->user3p(nullptr);
        preamblep->addNext(bodyp);
        return preamblep;
    }

    // Constraint text over the elements of an array is built at run time, by a loop
    // appending to a string variable.

    // Variable the text is built in
    static AstVar* newTextVarp(AstNode* nodep) {
        AstVar* const varp = new AstVar{nodep->fileline(), VVarType::BLOCKTEMP, "__Vtext",
                                        nodep->findStringDType()};
        varp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
        return varp;
    }
    // Statement appending 'exprp' to the text in 'varp'
    static AstStmtExpr* newTextAppendp(FileLine* flp, AstVar* varp, AstNodeExpr* exprp) {
        AstCFuncHard* const callp = new AstCFuncHard{flp, VCFunction::STRING_APPEND,
                                                     new AstVarRef{flp, varp, VAccess::READWRITE}};
        callp->addPinsp(exprp);
        callp->dtypeSetVoid();
        return callp->makeStmt();
    }
    // Statement appending a space and the term 'termp' to the text in 'varp'
    static AstStmtExpr* newTermAppendp(FileLine* flp, AstVar* varp, AstNodeExpr* termp) {
        return newTextAppendp(
            flp, varp, new AstConcatN{flp, new AstConst{flp, AstConst::String{}, " "}, termp});
    }
    // The SMT operator 'op' applied to the terms in 'varp', or 'identity' if there are none
    static AstCond* newTextApplyp(FileLine* flp, AstVar* varp, const std::string& op,
                                  const std::string& identity) {
        AstNodeExpr* const isEmptyp = new AstEqN{flp, new AstVarRef{flp, varp, VAccess::READ},
                                                 new AstConst{flp, AstConst::String{}, ""}};
        AstNodeExpr* const openp
            = new AstConcatN{flp, new AstConst{flp, AstConst::String{}, "(" + op},
                             new AstVarRef{flp, varp, VAccess::READ}};
        AstNodeExpr* const appliedp
            = new AstConcatN{flp, openp, new AstConst{flp, AstConst::String{}, ")"}};
        return new AstCond{flp, isEmptyp, new AstConst{flp, AstConst::String{}, identity},
                           appliedp};
    }
    // The text 'resultp', after 'foreachp' built it in 'varp', starting from 'init'
    AstSFormatF* newTextBuildp(FileLine* flp, AstVar* varp, const std::string& init,
                               AstForeach* foreachp, AstNodeExpr* resultp) {
        AstBegin* const blockp
            = new AstBegin{flp, m_uniqueNames.get("__VrandBlock"), nullptr, true};
        blockp->addDeclsp(varp);
        blockp->addStmtsp(new AstAssign{flp, new AstVarRef{flp, varp, VAccess::WRITE},
                                        new AstConst{flp, AstConst::String{}, init}});
        blockp->addStmtsp(foreachp);
        return new AstSFormatF{flp, "%s", false, new AstExprStmt{flp, blockp, resultp}};
    }

    // True if the statement references an index variable of an enclosing
    // constraint-foreach. Such a statement must stay inside the loop body; hoisting
    // it out leaves a dangling reference once task inlining deletes the index.
    bool referencesForeachIdx(const AstNode* nodep) const {
        if (m_foreachIdxVars.empty()) return false;
        return nodep->exists(
            [&](const AstVarRef* refp) { return m_foreachIdxVars.count(refp->varp()) != 0; });
    }

    AstBegin* newInitBlockp(AstNodeFTask* const taskp) const {
        AstBegin* const blockp = new AstBegin{
            taskp->fileline(), m_uniqueNames.get("__Vconstraint_init"), nullptr, true};
        taskp->addStmtsp(blockp);
        return blockp;
    }

    // Place a solver-registration statement: into the enclosing foreach body when it
    // references an enclosing foreach index (so it is not hoisted out of the index's
    // scope), otherwise into the init block.
    void addRegistrationStmt(AstNodeStmt* const stmtp, AstBegin* const initp) {
        if (m_foreachp && referencesForeachIdx(stmtp)) {
            // Appending to the body mid-iteration is safe: visit(AstStmtExpr) is a
            // no-op so the appended node is not re-processed, and prependDistPreamble()
            // correctly keeps it as a loop-body statement.
            m_foreachp->addBodyp(stmtp);
        } else {
            initp->addStmtsp(stmtp);
        }
    }

    // Create SFormatF for array dereference inside solver
    AstSFormatF* createSolverArrDerefp(FileLine* const fl, AstNodeExpr* const arrExprp,
                                       AstNodeExpr* const idxExprp) {
        AstNodeExpr* const argsp = AstNode::addNext(arrExprp, idxExprp);
        AstSFormatF* const formatp = new AstSFormatF{fl, "(select %s %s)", false, argsp};
        return formatp;
    }

    void setRandMode(AstVar* const varp, AstMemberSel* const memberselp,
                     const std::string& smtName, const RandomizeMode& randMode,
                     AstBegin* const initp) {
        AstNodeModule* const varClassp = VN_AS(varp->user2p(), NodeModule);
        AstVar* const subRandModeVarp = RandModeVars::randModeVarp(varClassp);
        if (subRandModeVarp) {
            AstNodeExpr* const parentAccessp = memberselp->fromp()->cloneTree(false);
            AstMemberSel* const randModeSelp
                = new AstMemberSel{varp->fileline(), parentAccessp, subRandModeVarp};
            randModeSelp->dtypep(subRandModeVarp->dtypep());
            AstCMethodHard* const atp
                = new AstCMethodHard{varp->fileline(), randModeSelp, VCMethod::ARRAY_AT,
                                     new AstConst{varp->fileline(), randMode.index}};
            atp->dtypeSetUInt32();
            // rand_mode ON: clear disabled state
            AstCMethodHard* const enablep = new AstCMethodHard{
                varp->fileline(),
                new AstVarRef{varp->fileline(), VN_AS(m_genp->user2p(), NodeModule), m_genp,
                              VAccess::READWRITE},
                VCMethod::RANDOMIZER_CLEAR_VAR_DISABLED};
            enablep->dtypeSetVoid();
            AstNodeExpr* const nameExprp
                = m_nestedAccessp ? m_nestedAccessp->cloneName()
                                  : new AstSFormatF{varp->fileline(), smtName, false, nullptr};
            nameExprp->dtypep(varp->dtypep());
            enablep->addPinsp(nameExprp);
            // rand_mode OFF: set disabled state
            AstCMethodHard* const disablep = new AstCMethodHard{
                varp->fileline(),
                new AstVarRef{varp->fileline(), VN_AS(m_genp->user2p(), NodeModule), m_genp,
                              VAccess::READWRITE},
                VCMethod::RANDOMIZER_SET_VAR_DISABLED};
            disablep->dtypeSetVoid();
            AstNodeExpr* const disnp = nameExprp->cloneTree(false);
            disablep->addPinsp(disnp);
            AstIf* const ifp
                = new AstIf{varp->fileline(), atp, enablep->makeStmt(), disablep->makeStmt()};
            addRegistrationStmt(ifp, initp);
        }
    }

    void markRandc(AstVar* const varp, const std::string& smtName, AstBegin* const initp) {
        AstCMethodHard* const markp = new AstCMethodHard{
            varp->fileline(),
            new AstVarRef{varp->fileline(), VN_AS(m_genp->user2p(), NodeModule), m_genp,
                          VAccess::READWRITE},
            VCMethod::RANDOMIZER_MARK_RANDC};
        markp->dtypeSetVoid();
        AstNodeExpr* const nameExprp
            = m_nestedAccessp ? m_nestedAccessp->cloneName()
                              : new AstSFormatF{varp->fileline(), smtName, false, nullptr};
        nameExprp->dtypep(varp->dtypep());
        markp->addPinsp(nameExprp);
        addRegistrationStmt(markp->makeStmt(), initp);
    }

    AstNodeModule* getLeftmostVarModulep(AstMemberSel* const memberselp,
                                         AstVar* const varp) const {
        if (memberselp) {
            // For memberselp, find the leftmost varref to get the class
            AstNode* leftMostNodep = memberselp->fromp();
            while (AstMemberSel* const nestedMemberSelp = VN_CAST(leftMostNodep, MemberSel)) {
                leftMostNodep = nestedMemberSelp->fromp();
            }
            if (AstNodeVarRef* const rootVarRefp = VN_CAST(leftMostNodep, NodeVarRef)) {
                return VN_AS(rootVarRefp->varp()->user2p(), NodeModule);
            }
            return VN_AS(memberselp->user2p(), NodeModule);
        }
        return VN_AS(varp->user2p(), NodeModule);
    }

    AstBegin* getInitp(AstVar* const varp, const bool memberselOrStructSel,
                       AstNodeModule* const classp) const {
        if (m_inlineInitBlockp) return m_inlineInitBlockp;
        varp->user3(true);
        if (memberselOrStructSel) {
            if (AstNodeFTask* const taskp
                = VN_AS(m_memberMap.findMember(classp, "randomize"), NodeFTask)) {
                return newInitBlockp(taskp);
            }
            // Inherited rand members may belong to a base class
            // that has no randomize(); use the caller's function
            if (m_memberselInitTaskp) return newInitBlockp(m_memberselInitTaskp);
            classp->v3fatalSrc("No randomize() in class");
        } else {
            AstNodeFTask* const taskp = VN_AS(m_memberMap.findMember(classp, "new"), NodeFTask);
            UASSERT_OBJ(taskp, classp, "No new() in class");
            return newInitBlockp(taskp);
        }
        return nullptr;
    }

    void createWriteVarForClassFields(AstClass* const elemClassp, const std::string& smtName,
                                      AstVar* const iterVarp, const bool isUnpackedClassRefArray,
                                      AstNodeModule* const classOrPackagep, AstVar* const varp,
                                      AstIf* const ifNonNullp,
                                      AstClassRefDType* elemClassRefDtp) const {
        FileLine* const fl = varp->fileline();
        AstNodeModule* const varClassp = VN_AS(varp->user2p(), NodeModule);
        const std::string idxFmt
            = isUnpackedClassRefArray ? "%0x" : keyHexFormat(iterVarp->dtypep()->skipRefp());

        for (const AstClass* cp = elemClassp; cp;
             cp = cp->extendsp() ? cp->extendsp()->classp() : nullptr) {
            for (AstNode* const mnodep : cp->memberspList()) {
                AstVar* const memberVarp = VN_CAST(mnodep, Var);
                if (!memberVarp || !memberVarp->rand().isRandomizable()) continue;
                AstNodeDType* const memberDtp = memberVarp->dtypep()->skipRefp();
                if (VN_IS(memberDtp, ClassRefDType) || memberDtp->isNonPackedArray()) continue;
                const int memberWidth = memberDtp->width();

                AstVarRef* const arrayWrRefp = new AstVarRef{fl, varClassp, varp, VAccess::WRITE};
                arrayWrRefp->classOrPackagep(classOrPackagep);
                AstNodeExpr* atWritep;
                if (isUnpackedClassRefArray) {
                    atWritep = new AstArraySel{fl, arrayWrRefp,
                                               new AstVarRef{fl, iterVarp, VAccess::READ}};
                } else {
                    atWritep = new AstCMethodHard{fl, arrayWrRefp, VCMethod::ARRAY_AT_WRITE,
                                                  new AstVarRef{fl, iterVarp, VAccess::READ}};
                }
                atWritep->dtypep(elemClassRefDtp);
                AstMemberSel* const memberSelp = new AstMemberSel{fl, atWritep, memberVarp};

                AstCMethodHard* const writeVarp
                    = new AstCMethodHard{fl,
                                         new AstVarRef{fl, VN_AS(m_genp->user2p(), NodeModule),
                                                       m_genp, VAccess::READWRITE},
                                         VCMethod::RANDOMIZER_WRITE_VAR};
                writeVarp->dtypeSetVoid();
                writeVarp->addPinsp(memberSelp);
                writeVarp->addPinsp(
                    new AstConst{fl, AstConst::Unsized64{}, static_cast<uint64_t>(memberWidth)});
                writeVarp->addPinsp(
                    new AstSFormatF{fl, smtName + "." + idxFmt + "." + memberVarp->name(), false,
                                    new AstVarRef{fl, iterVarp, VAccess::READ}});
                writeVarp->addPinsp(new AstConst{fl, AstConst::Unsized64{}, 0ULL});
                ifNonNullp->addThensp(writeVarp->makeStmt());
            }
        }
    }

    void createSolverArrayHandle(AstVar* const varp, AstClassRefDType* elemClassRefDtp,
                                 AstNodeModule* const classOrPackagep,
                                 const bool isUnpackedClassRefArray,
                                 const std::string& smtName) const {
        FileLine* const fl = varp->fileline();
        AstClass* const elemClassp = elemClassRefDtp->classp();
        AstNodeModule* const varClassp = VN_AS(varp->user2p(), NodeModule);

        AstVar* const iterVarp = new AstVar{fl, VVarType::BLOCKTEMP, m_uniqueNames.get("__Vi"),
                                            varp->findUInt32DType()};
        iterVarp->funcLocal(true);
        iterVarp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
        // Associative array elements are reached by key, walked with first()/next()
        AstAssocArrayDType* const assocDtp = VN_CAST(varp->dtypep()->skipRefp(), AssocArrayDType);
        AstVar* const idxVarp = assocDtp
                                    ? new AstVar{fl, VVarType::BLOCKTEMP,
                                                 m_uniqueNames.get("__Vk"), assocDtp->keyDTypep()}
                                    : iterVarp;

        AstNodeStmt* const stmtsp
            = new AstAssign{fl, new AstVarRef{fl, iterVarp, VAccess::WRITE}, new AstConst{fl, 0}};

        AstNodeExpr* sizep;
        if (isUnpackedClassRefArray) {
            const int arraySize
                = VN_AS(varp->dtypep()->skipRefp(), UnpackArrayDType)->elementsConst();
            sizep = new AstConst{fl, static_cast<uint32_t>(arraySize)};
        } else {
            AstVarRef* const arraySizeRefp = new AstVarRef{fl, varClassp, varp, VAccess::READ};
            arraySizeRefp->classOrPackagep(classOrPackagep);
            AstCMethodHard* const dynSizep
                = new AstCMethodHard{fl, arraySizeRefp, VCMethod::DYN_SIZE, nullptr};
            dynSizep->dtypeSetUInt32();
            sizep = dynSizep;
        }

        AstLoop* const loopp = new AstLoop{fl};
        stmtsp->addNext(loopp);
        loopp->addStmtsp(new AstLoopTest{
            fl, loopp, new AstLt{fl, new AstVarRef{fl, iterVarp, VAccess::READ}, sizep}});

        AstVarRef* const arrayReadRefp = new AstVarRef{fl, varClassp, varp, VAccess::READ};
        arrayReadRefp->classOrPackagep(classOrPackagep);
        AstNodeExpr* atReadp;
        if (isUnpackedClassRefArray) {
            atReadp
                = new AstArraySel{fl, arrayReadRefp, new AstVarRef{fl, idxVarp, VAccess::READ}};
        } else {
            atReadp = new AstCMethodHard{fl, arrayReadRefp, VCMethod::ARRAY_AT,
                                         new AstVarRef{fl, idxVarp, VAccess::READ}};
        }
        atReadp->dtypep(elemClassRefDtp);
        AstIf* const ifNonNullp
            = new AstIf{fl, new AstNeq{fl, atReadp, new AstConst{fl, AstConst::Null{}}}, nullptr};
        loopp->addStmtsp(ifNonNullp);

        createWriteVarForClassFields(elemClassp, smtName, idxVarp, isUnpackedClassRefArray,
                                     classOrPackagep, varp, ifNonNullp, elemClassRefDtp);

        loopp->addStmtsp(new AstAssign{
            fl, new AstVarRef{fl, iterVarp, VAccess::WRITE},
            new AstAdd{fl, new AstConst{fl, 1}, new AstVarRef{fl, iterVarp, VAccess::READ}}});

        varp->user3(true);
        AstBegin* initp = m_inlineInitBlockp;
        if (!initp) {
            AstNodeFTask* const taskp = VN_AS(m_memberMap.findMember(varClassp, "new"), NodeFTask);
            UASSERT_OBJ(taskp, varClassp, "No new() in class");
            initp = newInitBlockp(taskp);
        }
        // At the beginning, so declared before referenced
        initp->addDeclsp(iterVarp);
        if (assocDtp) {
            idxVarp->funcLocal(true);
            initp->addDeclsp(idxVarp);
            AstCMethodHard* const firstp
                = new AstCMethodHard{fl, arrayReadRefp->cloneTree(false), VCMethod::ASSOC_FIRST,
                                     new AstVarRef{fl, idxVarp, VAccess::READWRITE}};
            firstp->dtypeSetInt();
            AstCMethodHard* const nextp = firstp->cloneTree(false);
            nextp->method(VCMethod::ASSOC_NEXT);
            initp->addStmtsp(firstp->makeStmt());
            loopp->addStmtsp(nextp->makeStmt());
        }
        initp->addStmtsp(stmtsp);
    }

    void createSolverVarHandle(AstVar* const varp, const bool structSelOrCMeth,
                               const bool isGlobalConstrained, const RandomizeMode randMode,
                               AstMemberSel* const memberselp, const std::string& smtName,
                               AstNodeModule* const classOrPackagep, AstNodeModule* const classp,
                               AstBegin* const initp) {
        uint32_t unpackedDims = 0;
        if (varp->dtypeSkipRefp()->isNonPackedArray()) {
            unpackedDims = varp->dtypep()->dimensions(false).second;
        }
        if (VN_IS(varp->dtypeSkipRefp(), StructDType)
            && !VN_AS(varp->dtypeSkipRefp(), StructDType)->packed()) {
            markStructConstrainedRandRecurse(varp->dtypeSkipRefp());
            unpackedDims = 1;
        }
        AstCMethodHard* const methodp = new AstCMethodHard{
            varp->fileline(),
            new AstVarRef{varp->fileline(), VN_AS(m_genp->user2p(), NodeModule), m_genp,
                          VAccess::READWRITE},
            VCMethod::RANDOMIZER_WRITE_VAR};
        methodp->dtypeSetVoid();
        if (memberselp) {
            methodp->addPinsp(memberselp);
        } else {
            AstVarRef* const varRefp
                = new AstVarRef{varp->fileline(), classp, varp, VAccess::WRITE};
            varRefp->classOrPackagep(classOrPackagep);
            methodp->addPinsp(varRefp);
        }
        const size_t width = SmtUtil::arrayElementDTypep(varp->dtypep())->width();
        methodp->addPinsp(new AstConst{varp->fileline(), AstConst::Unsized64{}, width});
        AstNodeExpr* const varnamep = new AstCExpr{varp->fileline(), AstCExpr::Pure{},
                                                   "\"" + smtName + "\"", varp->width()};
        varnamep->dtypep(varp->dtypep());
        methodp->addPinsp(varnamep);
        methodp->addPinsp(
            new AstConst{varp->dtypep()->fileline(), AstConst::Unsized64{}, unpackedDims});
        if (randMode.usesMode && !(isGlobalConstrained && memberselp)) {
            methodp->addPinsp(
                new AstConst{varp->fileline(), AstConst::Unsized64{}, randMode.index});
        }
        // For globalConstrained sub-object members with rand_mode:
        // Always call write_var (keeps variable in solver for constraint
        // evaluation), but toggle disabled state so the solver skips
        // write-back when rand_mode is off.
        initp->addStmtsp(methodp->makeStmt());
        if (varp->lifetime().isStatic() && randMode.usesMode) {
            AstCMethodHard* const markp = new AstCMethodHard{
                varp->fileline(),
                new AstVarRef{varp->fileline(), VN_AS(m_genp->user2p(), NodeModule), m_genp,
                              VAccess::READWRITE},
                VCMethod::RANDOMIZER_MARK_VAR_STATIC};
            AstNodeExpr* const namep = new AstCExpr{varp->fileline(), AstCExpr::Pure{},
                                                    "\"" + smtName + "\"", varp->width()};
            namep->dtypep(varp->dtypep());
            markp->addPinsp(namep);
            markp->dtypeSetVoid();
            initp->addStmtsp(markp->makeStmt());
        }
        if (isGlobalConstrained && memberselp && randMode.usesMode) {
            setRandMode(varp, memberselp, smtName, randMode, initp);
        }
        // If randc, also emit markRandc() for cyclic tracking
        if (varp->isRandC()) markRandc(varp, smtName, initp);
    }

    AstNodeExpr* createVarExprp(AstNodeVarRef* nodep, const RandomizeMode randMode,
                                const std::string& smtName, const bool isGlobalConstrained,
                                AstMemberSel* memberselp, AstVar* const varp) {
        // Use AstSFormatF (not AstConst{String}) to prevent editFormat/V3Const
        // from reformatting the SMT variable name into a hex literal
        AstNodeExpr* exprp = new AstSFormatF{
            nodep->fileline(), m_nestedAccessp ? nodep->name() : smtName, false, nullptr};
        if (!randMode.usesMode) {
            // Global constraints keep nodep alive for write_var processing
            if (!isGlobalConstrained) VL_DO_DANGLING(pushDeletep(nodep), nodep);
            return exprp;
        }

        // Get const format, using memberselp if available for correct width/value
        AstNodeExpr* constFormatp
            = memberselp ? getConstFormat(memberselp->cloneTree(false)) : getConstFormat(nodep);

        // Static rand vars route through the var's owning class's static array
        // (may differ from m_classp when the rand var lives in a sub-object).
        AstNodeExpr* randModeAccessp;
        const bool varIsStatic = varp->lifetime().isStatic();
        AstClass* const varOwningClassp = varIsStatic ? VN_CAST(varp->user2p(), Class) : nullptr;
        AstVar* const ownerStaticRandModeVarp
            = varOwningClassp ? findStaticRandModeVarMember(varOwningClassp) : nullptr;
        if (ownerStaticRandModeVarp) {
            randModeAccessp = new AstVarRef{varp->fileline(),
                                            VN_AS(ownerStaticRandModeVarp->user2p(), NodeModule),
                                            ownerStaticRandModeVarp, VAccess::READ};
        } else if (memberselp) {
            AstNodeModule* const varClassp = VN_AS(varp->user2p(), NodeModule);
            AstVar* const effectiveRandModeVarp = RandModeVars::randModeVarp(varClassp);
            if (effectiveRandModeVarp) {
                // Member's class has randmode, use it
                AstNodeExpr* parentAccessp = memberselp->fromp()->cloneTree(false);
                AstMemberSel* randModeSelp
                    = new AstMemberSel{varp->fileline(), parentAccessp, effectiveRandModeVarp};
                randModeSelp->dtypep(effectiveRandModeVarp->dtypep());
                randModeAccessp = randModeSelp;
            } else {
                // Member's class has no randmode, use current scope's randmode
                UASSERT_OBJ(m_randModeVarp, nodep, "No m_randModeVarp");
                randModeAccessp
                    = new AstVarRef{varp->fileline(), VN_AS(m_randModeVarp->user2p(), NodeModule),
                                    m_randModeVarp, VAccess::READ};
            }
        } else {
            UASSERT_OBJ(m_randModeVarp, nodep, "No m_randModeVarp");
            randModeAccessp
                = new AstVarRef{varp->fileline(), VN_AS(m_randModeVarp->user2p(), NodeModule),
                                m_randModeVarp, VAccess::READ};
        }

        AstCMethodHard* const atp
            = new AstCMethodHard{nodep->fileline(), randModeAccessp, VCMethod::ARRAY_AT,
                                 new AstConst{nodep->fileline(), randMode.index}};
        atp->dtypeSetUInt32();
        exprp = new AstCond{varp->fileline(), atp, exprp, constFormatp};
        exprp->user1(true);  // Mark as formatted
        return exprp;
    }

    // VISITORS
    void visit(AstNodeVarRef* nodep) override {
        AstVar* varp = nodep->varp();
        if (varp->user4p()) {
            bool isSizeRef = false;
            if (AstCMethodHard* const methodp = VN_CAST(nodep->backp(), CMethodHard)) {
                if (methodp->method() == VCMethod::ASSOC_SIZE
                    || methodp->method() == VCMethod::DYN_SIZE) {
                    isSizeRef = true;
                }
            }
            if (!isSizeRef && m_sizeConstrainedArraysp) { m_sizeConstrainedArraysp->insert(varp); }
        }

        // Check if this variable is marked as globally constrained
        const bool isGlobalConstrained = nodep->varp()->globalConstrained();

        AstMemberSel* memberselp = nullptr;
        bool structSelOrCMeth = false;
        // Set below only when narrowing to one struct field/array element;
        // staying null means "check varp's own type" (see its use further down).
        AstNodeDType* selectedDtypep = nullptr;
        std::string smtName;
        if (m_nestedAccessp) {
            m_nestedAccessp->addVarNamePart(
                new AstSFormatF{varp->fileline(), nodep->name(), false, nullptr}, nodep->name());
            smtName = m_nestedAccessp->smtName();
            memberselp = m_nestedAccessp->accessTree();
        } else if (VN_IS(nodep->backp(), MemberSel)) {
            // Build complete path from topmost MemberSel
            AstNode* topMemberSelp = nodep->backp();
            while (VN_IS(topMemberSelp->backp(), MemberSel)) {
                topMemberSelp = topMemberSelp->backp();
            }
            memberselp = VN_AS(topMemberSelp, MemberSel)->cloneTree(false);
            smtName = buildMemberPath(memberselp);
        } else if (VN_IS(nodep->backp(), StructSel) || VN_IS(nodep->backp(), CMethodHard)) {
            // Build complete path for topmost StructSel or CMethodHard::ARRAY_AT
            AstNode* topNodep = nodep->backp();
            while (VN_IS(topNodep->backp(), StructSel) || VN_IS(topNodep->backp(), CMethodHard)) {
                topNodep = topNodep->backp();
            }

            if (VN_IS(topNodep, StructSel) || VN_IS(topNodep, CMethodHard)) {
                structSelOrCMeth = true;
                selectedDtypep = VN_AS(topNodep, NodeExpr)->dtypep();
            }

            memberselp = VN_CAST(topNodep, MemberSel);
            if (memberselp) smtName = buildMemberPath(memberselp);

            // Above functions returned empty string, unrecognized node type,
            // Using nodep->name();
            if (smtName == "") smtName = nodep->name();
        } else {
            // No MemberSel, StructSel or CMethodHard:at : just variable name
            smtName = nodep->name();
        }
        // Recorded so the runtime can tell constraints naming only randc variables apart
        // (#8058). A name matching no registered variable, as a nested access path formatted
        // at runtime does, must be taken as a non-randc variable, so its constraint is never
        // randc-only.
        UASSERT_OBJ(m_constraintVarsp, nodep,
                    "Variable reference outside a constraint expression");
        if (nodep->user1()) m_constraintVarsp->insert(smtName);

        if (memberselp) varp = memberselp->varp();
        // The SMT translation assumes bit-vector operands and does not
        // type-check; embedding a real value produces a malformed width.
        // Check the selected field/element's type, not the whole
        // struct/array's -- a real sibling field elsewhere is irrelevant.
        if (SmtUtil::dtypeContainsReal(structSelOrCMeth ? selectedDtypep : varp->dtypep())) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: real value in this constraint expression");
            return;
        }
        AstNodeModule* const classOrPackagep = nodep->classOrPackagep();
        const RandomizeMode randMode = {.asUQuad = varp->user1()};
        if (!randMode.usesMode && editFormat(nodep)) return;

        AstEnumDType* enumDtp = VN_CAST(nodep->dtypep()->skipRefToEnump(), EnumDType);
        if (enumDtp
            && (std::find(m_rangeConstrainedEnums.begin(), m_rangeConstrainedEnums.end(), varp)
                == m_rangeConstrainedEnums.end())) {
            AstVar* genVarp = m_genp;
            if (m_classp && m_classp->user3p()) genVarp = VN_AS(m_classp->user3p(), Var);
            UASSERT_OBJ(genVarp, nodep, "No 'randomize' variable in m_genp or m_classp");
            AstNodeExpr* enumRangeExprp
                = createEnumConstraint(nodep->fileline(), varp->name(), enumDtp, genVarp);
            AstBegin* targetp = m_inlineInitBlockp;
            if (!targetp) {
                targetp
                    = newInitBlockp(SmtUtil::getCreateConstraintSetupFunc(m_classp, m_memberMap));
            }
            targetp->addStmtsp(enumRangeExprp->makeStmt());
            m_rangeConstrainedEnums.push_back(varp);
        }

        VNRelinker relinker;
        nodep->unlinkFrBack(&relinker);
        AstNodeExpr* const exprp
            = createVarExprp(nodep, randMode, smtName, isGlobalConstrained, memberselp, varp);
        relinker.relink(exprp);

        // Global / inline / class-level member-select refs key on the full path
        // (so same-type sub-objects c1.x, c2.x stay distinct); a plain class-level
        // variable keys on user3(). Inline 'with' dedups per function (own solver).
        const bool alreadyWritten = m_inlineInitBlockp    ? m_inlineWrittenVars.count(smtName) > 0
                                    : isGlobalConstrained ? m_writtenVars.count(smtName) > 0
                                    : memberselp          ? m_writtenVars.count(smtName) > 0
                                                          : varp->user3();
        const bool shouldWriteVar = !alreadyWritten;
        if (shouldWriteVar) {
            // Track this variable path as written
            if (m_inlineInitBlockp)
                m_inlineWrittenVars.insert(smtName);
            else if (isGlobalConstrained || memberselp)
                m_writtenVars.insert(smtName);
            // For global constraints, delete nodep after processing
            if (isGlobalConstrained && !nodep->backp()) VL_DO_DANGLING(pushDeletep(nodep), nodep);

            bool isClassRefArray = false;
            bool isUnpackedClassRefArray = false;
            AstClassRefDType* elemClassRefDtp = nullptr;
            {
                AstNodeDType* varDtp = varp->dtypep()->skipRefp();
                if (varDtp->isNonPackedArray()) {
                    AstNodeDType* const elemDtp = varDtp->subDTypep()->skipRefp();
                    elemClassRefDtp = VN_CAST(elemDtp, ClassRefDType);
                    if (elemClassRefDtp) {
                        isClassRefArray = true;
                        isUnpackedClassRefArray = VN_IS(varDtp, UnpackArrayDType);
                    }
                }
            }

            AstNodeModule* const classp = getLeftmostVarModulep(memberselp, varp);
            AstBegin* const initp = getInitp(varp, memberselp || structSelOrCMeth, classp);
            if (m_nestedAccessp) {
                AstStmtExpr* const writeVarStmtp = m_nestedAccessp->makeWriteVarStmt(varp, m_genp);
                addRegistrationStmt(writeVarStmtp, initp);
                if (isGlobalConstrained && memberselp && randMode.usesMode) {
                    setRandMode(varp, memberselp, smtName, randMode, initp);
                }
                // If randc, also emit markRandc() for cyclic tracking
                if (varp->isRandC()) markRandc(varp, smtName, initp);
            } else if (isClassRefArray && !memberselp) {
                createSolverArrayHandle(varp, elemClassRefDtp, classOrPackagep,
                                        isUnpackedClassRefArray, smtName);
            } else {
                createSolverVarHandle(varp, structSelOrCMeth, isGlobalConstrained, randMode,
                                      memberselp, smtName, classOrPackagep, classp, initp);
            }
        } else {
            // Variable already written, clean up cloned memberselp if any
            if (memberselp) VL_DO_DANGLING(memberselp->deleteTree(), memberselp);
            // Delete nodep if it's a global constraint (not deleted yet)
            if (isGlobalConstrained && !nodep->backp()) VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
        if (m_nestedAccessp) { VL_DO_DANGLING(delete m_nestedAccessp, m_nestedAccessp); }
    }
    // Build popcount expansion: (x & 1) + ((x & 2) >> 1) + ...
    // argp is consumed; caller must clone if reusing.
    AstNodeExpr* buildCountOnesExpansion(FileLine* fl, AstNodeExpr* argp) {
        const V3Number numOne{fl, argp->width(), 1};
        AstNodeExpr* sump = new AstAnd{fl, argp, new AstConst{fl, numOne}};
        sump->user1(true);
        for (int i = 1; i < argp->width(); i++) {
            V3Number numBitMask{fl, argp->width(), 0};
            numBitMask.setBit(i, 1);
            AstAnd* const andp
                = new AstAnd{fl, argp->cloneTreePure(false), new AstConst{fl, numBitMask}};
            andp->user1(true);
            AstShiftR* const shiftp
                = new AstShiftR{fl, andp,
                                new AstConst{fl, AstConst::WidthedValue{}, argp->width(),
                                             static_cast<uint32_t>(i)}};
            shiftp->user1(true);
            sump = new AstAdd{fl, sump, shiftp};
            sump->user1(true);
        }
        return sump;
    }

    void visit(AstCountOnes* nodep) override {
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* const argp = nodep->lhsp()->unlinkFrBack();
        AstNodeExpr* sump = buildCountOnesExpansion(fl, argp);
        sump = adjustWidth(fl, sump, nodep->width(), nodep->dtypep()->numeric());
        sump->user1(true);
        nodep->replaceWith(sump);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
        iterate(sump);
    }
    void visit(AstRedXor* nodep) override {
        if (editFormat(nodep)) return;

        // Build popcount expansion: (extract x 1 1) ^ (extract x 2 2) ^ ...
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* const argp = nodep->lhsp()->unlinkFrBack();

        AstNodeExpr* redxorp = new AstSel{fl, argp, 0, 1};
        redxorp->user1(true);
        for (int i = 1; i < argp->width(); i++) {
            AstSel* const selp = new AstSel{fl, argp->cloneTreePure(false), i, 1};
            selp->user1(true);

            redxorp = new AstXor{fl, redxorp, selp};
            redxorp->user1(true);
        }

        nodep->replaceWith(redxorp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
        iterate(redxorp);
    }
    void visit(AstRedAnd* nodep) override {
        if (editFormat(nodep)) return;
        // Convert to (~x == 0)
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* const argp = nodep->lhsp()->unlinkFrBack();
        const V3Number numZero{fl, argp->width(), 0};
        AstNodeExpr* const negp = new AstNot{fl, argp};
        negp->user1(true);
        AstNodeExpr* const eqp = new AstEq{fl, negp, new AstConst{fl, numZero}};
        eqp->user1(true);
        nodep->replaceWith(eqp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
        iterate(eqp);
    }
    void visit(AstRedOr* nodep) override {
        if (editFormat(nodep)) return;
        // Convert to (x != 0)
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* const argp = nodep->lhsp()->unlinkFrBack();
        const V3Number numZero{fl, argp->width(), 0};
        AstNodeExpr* const neqp = new AstNeq{fl, argp, new AstConst{fl, numZero}};
        neqp->user1(true);
        nodep->replaceWith(neqp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
        iterate(neqp);
    }
    void visit(AstOneHot* nodep) override {
        if (editFormat(nodep)) return;
        // $onehot(x) = (x != 0) && ((x & (x-1)) == 0)
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* const argp = nodep->lhsp()->unlinkFrBack();
        const int w = argp->width();

        const V3Number numZero{fl, w, 0};
        AstNeq* const neZerop
            = new AstNeq{fl, argp->cloneTreePure(false), new AstConst{fl, numZero}};
        neZerop->user1(true);

        const V3Number numOne{fl, w, 1};
        AstSub* const subp = new AstSub{fl, argp->cloneTreePure(false), new AstConst{fl, numOne}};
        subp->user1(true);

        AstAnd* const andp = new AstAnd{fl, argp, subp};
        andp->user1(true);

        const V3Number numZero2{fl, w, 0};
        AstEq* const eqZerop = new AstEq{fl, andp, new AstConst{fl, numZero2}};
        eqZerop->user1(true);

        AstLogAnd* const resultp = new AstLogAnd{fl, neZerop, eqZerop};
        resultp->user1(true);

        nodep->replaceWith(resultp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
        iterate(resultp);
    }
    void visit(AstOneHot0* nodep) override {
        if (editFormat(nodep)) return;
        // $onehot0(x) = (x & (x-1)) == 0
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* const argp = nodep->lhsp()->unlinkFrBack();
        const int w = argp->width();

        const V3Number numOne{fl, w, 1};
        AstSub* const subp = new AstSub{fl, argp->cloneTreePure(false), new AstConst{fl, numOne}};
        subp->dtypeFrom(argp);
        subp->user1(true);

        AstAnd* const andp = new AstAnd{fl, argp, subp};
        andp->dtypeFrom(argp);
        andp->user1(true);

        const V3Number numZero{fl, w, 0};
        AstEq* const eqp = new AstEq{fl, andp, new AstConst{fl, numZero}};
        eqp->user1(true);

        nodep->replaceWith(eqp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
        iterate(eqp);
    }
    void visit(AstCountBits* nodep) override {
        if (editFormat(nodep)) return;
        FileLine* const fl = nodep->fileline();

        bool countOnes = false;
        bool countZeros = false;
        for (AstNodeExpr* ctrlp : {nodep->rhsp(), nodep->thsp(), nodep->fhsp()}) {
            const AstConst* const cp = VN_CAST(ctrlp, Const);
            if (!cp) {
                nodep->v3warn(E_UNSUPPORTED,
                              "Unsupported: non-constant control in $countbits inside constraint");
                AstConst* const zerop
                    = new AstConst{fl, AstConst::WidthedValue{}, nodep->width(), 0U};
                nodep->replaceWith(zerop);
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
                return;
            }
            if (cp->num().bitIs1(0) && !countOnes)
                countOnes = true;
            else if (cp->num().bitIs0(0) && !countZeros)
                countZeros = true;
        }

        AstNodeExpr* const argp = nodep->lhsp()->unlinkFrBack();
        const int argWidth = argp->width();
        AstNodeExpr* sump = nullptr;
        if (countOnes && countZeros) {
            // ones + zeros = width for 2-state types
            sump = new AstConst{fl, AstConst::WidthedValue{}, nodep->width(), (uint32_t)argWidth};
            VL_DO_DANGLING(argp->deleteTree(), argp);
        } else if (countOnes) {
            sump = buildCountOnesExpansion(fl, argp);
        } else if (countZeros) {
            // width - countones(x)
            AstNodeExpr* const onesCountp = buildCountOnesExpansion(fl, argp);
            const V3Number widthVal{nodep, onesCountp->width(), (uint32_t)argWidth};
            sump = new AstSub{fl, new AstConst{fl, widthVal}, onesCountp};
            sump->user1(true);
        } else {
            sump = new AstConst{fl, AstConst::WidthedValue{}, nodep->width(), 0U};
            VL_DO_DANGLING(argp->deleteTree(), argp);
        }

        sump = adjustWidth(fl, sump, nodep->width(), nodep->dtypep()->numeric());
        sump->user1(true);

        nodep->replaceWith(sump);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
        iterate(sump);
    }
    void visit(AstCLog2* nodep) override {
        if (editFormat(nodep)) return;
        // $clog2(x): ITE chain (x<=1)?0 : (x<=2)?1 : ... : argWidth
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* const argp = nodep->lhsp()->unlinkFrBack();
        const int argWidth = argp->width();
        const int resultWidth = nodep->width();

        AstNodeExpr* resultp
            = new AstConst{fl, AstConst::WidthedValue{}, resultWidth, (uint32_t)argWidth};

        for (int k = argWidth - 1; k >= 0; k--) {
            V3Number threshold{fl, argWidth, 0};
            if (k < 32)
                threshold.setLong(1ULL << k);
            else
                threshold.setBit(k, 1);

            AstLte* const ltep
                = new AstLte{fl, argp->cloneTreePure(false), new AstConst{fl, threshold}};
            ltep->user1(true);

            AstConst* const valuep
                = new AstConst{fl, AstConst::WidthedValue{}, resultWidth, (uint32_t)k};

            resultp = new AstCond{fl, ltep, valuep, resultp};
            resultp->dtypeChgSigned(VSigning::SIGNED);
            resultp->user1(true);
        }

        VL_DO_DANGLING(argp->deleteTree(), argp);
        nodep->replaceWith(resultp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
        iterate(resultp);
    }
    void visit(AstIsUnbounded* nodep) override {
        // Only true for the literal '$' token, never a real expression, so
        // this always folds to false. It has no runtime implementation of
        // its own, so it must be substituted now rather than left for later.
        nodep->v3warn(CONSTRAINTIGN,
                      "Unsupported: $isunbounded() in a constraint, treating as constant");
        AstConst* const zerop = new AstConst{nodep->fileline(), AstConst::BitFalse{}};
        nodep->replaceWith(zerop);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
        // So the constant is rendered as an SMT literal like every other
        // folded constant here, instead of being left behind unconverted.
        iterate(zerop);
    }
    void handlePow(AstNodeBiop* nodep) {
        if (AstConst* const exponentp = VN_CAST(nodep->rhsp(), Const)) {
            FileLine* const fl = nodep->fileline();
            AstNodeExpr* const basep = nodep->lhsp();
            const V3Number numOne{nodep, basep->width(), 1};
            AstNodeExpr* powerp = new AstConst{fl, numOne};
            const bool baseSigned = VN_IS(nodep, PowSS) || VN_IS(nodep, PowSU);
            const int32_t exponent = baseSigned ? exponentp->toSInt() : exponentp->toUInt();
            if (exponent > 0) {
                for (int32_t i = 0; i < exponent; i++) {
                    if (baseSigned) {
                        powerp = new AstMulS{fl, powerp, basep->cloneTreePure(false)};
                    } else {
                        powerp = new AstMul{fl, powerp, basep->cloneTreePure(false)};
                    }
                    powerp->user1(true);
                }
            } else if (exponent < 0) {
                // Limit chain of divisions to max 2, because operations are on integers.
                // Two divisions are needed to preserve the sign.
                if (baseSigned) {
                    powerp = new AstDivS{fl, powerp, basep->cloneTreePure(false)};
                    powerp->user1(true);
                    powerp = new AstDivS{fl, powerp, basep->cloneTreePure(false)};
                    powerp->user1(true);
                } else {
                    powerp = new AstDiv{fl, powerp, basep->cloneTreePure(false)};
                    powerp->user1(true);
                }
            }
            nodep->replaceWith(powerp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            iterate(powerp);
        } else if (const AstConst* const basep = VN_CAST(nodep->lhsp(), Const)) {
            if (basep->num().toUInt() == 2) {
                // Non-constant exponent, base == 2: transform to shift-based SMT expression.
                // AstPow/AstPowSU (unsigned exponent): 2**n -> 1<<n
                // AstPowSS/AstPowUS (signed exponent): 2**n -> n>=0 ? 1<<n : 0
                // IEEE 1800-2023 ss11.4.3: integer base with negative exponent gives 0,
                // which ShiftL cannot represent; use SMT ite (AstCond -> bvsge + bvshl).
                FileLine* const fl = nodep->fileline();
                AstNodeExpr* const rhsp = nodep->rhsp()->unlinkFrBack();
                const int width = nodep->width();
                const bool rhsDependent = rhsp->user1();
                AstConst* const onep = new AstConst{fl, AstConst::WidthedValue{}, width, 1};
                AstShiftL* const shiftp = new AstShiftL{fl, onep, rhsp, width};
                shiftp->dtypeFrom(nodep);
                shiftp->user1(rhsDependent);
                AstNodeExpr* resultp = shiftp;
                if (VN_IS(nodep, PowSS) || VN_IS(nodep, PowUS)) {
                    // Signed exponent: guard 1<<n with n>=0 check
                    AstNodeExpr* const nClonep = rhsp->cloneTreePure(false);
                    nClonep->user1(rhsDependent);
                    AstConst* const zeroNp
                        = new AstConst{fl, AstConst::WidthedValue{}, rhsp->width(), 0};
                    AstGteS* const condp = new AstGteS{fl, nClonep, zeroNp};
                    condp->user1(rhsDependent);
                    AstConst* const zeroRp = new AstConst{fl, AstConst::WidthedValue{}, width, 0};
                    resultp = new AstCond{fl, condp, shiftp, zeroRp};
                    resultp->dtypeFrom(nodep);
                    resultp->user1(nodep->user1());
                }
                nodep->replaceWith(resultp);
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
                iterate(resultp);
            } else {
                nodep->v3warn(CONSTRAINTIGN,
                              "Unsupported: Power (**) expression with non-2 base in constraint");
            }
        } else {
            nodep->v3warn(
                CONSTRAINTIGN,
                "Unsupported: Power (**) expression with non-constant exponent in constraint");
        }
    }
    void visit(AstPow* nodep) override { handlePow(nodep); }
    void visit(AstPowSS* nodep) override { handlePow(nodep); }
    void visit(AstPowSU* nodep) override { handlePow(nodep); }
    void visit(AstPowUS* nodep) override { handlePow(nodep); }
    // SMT-LIB2 shift operations (bvshl/bvlshr/bvashr) require both operands
    // to have the same bitvector width. Extend the narrower operand, then
    // truncate the result if the value was widened. Never truncate the shift
    // amount, as large shifts must still shift out all of the original bits.
    void handleShift(AstNodeBiop* nodep) {
        if (editFormat(nodep)) return;
        const int lhsWidth = nodep->lhsp()->width();
        const int rhsWidth = nodep->rhsp()->width();
        if (rhsWidth < lhsWidth) {
            FileLine* const fl = nodep->fileline();
            AstNodeExpr* const rhsp = nodep->rhsp()->unlinkFrBack();
            AstExtend* const extendp = new AstExtend{fl, rhsp, lhsWidth};
            // Always visit the wrapper: a rand MemberSel can have user1 unset until its
            // own visitor translates it. Copying that flag would format the entire
            // extension from the pre-randomize value. Non-rand children are still
            // formatted as constants by their own visitors.
            extendp->user1(true);
            nodep->rhsp(extendp);
        } else if (rhsWidth > lhsWidth) {
            FileLine* const fl = nodep->fileline();
            AstNodeDType* const dtypep = nodep->dtypep();
            AstNodeExpr* const lhsp = nodep->lhsp()->unlinkFrBack();
            AstNodeExpr* const extendp
                = VN_IS(nodep, ShiftRS)
                      ? static_cast<AstNodeExpr*>(new AstExtendS{fl, lhsp, rhsWidth})
                      : static_cast<AstNodeExpr*>(new AstExtend{fl, lhsp, rhsWidth});
            // Likewise, visit the extension instead of prematurely formatting rand
            // member selections as constants.
            extendp->user1(true);
            nodep->lhsp(extendp);
            nodep->dtypeSetLogicSized(rhsWidth, dtypep->numeric());
            VNRelinker relinker;
            nodep->unlinkFrBack(&relinker);
            AstSel* const selp = new AstSel{fl, nodep, 0, lhsWidth};
            selp->dtypep(dtypep);
            selp->user1(nodep->user1());
            relinker.relink(selp);
            iterate(selp);
            return;
        }
        editSMT(nodep, nodep->lhsp(), nodep->rhsp());
    }
    void visit(AstShiftL* nodep) override { handleShift(nodep); }
    void visit(AstShiftR* nodep) override { handleShift(nodep); }
    void visit(AstShiftRS* nodep) override { handleShift(nodep); }
    void visit(AstNodeBiop* nodep) override {
        if (editFormat(nodep)) return;
        editSMT(nodep, nodep->lhsp(), nodep->rhsp());
    }
    void visit(AstNodeUniop* nodep) override {
        if (editFormat(nodep)) return;
        editSMT(nodep, nodep->lhsp());
    }
    void visit(AstNodeTriop* nodep) override {
        if (editFormat(nodep)) return;
        editSMT(nodep, nodep->lhsp(), nodep->rhsp(), nodep->thsp());
    }
    void visit(AstCond* nodep) override {
        if (editFormat(nodep)) return;
        if (!nodep->condp()->user1()) {
            // Do not burden the solver if cond computable: (cond ? "then" : "else")
            iterate(nodep->thenp());
            iterate(nodep->elsep());
            UASSERT_OBJ(
                nodep->thenp()->isString() && nodep->elsep()->isString(), nodep,
                "Branches of conditional expression in constraint not converted to strings");
            nodep->dtypeSetString();
            return;
        }
        // Fall back to "(ite cond then else)"
        visit(static_cast<AstNodeTriop*>(nodep));
    }
    void visit(AstReplicate* nodep) override {
        // Biop, but RHS is harmful
        if (editFormat(nodep)) return;
        editSMT(nodep, nodep->srcp());
    }
    void visit(AstSel* nodep) override {
        if (editFormat(nodep)) return;
        VNRelinker handle;
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* const msbp = new AstSFormatF{
            fl, "%1d", false,
            new AstAdd{fl, nodep->lsbp()->cloneTreePure(false),
                       new AstConst{fl, static_cast<uint32_t>(nodep->widthConst() - 1)}}};
        AstNodeExpr* const lsbp
            = new AstSFormatF{fl, "%1d", false, nodep->lsbp()->unlinkFrBack(&handle)};
        handle.relink(lsbp);

        editSMT(nodep, nodep->fromp(), lsbp, msbp);
    }
    void visit(AstStructSel* nodep) override {
        if (editFormat(nodep)) return;
        const bool outermost = !m_deferRandModeHoist;
        AstNodeExpr* const origp = outermost ? nodep->cloneTree(false) : nullptr;
        VL_RESTORER(m_structSel);
        m_structSel = true;
        if (VN_IS(nodep->fromp()->dtypep()->skipRefp(), StructDType)) {
            AstNodeExpr* const fromp = nodep->fromp();
            AstStructDType* const structp = VN_AS(fromp->dtypep()->skipRefp(), StructDType);
            markConstrainedRandMember(structp, nodep->name());
            if (isRandQualifiedPath(fromp)) {
                markStructConstrainedRandRecurse(fromp->dtypep());
            } else {
                structp->markConstrainedRand(true);
            }
        }
        // Mark Random for structArray
        if (VN_IS(nodep->fromp(), ArraySel) || VN_IS(nodep->fromp(), CMethodHard)) {
            AstNodeExpr* const fromp = VN_IS(nodep->fromp(), ArraySel)
                                           ? VN_AS(nodep->fromp(), ArraySel)->fromp()
                                           : VN_AS(nodep->fromp(), CMethodHard)->fromp();
            AstStructDType* const structp
                = VN_AS(fromp->dtypep()->skipRefp()->subDTypep()->skipRefp(), StructDType);
            markConstrainedRandMember(structp, nodep->name());
            if (isRandQualifiedPath(fromp)) {
                markStructConstrainedRandRecurse(fromp->dtypep()->skipRefp()->subDTypep());
            } else {
                structp->markConstrainedRand(true);
            }
        }
        {
            VL_RESTORER(m_deferRandModeHoist);
            m_deferRandModeHoist = true;
            iterateChildren(nodep);
        }
        FileLine* const fl = nodep->fileline();
        AstSFormatF* newp = nullptr;
        if (VN_AS(nodep->fromp(), SFormatF)->name() == "%s.%s") {
            newp = new AstSFormatF{fl, "%s.%s." + nodep->name(), false,
                                   VN_AS(nodep->fromp(), SFormatF)->exprsp()->cloneTreePure(true)};
            if (newp->exprsp()->nextp()->name().rfind("#x", 0) == 0)
                newp->exprsp()->nextp()->name("%x");  //  for #x%x to %x
        } else {
            newp = new AstSFormatF{fl, nodep->fromp()->name() + "." + nodep->name(), false,
                                   nullptr};
        }
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
        if (origp && !hoistRandModeOverSelectAndMember(newp, origp)) {
            VL_DO_DANGLING(pushDeletep(origp), origp);
        }
    }
    // Format of an array index or key in SMT names, normalized to standard bit widths
    static std::string keyHexFormat(const AstNodeDType* const keyDtp) {
        if (!keyDtp->isIntegralOrPacked()) return "%32x";  // String key
        const int width = keyDtp->width();
        if (width <= 8) return "%2x";
        if (width <= 16) return "%4x";
        return "%" + std::to_string(VL_WORDS_I(width) * 8) + "x";
    }
    void addStringNamePart(AstNodeExpr* const indexp, const std::string& fmt = "%32x") {
        if (m_nestedAccessp) {
            AstNodeExpr* const bitp = indexp->cloneTreePure(false);
            AstNodeExpr* const bitFormatp = new AstSFormatF{bitp->fileline(), fmt, false, bitp};
            AstSFormatF* const herep
                = new AstSFormatF{indexp->fileline(), "%s.%s", false, bitFormatp};
            m_nestedAccessp->addVarNamePart(herep, indexp->name());
        }
    }
    void visit(AstAssocSel* nodep) override {
        if (editFormat(nodep)) return;
        FileLine* const fl = nodep->fileline();
        // Keep a pre-edit clone for the rand_mode hoist below.
        AstNodeExpr* const origp = nodep->cloneTree(false);
        AstNodeExpr* const bitp = nodep->bitp();
        const AstNodeDType* const keyDtp = bitp->dtypep()->skipRefp();
        const bool keyIsPackedString = VN_IS(bitp, CvtPackString);
        const bool keyIsString = !keyIsPackedString && keyDtp->isString();
        const bool keyIsIntegral = keyDtp->isIntegralOrPacked();
        const bool elemMemberSel = VN_IS(nodep->backp(), MemberSel);
        AstAssocArrayDType* const assocDtp
            = VN_AS(nodep->fromp()->dtypep()->skipRefp(), AssocArrayDType);
        if (VN_IS(assocDtp->subDTypep()->skipRefp(), ClassRefDType)
            && (keyIsString || keyIsPackedString || keyIsIntegral) && !elemMemberSel) {
            AstNodeExpr* const arrayp = nodep->fromp()->unlinkFrBack();
            AstNodeExpr* const keyp = nodep->bitp()->unlinkFrBack();
            AstCMethodHard* const atp = new AstCMethodHard{fl, arrayp, VCMethod::ARRAY_AT, keyp};
            atp->dtypep(assocDtp->subDTypep()->skipRefp());
            AstCExpr* const handlep = new AstCExpr{fl, ""};
            handlep->add(atp);
            handlep->add(".operator->()");
            handlep->dtypep(nodep->findUInt64DType());
            nodep->replaceWith(getConstFormat(new AstCCast{fl, handlep, 64}));
            VL_DO_DANGLING(origp->deleteTree(), origp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            return;
        }
        AstSFormatF* newp = nullptr;
        if (keyIsString) {
            addStringNamePart(bitp);
            VNRelinker handle;
            AstNodeExpr* const idxp = new AstSFormatF{fl, (m_structSel ? "%32x" : "#x%32x"), false,
                                                      nodep->bitp()->unlinkFrBack(&handle)};
            handle.relink(idxp);
            newp = editSMT(nodep, nodep->fromp(), idxp);
        } else if (keyIsPackedString) {
            AstCvtPackString* const stringp = VN_AS(nodep->bitp(), CvtPackString);
            const size_t stringSize = VN_AS(stringp->lhsp(), Const)->width();
            if (stringSize > 128) {
                stringp->v3warn(
                    CONSTRAINTIGN,
                    "Unsupported: Constrained randomization of associative array keys of "
                        << stringSize << "bits, limit is 128 bits");
            }
            addStringNamePart(nodep->bitp());
            VNRelinker handle;
            AstNodeExpr* const idxp = new AstSFormatF{fl, (m_structSel ? "%32x" : "#x%32x"), false,
                                                      stringp->lhsp()->unlinkFrBack(&handle)};
            handle.relink(idxp);
            newp = editSMT(nodep, nodep->fromp(), idxp);
        } else {
            if (keyIsIntegral) {
                const std::string fmt = (m_structSel ? "" : "#x") + keyHexFormat(keyDtp);
                if (m_nestedAccessp) addStringNamePart(nodep->bitp(), fmt);
                VNRelinker handle;
                AstNodeExpr* const idxp
                    = new AstSFormatF{fl, fmt, false, nodep->bitp()->unlinkFrBack(&handle)};
                handle.relink(idxp);
                newp = editSMT(nodep, nodep->fromp(), idxp);
            } else {
                nodep->bitp()->v3error(
                    "Illegal non-integral expression or subexpression in random constraint."
                    " (IEEE 1800-2023 18.3)");
                if (m_nestedAccessp) m_nestedAccessp->error();
            }
        }
        if (newp && m_structSel && newp->name() == "(select %s %s)") { newp->name("%s.%s"); }
        if (!newp || !hoistRandModeOverSelectAndMember(newp, origp)) {
            VL_DO_DANGLING(origp->deleteTree(), origp);
        }
    }
    void renameArrayExpr(AstSFormatF* const newp) const {
        if (m_structSel) {
            newp->name("%s.%s");
            newp->exprsp()->nextp()->name("%x");
        }
    }
    void visit(AstArraySel* nodep) override {
        if (editFormat(nodep)) return;
        FileLine* const fl = nodep->fileline();
        VNRelinker handle;
        // Check if index actually references a rand variable (not just user1,
        // which can be over-marked in sum/with expansion contexts). A
        // std::randomize() with-clause argument carries no rand qualifier of
        // its own but is still part of the solve.
        bool indexIsRand = false;
        nodep->bitp()->foreach([&](const AstNodeVarRef* vrefp) {
            if (vrefp->varp()->rand().isRandomizable() || vrefp->varp()->isStdRandomizeArg()) {
                indexIsRand = true;
            }
        });
        if (m_nestedAccessp) {
            AstNodeExpr* const bitp = nodep->bitp()->cloneTreePure(false);
            AstNodeExpr* const bitFormatp
                = indexIsRand ? new AstSFormatF{bitp->fileline(), bitp->name(), false, nullptr}
                              : new AstSFormatF{bitp->fileline(), "%x", false, bitp};
            AstSFormatF* const herep
                = new AstSFormatF{nodep->fileline(), "%s.%s", false, bitFormatp};
            if (AstSel* const selp = VN_CAST(bitp, Sel)) {
                m_nestedAccessp->addVarNamePart(herep, selp->fromp()->name());
            } else {
                m_nestedAccessp->addVarNamePart(herep, bitp->name());
            }
            if (indexIsRand) {
                nodep->v3warn(E_UNSUPPORTED,
                              "Unsupported: Randomized index in complex expression");
                m_nestedAccessp->error();
                VL_DO_DANGLING(bitp->deleteTree(), bitp);
                return;
            }
        }
        if (indexIsRand) {
            // Index depends on rand variable -- keep as SMT symbol.
            // Array index sort is 32-bit, so zero-extend narrower indices.
            AstNodeExpr* indexp = nodep->bitp()->unlinkFrBack(&handle);
            if (indexp->width() < 32) {
                AstExtend* const extendp = new AstExtend{fl, indexp, 32};
                extendp->user1(true);
                indexp = extendp;
            }
            handle.relink(indexp);
            AstSFormatF* const newp = editSMT(nodep, nodep->fromp(), indexp);
            renameArrayExpr(newp);
        } else {
            // Index is constant or non-rand -- format as hex literal.
            // Keep a pre-edit clone for the rand_mode hoist below.
            AstNodeExpr* const origp = nodep->cloneTree(false);
            AstNodeExpr* const indexp
                = new AstSFormatF{fl, "#x%8x", false, nodep->bitp()->unlinkFrBack(&handle)};
            handle.relink(indexp);
            AstSFormatF* const newp = editSMT(nodep, nodep->fromp(), indexp);
            renameArrayExpr(newp);
            if (!newp || !hoistRandModeOverSelectAndMember(newp, origp)) {
                VL_DO_DANGLING(origp->deleteTree(), origp);
            }
        }
    }
    // True iff exprp is an ARRAY_AT read of a class's own instance mode array.
    static bool isRandModeGate(const AstNodeExpr* exprp) {
        const AstCMethodHard* const atp = VN_CAST(exprp, CMethodHard);
        if (!atp || atp->method() != VCMethod::ARRAY_AT) return false;
        const AstVar* varp = nullptr;
        if (const AstVarRef* const refp = VN_CAST(atp->fromp(), VarRef)) {
            varp = refp->varp();
        } else if (const AstMemberSel* const mselp = VN_CAST(atp->fromp(), MemberSel)) {
            varp = mselp->varp();
        }
        if (!varp) return false;
        const AstClass* const classp = VN_CAST(varp->user2p(), Class);
        return classp && classp->user2p() == varp;
    }
    // Lift a rand_mode Cond above the (select ...) chain of a frozen array element.
    bool hoistRandModeOverSelectAndMember(AstSFormatF* newp, AstNodeExpr* origp) {
        if (m_deferRandModeHoist) return false;
        // Only for selects yielding a non-array element (full chains)
        if (VN_IS(origp->dtypep()->skipRefp(), UnpackArrayDType)) return false;
        // Walk nested "(select %s %s)" frames down to a mode-gating AstCond
        std::vector<AstSFormatF*> frames;
        AstCond* modeCondp = nullptr;
        for (AstSFormatF* curp = newp;
             curp
             && (curp->name() == "(select %s %s)" || curp->name() == "%s.%s"
                 || curp->name().rfind("%s.", 0) == 0);) {
            AstNodeExpr* const firstp = curp->exprsp();
            frames.push_back(curp);
            if (AstCond* const condp = VN_CAST(firstp, Cond)) {
                if (isRandModeGate(condp->condp())) modeCondp = condp;
                break;
            }
            curp = VN_CAST(firstp, SFormatF);
        }
        if (!modeCondp) return false;
        FileLine* const fl = newp->fileline();
        AstNodeExpr* const modep = modeCondp->condp()->unlinkFrBack();
        AstNodeExpr* activep = modeCondp->thenp()->unlinkFrBack();
        // Rebuild the select chain text around the SMT name, innermost first
        for (auto it = frames.rbegin(); it != frames.rend(); ++it) {
            AstNodeExpr* const remainingArgsp = VN_CAST((*it)->exprsp()->nextp(), NodeExpr);
            if (remainingArgsp) { remainingArgsp->unlinkFrBackWithNext(); }
            activep = new AstSFormatF{fl, (*it)->name(), false,
                                      AstNode::addNext(activep, remainingArgsp)};
        }
        AstCond* const hoistp = new AstCond{fl, modep, activep, getConstFormat(origp)};
        hoistp->user1(true);  // Mark as formatted
        newp->replaceWith(hoistp);
        VL_DO_DANGLING(pushDeletep(newp), newp);
        return true;
    }
    void visit(AstMemberSel* nodep) override {
        // Check if rootVar is globalConstrained
        if (nodep->varp()->rand().isRandomizable() && nodep->fromp()) {
            FileLine* const fl = nodep->fileline();
            if (m_nestedAccessp) {
                AstSFormatF* const formatp = new AstSFormatF{fl, nodep->name(), false, nullptr};
                m_nestedAccessp->addVarNamePart(new AstSFormatF{fl, "%s.%s", false, formatp},
                                                nodep->name());
            }
            AstNode* rootNodep = nodep->fromp();
            while (const AstMemberSel* const selp = VN_CAST(rootNodep, MemberSel)) {
                rootNodep = selp->fromp();
            }

            AstNodeSel* arraySelp = VN_CAST(rootNodep, ArraySel);
            if (!arraySelp) arraySelp = VN_CAST(rootNodep, AssocSel);

            if (arraySelp) {
                AstNodeDType* const arrayDtp = arraySelp->fromp()->dtypep()->skipRefp();
                AstNodeDType* const elemDtp
                    = arrayDtp->subDTypep() ? arrayDtp->subDTypep()->skipRefp() : nullptr;
                if (elemDtp && VN_IS(elemDtp, ClassRefDType)) {
                    const bool isSimple
                        = nodep->fromp() == rootNodep && VN_IS(arraySelp->fromp(), VarRef);
                    if (!isSimple && !m_nestedAccessp) {
                        m_nestedAccessp = new NestedAccessPath(nodep->cloneTree(false),
                                                               &m_firstExpressionInsideIndexp);
                        AstSFormatF* const formatp
                            = new AstSFormatF{fl, nodep->name(), false, nullptr};
                        m_nestedAccessp->addVarNamePart(
                            new AstSFormatF{fl, "%s.%s", false, formatp}, nodep->name());
                    }
                    VL_RESTORER(m_structSel);
                    m_structSel = true;
                    nodep->user1(true);
                    arraySelp->user1(true);
                    AstNodeExpr* const origp = nodep->cloneTree(false);
                    iterateChildren(nodep);
                    AstSFormatF* const newp = new AstSFormatF{fl, "%s." + nodep->name(), false,
                                                              nodep->fromp()->unlinkFrBack()};
                    nodep->replaceWith(newp);
                    if (!hoistRandModeOverSelectAndMember(newp, origp))
                        VL_DO_DANGLING(origp->deleteTree(), origp);
                    VL_DO_DANGLING(pushDeletep(nodep), nodep);
                    VL_DO_DANGLING(delete m_nestedAccessp, m_nestedAccessp);
                    return;
                }
            }
            // Check if the root variable participates in global constraints
            if (const AstVarRef* const varRefp = VN_CAST(rootNodep, VarRef)) {
                AstVar* const constrainedVarp = varRefp->varp();
                if (constrainedVarp->globalConstrained()) {
                    bool const beforeIterate = m_nestedAccessp;
                    // Global constraint - unwrap the MemberSel
                    iterateChildren(nodep);
                    if (beforeIterate) {
                        nodep->replaceWith(new AstSFormatF{fl, "%s." + nodep->name(), false,
                                                           nodep->fromp()->unlinkFrBack()});
                    } else {
                        nodep->replaceWith(nodep->fromp()->unlinkFrBack());
                    }
                    VL_DO_DANGLING(nodep->deleteTree(), nodep);
                    return;
                }
            }
        }
        // Handle MemberSel references created by captureRefByThis()
        if (VN_IS(nodep->fromp(), VarRef)
            && nodep->fromp()->user1()  // Depending on a randomized variable
            && nodep->user2p()  // Pointer to containing module
            && VN_AS(nodep->user2p(), NodeModule) == nodep->varp()->user2p()) {
            // Convert to VarRef
            AstVarRef* const varRefp
                = new AstVarRef{nodep->fileline(), nodep->varp(), VAccess::READ};
            varRefp->user1(nodep->varp()->rand().isRandomizable());
            varRefp->classOrPackagep(VN_AS(nodep->user2p(), NodeModule));
            nodep->replaceWith(varRefp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            visit(varRefp);
        } else if (nodep->user1() && VN_IS(nodep->fromp(), CMethodHard)
                   && VN_AS(nodep->fromp(), CMethodHard)->method() == VCMethod::ARRAY_AT) {
            // Class ref array element member access (e.g., items[i].val)
            AstCMethodHard* const cmethodp = VN_AS(nodep->fromp(), CMethodHard);
            AstNodeDType* const arrayDtp = cmethodp->fromp()->dtypep()->skipRefp();
            AstNodeDType* const elemDtp = arrayDtp->subDTypep()->skipRefp();
            if (VN_IS(elemDtp, ClassRefDType)) {
                VL_RESTORER(m_structSel);
                m_structSel = true;
                iterateChildren(nodep);
                FileLine* const fl = nodep->fileline();
                AstSFormatF* newp = nullptr;
                if (AstSFormatF* const fromp = VN_CAST(nodep->fromp(), SFormatF)) {
                    if (fromp->name() == "%s.%s") {
                        newp = new AstSFormatF{fl, "%s.%s." + nodep->name(), false,
                                               fromp->exprsp()->cloneTreePure(true)};
                    } else {
                        newp = new AstSFormatF{fl, fromp->name() + "." + nodep->name(), false,
                                               nullptr};
                    }
                } else {
                    newp = new AstSFormatF{fl, nodep->name(), false, nullptr};
                }
                nodep->replaceWith(newp);
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
                return;
            }
            // Not a class ref element, fall through to normal handling
            iterateChildren(nodep);
            nodep->replaceWith(nodep->fromp()->unlinkFrBack());
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            return;
        } else if (nodep->user1()) {
            iterateChildren(nodep);
            nodep->replaceWith(nodep->fromp()->unlinkFrBack());
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            return;
        } else {
            editFormat(nodep);
        }
    }
    void visit(AstSFormatF* nodep) override {}
    void visit(AstStmtExpr* nodep) override {}
    void visit(AstCStmt* nodep) override {}
    void visit(AstIf* nodep) override {
        // Hoisted runtime-conditional disable_soft statements parked in the
        // constraint-items list by the pre-pass; already fully lowered.
    }
    void visit(AstConstraintIf* nodep) override {
        // Outside a fold, this if's branches are folded here and m_constraintVars collects
        // their names for the constraint replacing it; a nested if adds to its parent's fold
        const bool foldOwner = !m_wantSingle;
        UASSERT_OBJ(!foldOwner || m_constraintVars.empty(), nodep,
                    "Constraint names of an earlier fold were not taken over");
        AstNodeExpr* newp = nullptr;
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* const thenp = editSingle(fl, nodep->thensp());
        AstNodeExpr* const elsep = editSingle(fl, nodep->elsesp());
        if (thenp && elsep) {
            newp = new AstCond{fl, nodep->condp()->unlinkFrBack(), thenp, elsep};
        } else if (thenp) {
            newp = new AstLogIf{fl, nodep->condp()->unlinkFrBack(), thenp};
        } else if (elsep) {
            newp = new AstLogIf{fl, new AstNot{fl, nodep->condp()->unlinkFrBack()}, elsep};
        }
        if (newp) {
            newp->dtypeSetBit();  // Result is boolean (prevents bare-var != 0 wrapping)
            newp->user1(true);  // Assume result-dependent
            AstConstraintExpr* const exprp = new AstConstraintExpr{fl, newp};
            nodep->replaceWith(exprp);
            // Iterated next (AstNode::iterateAndNext), and takes over the folded names
            if (foldOwner) m_foldTakerp = exprp;
        } else {
            nodep->unlinkFrBack();
        }
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstGenBlock* nodep) override {
        // Dubious but this is what we used to do. Does that mean no randomzie
        // methods work under a generage block?
    }
    void visit(AstBegin* nodep) override {}
    void visit(AstConstraintForeach* nodep) override {
        // Convert to plain foreach
        FileLine* const fl = nodep->fileline();

        if (!nodep->bodyp()) {
            nodep->unlinkFrBack();
        } else if (m_wantSingle) {
            AstNodeExpr* const itemp = editSingle(fl, nodep->bodyp());
            AstVar* const textVarp = newTextVarp(nodep);
            AstNodeStmt* const bodyp
                = prependDistPreamble(nodep, newTermAppendp(fl, textVarp, itemp));
            nodep->replaceWith(newTextBuildp(
                fl, textVarp, "", new AstForeach{fl, nodep->headerp()->unlinkFrBack(), bodyp},
                newTextApplyp(fl, textVarp, "bvand", "#b1")));
        } else {
            VL_RESTORER(m_foreachp);
            VL_RESTORER_COPY(m_foreachIdxVars);
            m_foreachp = nodep;
            for (AstNode* elemp = nodep->headerp()->elementsp(); elemp; elemp = elemp->nextp()) {
                if (const AstVar* const varp = VN_CAST(elemp, Var)) m_foreachIdxVars.insert(varp);
            }
            iterateAndNextNull(nodep->bodyp());
            AstNodeStmt* const bodyp
                = prependDistPreamble(nodep, nodep->bodyp()->unlinkFrBackWithNext());
            nodep->replaceWith(
                new AstBegin{fl, m_uniqueNames.get("__VrandBlock"),
                             new AstForeach{fl, nodep->headerp()->unlinkFrBack(), bodyp}, true});
        }
        UASSERT_OBJ(!nodep->user3p(), nodep, "Dist bucket preamble not injected into foreach");
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstConstraintBefore* nodep) override {
        // Generate solveBefore() calls for each (lhs, rhs) variable pair.
        // Do NOT iterate children -- these are variable references, not constraint expressions.
        FileLine* const fl = nodep->fileline();
        AstNodeModule* const genModp = VN_AS(m_genp->user2p(), NodeModule);

        for (AstNodeExpr* lhsp = nodep->lhssp(); lhsp; lhsp = VN_CAST(lhsp->nextp(), NodeExpr)) {
            AstNodeExpr* const lhsTestp = buildSolveBeforeNameExpr(fl, lhsp);
            if (!lhsTestp) {
                lhsp->v3fatalSrc("Unexpected expression type in solve...before lhs");
                continue;
            }
            VL_DO_DANGLING(lhsTestp->deleteTree(), lhsTestp);
            for (AstNodeExpr* rhsp = nodep->rhssp(); rhsp;
                 rhsp = VN_CAST(rhsp->nextp(), NodeExpr)) {
                AstNodeExpr* const rhsNamep = buildSolveBeforeNameExpr(fl, rhsp);
                if (!rhsNamep) {
                    rhsp->v3fatalSrc("Unexpected expression type in solve...before rhs");
                    continue;
                }
                AstCMethodHard* const callp = new AstCMethodHard{
                    fl, new AstVarRef{fl, genModp, m_genp, VAccess::READWRITE},
                    VCMethod::RANDOMIZER_SOLVE_BEFORE};
                callp->dtypeSetVoid();
                callp->addPinsp(buildSolveBeforeNameExpr(fl, lhsp));
                callp->addPinsp(rhsNamep);
                nodep->addHereThisAsNext(callp->makeStmt());
            }
        }
        VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
    }
    void visit(AstConstraintUnique* nodep) override {
        FileLine* const fl = nodep->fileline();

        AstBegin* initp;
        AstVar* genVarp;
        AstNodeModule* genModp = nullptr;
        if (m_inlineInitBlockp) {
            // A randomize() with {} inline block's own per-invocation
            // function/generator, as every other write_var call site in this
            // visitor already uses. Registering there instead of unconditionally
            // into the class's constructor/persistent generator lets the
            // registration re-run on every call, seeing the array's current
            // (possibly just-resolved-this-call) size, rather than freezing it at
            // construction time. Its generator is a function-local var referenced
            // directly, with no module qualifier (genModp stays null).
            initp = m_inlineInitBlockp;
            genVarp = m_genp;
        } else {
            initp = newInitBlockp(VN_AS(m_memberMap.findMember(m_classp, "new"), NodeFTask));
            genVarp = SmtUtil::getRandomGenerator(m_classp);
            UASSERT_OBJ(genVarp, nodep, "No generator variable");
            genModp = VN_AS(genVarp->user2p(), NodeModule);
            UASSERT_OBJ(genModp, nodep, "genVarp has no NodeModule set");
        }
        // Every remaining ConstraintExprVisitor construction site passes a non-null
        // genp whenever m_classp is set (class-level: only reached inside
        // `if (genp) {...}` in visit(AstClass*); with{}-block: always a freshly
        // created local generator var), so genVarp can no longer be null here.
        UASSERT_OBJ(genVarp, nodep, "No generator variable");
        const auto genVarRefp = [&](VAccess access) -> AstVarRef* {
            return genModp ? new AstVarRef{fl, genModp, genVarp, access}
                           : new AstVarRef{fl, genVarp, access};
        };

        // Registration calls emitted where the unique statement stood, so they end up
        // in the constraint setup task and re-run on every randomize()
        AstNode* setupStmtsp = nullptr;
        // Under a condition the distinctness must instead become part of the guarded
        // constraint expression, which needs an element count known at verilation time
        std::vector<std::string> smtExprs;
        for (AstNode* const itemp : nodep->rangespList()) {
            if (AstVarRef* const varRefp = VN_CAST(itemp, VarRef)) {
                AstVar* const varp = varRefp->varp();
                AstNodeModule* const varModp = VN_AS(varp->user2p(), NodeModule);
                UASSERT_OBJ(varModp, nodep, "varp has no NodeModule set");
                AstNodeDType* const dtypep = varp->dtypep()->skipRefp();

                const static auto dynDTypeSupported
                    = [](const AstNodeDType* const dtypep) -> bool {
                    return VN_IS(dtypep, DynArrayDType) || VN_IS(dtypep, QueueDType)
                           || VN_IS(dtypep, AssocArrayDType);
                };

                // Establish it is an array before asking for its element type
                uint64_t elemWidth;
                uint32_t staticSize = 0;  // Element count, zero when only known at run time
                if (const AstUnpackArrayDType* const up = VN_CAST(dtypep, UnpackArrayDType)) {
                    const AstRange* const rangep = up->rangep();
                    UASSERT_OBJ(rangep && VN_IS(rangep->leftp(), Const)
                                    && VN_IS(rangep->rightp(), Const),
                                nodep, "Unpack array does not have a constant range");
                    staticSize = up->elementsConst();
                    if (staticSize > 100) {
                        nodep->v3warn(
                            CONSTRAINTIGN,
                            "Unsupported: Unique constraint on static arrays of size > 100");
                        continue;
                    }
                    elemWidth = static_cast<uint64_t>(varp->dtypep()->width());
                } else if (dynDTypeSupported(dtypep)) {
                    elemWidth = static_cast<uint64_t>(dtypep->subDTypep()->width());
                } else {
                    nodep->v3warn(CONSTRAINTIGN, "Unsupported: Unique constraint on "
                                                     << dtypep->prettyDTypeName(false));
                    continue;
                }

                // Ensure it is ONLY 1-D by checking that the element type is not an array/queue
                const AstNodeDType* const subp = dtypep->subDTypep()->skipRefp();
                if (VN_IS(subp, NodeArrayDType) || VN_IS(subp, QueueDType)
                    || VN_IS(subp, DynArrayDType) || VN_IS(subp, AssocArrayDType)
                    || VN_IS(subp, WildcardArrayDType)) {
                    nodep->v3warn(CONSTRAINTIGN,
                                  "Unsupported: Unique constraint on multidimensional arrays");
                    continue;
                }

                if (m_wantSingle && !staticSize) {
                    nodep->v3warn(CONSTRAINTIGN,
                                  "Unsupported: Unique constraint on dynamically sized array "
                                  "inside conditional constraint");
                    continue;
                }

                // A with{}-block's own registration must use the per-instance
                // m_inlineWrittenVars (fresh for each ConstraintExprVisitor pass), not
                // the permanent, compile-time-once AstVar::user3() -- otherwise a
                // unique{} target that isn't itself size-constrained (so the two-phase
                // solve's manual refresh loop doesn't cover it) never gets write_var'd
                // again on the second pass, once the class generator copy in between
                // has dropped its first-pass registration. This mirrors the general
                // (non-unique) write_var dedup a few hundred lines up, which already
                // makes exactly this distinction.
                const bool alreadyWritten = m_inlineInitBlockp
                                                ? m_inlineWrittenVars.count(varp->name()) > 0
                                                : varp->user3();
                if (!alreadyWritten) {
                    varp->user3(true);  // Solver owns it; __VBasicRand must not overwrite
                    if (m_inlineInitBlockp) m_inlineWrittenVars.insert(varp->name());
                    // Convert to C string
                    AstNodeExpr* const varnamep = new AstCExpr{
                        fl, AstCExpr::Pure{}, "\"" + varp->name() + "\"", varp->width()};

                    AstCMethodHard* const writeVarCallp = new AstCMethodHard{
                        fl, genVarRefp(VAccess::READ), VCMethod::RANDOMIZER_WRITE_VAR};
                    AstVarRef* const argVarRefp = new AstVarRef{fl, varp, VAccess::READ};
                    if (m_classp) argVarRefp->classOrPackagep(varModp);
                    writeVarCallp->addPinsp(argVarRefp);
                    writeVarCallp->addPinsp(new AstConst{fl, AstConst::Unsized64{}, elemWidth});
                    writeVarCallp->addPinsp(varnamep);
                    writeVarCallp->addPinsp(new AstConst{fl, 1});  // Dimension
                    const RandomizeMode randMode = {.asUQuad = varp->user1()};
                    if (randMode.usesMode) {
                        writeVarCallp->addPinsp(
                            new AstConst{fl, AstConst::Unsized64{}, randMode.index});
                    }
                    writeVarCallp->dtypeSetVoid();
                    initp->addStmtsp(new AstStmtExpr{fl, writeVarCallp});
                }

                // A solver-sized container is resized between solve passes; joining the
                // size-constrained set gets its element table refreshed in between
                if (varp->user4p() && m_sizeConstrainedArraysp) {
                    m_sizeConstrainedArraysp->insert(varp);
                }

                if (m_wantSingle) {
                    // Fewer than two elements are trivially distinct
                    if (staticSize < 2) continue;
                    // Named in the text below, so the folded constraint must record it too.
                    // Visited from the if's fold, outside any constraint expression, so
                    // m_constraintVarsp is not set: add to the fold's names directly
                    m_constraintVars.insert(varp->name());
                    std::string exprStr = "(__Vbv (distinct";
                    for (uint32_t i = 0; i < staticSize; ++i) {
                        exprStr += " (select " + varp->name() + " #x";
                        for (int shift = 28; shift >= 0; shift -= 4) {
                            exprStr += "0123456789abcdef"[(i >> shift) & 0xf];
                        }
                        exprStr += ')';
                    }
                    smtExprs.emplace_back(exprStr + "))");
                    continue;
                }

                AstNodeExpr* const namep = new AstConst{fl, AstConst::String{}, varp->name()};
                AstCMethodHard* const randUniqueCallp = new AstCMethodHard{
                    fl, genVarRefp(VAccess::READ), VCMethod::RANDOMIZER_UNIQUE, namep};
                randUniqueCallp->dtypep(nodep->findVoidDType());
                randUniqueCallp->addPinsp(new AstConst{fl, *m_uniqueConstraintIdp});
                setupStmtsp = AstNode::addNext(setupStmtsp, new AstStmtExpr{fl, randUniqueCallp});
            }
        }
        ++(*m_uniqueConstraintIdp);
        if (m_wantSingle && !smtExprs.empty()) {
            std::string exprStr = smtExprs.front();
            if (smtExprs.size() > 1) {
                exprStr = "(bvand";
                for (const std::string& oneExprp : smtExprs) exprStr += " " + oneExprp;
                exprStr += ')';
            }
            AstSFormatF* const newp = new AstSFormatF{fl, exprStr, false, nullptr};
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            return;
        }
        if (setupStmtsp) nodep->addHereThisAsNext(setupStmtsp);
        nodep->unlinkFrBack();
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    void visit(AstConstraintExpr* nodep) override {
        // IEEE 1800-2023 18.5.13: 'disable soft' is a meta-level directive on
        // the constraint graph, lowered to a void RANDOMIZER_DISABLE_SOFT
        // call.  Conditional occurrences (if / foreach / implication body)
        // are rewritten by extractConditionalDisableSofts() before this
        // visitor runs, so anything we see here is unconditional.
        VL_RESTORER(m_firstExpressionInsideIndexp);
        // Outside a fold this constraint is emitted here with only its own names: those it
        // records, plus the folded names when it replaces an if (see visit(AstConstraintIf*))
        std::set<std::string> vars;
        if (!m_wantSingle) {
            if (nodep == m_foldTakerp) {
                vars.swap(m_constraintVars);
                m_foldTakerp = nullptr;
            }
            UASSERT_OBJ(m_constraintVars.empty(), nodep,
                        "Constraint names carried over from another constraint");
        }
        VL_RESTORER(m_constraintVarsp);
        m_constraintVarsp = m_wantSingle ? &m_constraintVars : &vars;
        if (nodep->isDisableSoft()) {
            nodep->replaceWith(buildDisableSoftCallStmt(nodep));
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            return;
        }
        // IEEE 1800-2023 18.5.1: A bare expression used as a constraint is
        // implicitly treated as "expr != 0" when wider than 1 bit.
        // Must wrap before iterateChildren, which converts to SMT format.
        {
            AstNodeExpr* const exprp = nodep->exprp();
            if (exprp->width() > 1) {
                FileLine* const fl = exprp->fileline();
                const V3Number numZero{fl, exprp->width(), 0};
                AstNodeExpr* const neqp
                    = new AstNeq{fl, exprp->unlinkFrBack(), new AstConst{fl, numZero}};
                neqp->user1(true);  // Mark as rand-dependent for SMT path
                nodep->exprp(neqp);
            }
        }
        iterateChildren(nodep);
        if (m_wantSingle) {
            nodep->replaceWith(nodep->exprp()->unlinkFrBack());
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            return;
        }
        // Emit as soft or hard constraint per IEEE 1800-2023 18.5.13
        const VCMethod method
            = nodep->isSoft() ? VCMethod::RANDOMIZER_SOFT : VCMethod::RANDOMIZER_HARD;
        AstCMethodHard* const callp = new AstCMethodHard{
            nodep->fileline(),
            new AstVarRef{nodep->fileline(), VN_AS(m_genp->user2p(), NodeModule), m_genp,
                          VAccess::READWRITE},
            method, nodep->exprp()->unlinkFrBack()};
        callp->dtypeSetVoid();
        if (method == VCMethod::RANDOMIZER_HARD) {
            // hard() pin layout is asserted in EmitCFunc: the variable list is always pin 2
            callp->addPinsp(
                new AstCExpr{nodep->fileline(), AstCExpr::Pure{}, constraintVarsList(vars)});
        }
        // Pass filename, lineno, and source as separate arguments
        // This allows EmitC to call protect() on filename, similar to VL_STOP
        // Add filename parameter
        callp->addPinsp(new AstCExpr{nodep->fileline(), AstCExpr::Pure{},
                                     "\"" + nodep->fileline()->filename() + "\""});
        // Add line number parameter
        const uint32_t lineno = static_cast<uint32_t>(nodep->fileline()->lineno());
        callp->addPinsp(new AstConst{nodep->fileline(), lineno});
        // Add source text parameter (empty if --protect-ids to avoid source leakage)
        std::string prettyText;
        if (!v3Global.opt.protectIds()) {
            prettyText = nodep->fileline()->prettySource();
            size_t pos = 0;
            while ((pos = prettyText.find('"', pos)) != std::string::npos) {
                prettyText.insert(pos, "\\");
                pos += std::strlen("\\\"");
            }
        }
        callp->addPinsp(
            new AstCExpr{nodep->fileline(), AstCExpr::Pure{}, "\"" + prettyText + "\""});
        nodep->replaceWith(callp->makeStmt());
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstCMethodHard* nodep) override {
        if (editFormat(nodep)) return;
        FileLine* const fl = nodep->fileline();

        if (nodep->method() == VCMethod::ARRAY_AT) {
            addStringNamePart(nodep->pinsp(), "%x");
            const bool indexIsRand = nodep->pinsp()->exists([](const AstNodeVarRef* const vrefp) {
                return vrefp->varp()->rand().isRandomizable();
            });
            if (nodep->fromp()->user1()) {
                // Queue/dynamic element: pre-edit clone for the rand_mode hoist, non-rand index
                // only. A std::randomize() with-clause argument carries no rand qualifier of its
                // own but is still part of the solve.
                {
                    const AstNode* const basep = nodep->baseFromp(true);
                    if (basep->name() == "__Vthis"
                        && VN_AS(basep->backp(), MemberSel)->varp()->isRand()) {
                        nodep->fromp()->v3warn(E_UNSUPPORTED,
                                               "Unsupported: Complex expression captured from "
                                               "current scope with randomized variable");
                        return;
                    }
                }
                AstNodeExpr* const origp = indexIsRand ? nullptr : nodep->cloneTree(false);
                const AstVarRef* const baseRefp
                    = m_structSel ? VN_CAST(nodep->fromp()->baseFromp(true), VarRef) : nullptr;
                if (baseRefp && VN_IS(nodep->pinsp(), Const)
                    && VN_IS(baseRefp->varp()->dtypep()->skipRefp(), DynArrayDType)
                    && m_prepareConstrainedArraysp) {
                    AstNodeExpr* const indexp = nodep->pinsp()->cloneTreePure(false);
                    AstNodeExpr* const arrayp = nodep->fromp()->cloneTreePure(false);
                    AstCMethodHard* const currentSizep
                        = new AstCMethodHard{fl, arrayp->cloneTreePure(false), VCMethod::DYN_SIZE};
                    currentSizep->dtypeSetInt();
                    AstNodeExpr* const inRangeRequiredp = new AstLogAnd{
                        fl,
                        new AstLteS{fl,
                                    new AstConst{fl, AstConst::WidthedValue{}, indexp->width(), 0},
                                    indexp->cloneTreePure(false)},
                        new AstGteS{fl, indexp->cloneTreePure(false), currentSizep}};
                    AstCMethodHard* const resizep
                        = new AstCMethodHard{fl, arrayp, VCMethod::DYN_RESIZE,
                                             new AstAdd{fl, indexp, new AstConst{fl, 1}}};
                    resizep->dtypeSetVoid();
                    m_prepareConstrainedArraysp->addStmtsp(
                        new AstIf{fl, inRangeRequiredp, resizep->makeStmt()});
                }
                AstCMethodHard* const sizep
                    = m_structSel ? new AstCMethodHard{fl, nodep->fromp()->cloneTreePure(false),
                                                       VCMethod::DYN_SIZE}
                                  : nullptr;
                AstNodeExpr* const originalPinp = nodep->pinsp();
                iterateChildren(nodep);
                AstNodeExpr* const pinp = nodep->pinsp()->unlinkFrBack();
                AstSFormatF* newp;
                if (m_structSel) {
                    if (AstSFormatF* const sformatfp = VN_CAST(pinp, SFormatF)) {
                        sformatfp->name("%x");
                    }
                    AstNodeExpr* const argsp
                        = AstNode::addNext(nodep->fromp()->unlinkFrBack(), pinp);
                    sizep->dtypeSetInt();
                    AstLogAnd* const condp
                        = new AstLogAnd{fl,
                                        new AstLteS{fl,
                                                    new AstConst{fl, AstConst::WidthedValue{},
                                                                 originalPinp->width(), 0},
                                                    originalPinp->cloneTreePure(false)},
                                        new AstLtS{fl, originalPinp->cloneTreePure(false), sizep}};
                    m_conditionp = m_conditionp ? new AstLogAnd{fl, m_conditionp, condp} : condp;
                    newp = new AstSFormatF{fl, "%s.%s", false, argsp};
                } else {
                    newp = createSolverArrDerefp(fl, nodep->fromp()->unlinkFrBack(), pinp);
                }
                nodep->replaceWith(newp);
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
                if (origp && !hoistRandModeOverSelectAndMember(newp, origp)) {
                    VL_DO_DANGLING(origp->deleteTree(), origp);
                }

            } else if (indexIsRand) {
                nodep->v3warn(E_UNSUPPORTED,
                              "Unsupported: Randomization of an index to a non-random variable");

            } else {
                nodep->user1(false);
                UASSERT_OBJ(editFormat(nodep), nodep,
                            "editFormat should return true when user1 is false");
            }
            return;
        }

        if (nodep->method() == VCMethod::ARRAY_INSIDE) {
            const bool randArr = nodep->fromp()->user1();

            AstVar* const newVarp
                = new AstVar{fl, VVarType::BLOCKTEMP, "__Vinside", nodep->findIntDType()};
            AstNodeExpr* const idxRefp = new AstVarRef{nodep->fileline(), newVarp, VAccess::READ};
            AstForeachHeader* const headerp
                = new AstForeachHeader{fl, nodep->fromp()->cloneTreePure(false), newVarp};
            AstNodeExpr* const selp = newSel(nodep->fileline(), nodep->fromp(), idxRefp);
            selp->user1(randArr);
            AstNode* const itemp = new AstEq{fl, selp, nodep->pinsp()->unlinkFrBack()};
            itemp->user1(true);

            AstVar* const textVarp = newTextVarp(nodep);
            AstStmtExpr* const appendp
                = newTermAppendp(fl, textVarp, VN_AS(iterateSubtreeReturnEdits(itemp), NodeExpr));
            nodep->replaceWith(newTextBuildp(fl, textVarp, "",
                                             new AstForeach{fl, headerp, appendp},
                                             newTextApplyp(fl, textVarp, "bvor", "#b0")));
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            return;
        }

        // Array reduction methods (sum, product, and, or, xor)
        if (nodep->method() == VCMethod::ARRAY_R_SUM
            || nodep->method() == VCMethod::ARRAY_R_PRODUCT
            || nodep->method() == VCMethod::ARRAY_R_AND || nodep->method() == VCMethod::ARRAY_R_OR
            || nodep->method() == VCMethod::ARRAY_R_XOR) {

            AstWith* const withp = nodep->withp();

            // For 'with' clause: check array size limit and item.index support
            if (withp) {
                if (AstUnpackArrayDType* const adtypep
                    = VN_CAST(nodep->fromp()->dtypep()->skipRefp(), UnpackArrayDType)) {
                    const int arraySize = adtypep->elementsConst();
                    if (arraySize > v3Global.opt.constraintArrayLimit()) {
                        nodep->v3warn(CONSTRAINTIGN,
                                      "Constraint array reduction ignored (array size "
                                          + cvtToStr(arraySize)
                                          + " exceeds --constraint-array-limit of "
                                          + cvtToStr(v3Global.opt.constraintArrayLimit())
                                          + "), treating as state");
                        nodep->user1(false);
                        if (editFormat(nodep)) return;
                        nodep->v3fatalSrc("Method not handled in constraints? " << nodep);
                        return;
                    }
                }
            }

            // For without 'with' clause: need random array for variable registration
            const bool hasRandomArray = nodep->fromp()->user1();
            if (!withp && !hasRandomArray) {
                // No 'with' clause and not a random array - can't handle
                nodep->v3warn(CONSTRAINTIGN,
                              "Unsupported: randomizing this expression, treating as state");
                nodep->user1(false);
                if (editFormat(nodep)) return;
                nodep->v3fatalSrc("Method not handled in constraints? " << nodep);
                return;
            }
            if (!VN_IS(nodep->fromp(), VarRef)) {
                // Non-dynamic subarrays and member arrays are handled in other parts of code
                nodep->v3warn(CONSTRAINTIGN, "Unsupported: Array reduction constraint on dynamic "
                                             "array inside array or struct");
                return;
            }

            // Create loop variable and header
            AstVar* const loopVarp
                = new AstVar{fl, VVarType::BLOCKTEMP, "__Vreduce", nodep->findIntDType()};
            AstForeachHeader* const headerp
                = new AstForeachHeader{fl, nodep->fromp()->cloneTreePure(false), loopVarp};

            // Determine SMT operation and compute identity elements
            const char* smtOp = nullptr;
            std::string identity;
            if (withp) {
                // For 'with' clause: use binary format, compute from result width
                const int width = nodep->dtypep()->width();
                if (nodep->method() == VCMethod::ARRAY_R_SUM) {
                    smtOp = "bvadd";
                    identity = "#b" + std::string(width, '0');
                } else if (nodep->method() == VCMethod::ARRAY_R_PRODUCT) {
                    smtOp = "bvmul";
                    identity = (width > 0) ? "#b" + std::string(width - 1, '0') + "1" : "#b0";
                } else if (nodep->method() == VCMethod::ARRAY_R_AND) {
                    smtOp = "bvand";
                    identity = "#b" + std::string(width, '1');
                } else if (nodep->method() == VCMethod::ARRAY_R_OR) {
                    smtOp = "bvor";
                    identity = "#b" + std::string(width, '0');
                } else {  // ARRAY_R_XOR
                    smtOp = "bvxor";
                    identity = "#b" + std::string(width, '0');
                }
            } else {
                // For without 'with' clause: use hex format, compute from element width
                AstVarRef* const arrRefp = VN_CAST(nodep->fromp(), VarRef);
                UASSERT_OBJ(arrRefp, nodep, "Array reduction in constraint has non-VarRef source");
                AstVar* const arrVarp = arrRefp->varp();
                AstNodeDType* elemDtp = arrVarp->dtypep()->skipRefp()->subDTypep();
                const int elemWidth = elemDtp->width();
                const int hexDigits = (elemWidth + 3) / 4;

                const std::string zeroIdentity = "#x" + std::string(hexDigits, '0');
                const std::string oneIdentity = "#x" + std::string(hexDigits - 1, '0') + "1";
                const std::string allOnesIdentity = "#x" + std::string(hexDigits, 'f');

                if (nodep->method() == VCMethod::ARRAY_R_SUM) {
                    smtOp = "bvadd";
                    identity = zeroIdentity;
                } else if (nodep->method() == VCMethod::ARRAY_R_PRODUCT) {
                    smtOp = "bvmul";
                    identity = oneIdentity;
                } else if (nodep->method() == VCMethod::ARRAY_R_AND) {
                    smtOp = "bvand";
                    identity = allOnesIdentity;
                } else if (nodep->method() == VCMethod::ARRAY_R_OR) {
                    smtOp = "bvor";
                    identity = zeroIdentity;
                } else {  // ARRAY_R_XOR
                    smtOp = "bvxor";
                    identity = zeroIdentity;
                }
            }

            // Build loop body based on whether we have a 'with' clause
            AstVar* const textVarp = newTextVarp(nodep);
            AstNodeStmt* bodyp;
            if (withp) {
                // With 'with' clause: evaluate expression for each element
                const bool randArr = nodep->fromp()->user1();
                AstNodeExpr* const idxRefp = new AstVarRef{fl, loopVarp, VAccess::READ};
                AstNodeExpr* const elemSelp = newSel(fl, nodep->fromp(), idxRefp);
                elemSelp->user1(randArr);

                // Get the result width for the reduction
                const int resultWidth = nodep->dtypep()->width();
                const VSigning resultSigning = nodep->dtypep()->numeric();

                AstNode* perElemExprp = withp->exprp()->cloneTreePure(false);
                if (AstLambdaArgRef* const rootRefp = VN_CAST(perElemExprp, LambdaArgRef)) {
                    if (rootRefp->index()) {
                        // item.index at root -> replace with loop variable, adjust width
                        AstVarRef* const loopRefp = new AstVarRef{fl, loopVarp, VAccess::READ};
                        perElemExprp = adjustWidth(fl, loopRefp, resultWidth, resultSigning);
                    } else {
                        // item at root -> replace with array element
                        perElemExprp = elemSelp->cloneTreePure(false);
                    }
                    VL_DO_DANGLING(rootRefp->deleteTree(), rootRefp);
                } else {
                    perElemExprp->foreach([&](AstLambdaArgRef* refp) {
                        if (refp->index()) {
                            // item.index -> replace with loop variable, adjust width
                            AstVarRef* const loopRefp = new AstVarRef{fl, loopVarp, VAccess::READ};
                            AstNode* const replacementp
                                = adjustWidth(fl, loopRefp, resultWidth, resultSigning);
                            refp->replaceWith(replacementp);
                        } else {
                            // item -> replace with array element
                            refp->replaceWith(elemSelp->cloneTreePure(false));
                        }
                        VL_DO_DANGLING(pushDeletep(refp), refp);
                    });
                }
                VL_DO_DANGLING(elemSelp->deleteTree(), elemSelp);

                // enum-literal folding pass already ran -- re-fold the literals.
                perElemExprp = V3Const::constifyEdit(perElemExprp);

                perElemExprp->foreach([&](AstNode* nodep) {
                    // Don't mark loop variable references as randomizable
                    if (!VN_IS(nodep, Const)) {
                        if (AstNodeVarRef* const vrefp = VN_CAST(nodep, NodeVarRef)) {
                            if (vrefp->varp() != loopVarp) nodep->user1(true);
                        } else {
                            nodep->user1(true);
                        }
                    }
                });

                // Apply the operator to the text so far and the element's term
                AstNodeExpr* const openp = new AstConcatN{
                    fl, new AstConst{fl, AstConst::String{}, "(" + std::string{smtOp} + " "},
                    new AstVarRef{fl, textVarp, VAccess::READ}};
                bodyp = new AstAssign{
                    fl, new AstVarRef{fl, textVarp, VAccess::WRITE},
                    new AstConcatN{fl, openp, new AstConst{fl, AstConst::String{}, " "}}};
                bodyp->addNext(newTextAppendp(
                    fl, textVarp, VN_AS(iterateSubtreeReturnEdits(perElemExprp), NodeExpr)));
                bodyp->addNext(
                    newTextAppendp(fl, textVarp, new AstConst{fl, AstConst::String{}, ")"}));
            } else {
                // Without 'with' clause: register each element as solver variable
                AstVarRef* const arrRefp = VN_CAST(nodep->fromp(), VarRef);
                AstVar* const arrVarp = arrRefp->varp();
                const std::string smtArrayName = arrVarp->name();
                AstNodeDType* const elemDtp = arrVarp->dtypep()->skipRefp()->subDTypep();
                const int elemWidth = elemDtp->width();
                AstNodeModule* const arrModulep = VN_AS(arrVarp->user2p(), NodeModule);
                AstNodeModule* const genModulep = VN_AS(m_genp->user2p(), NodeModule);
                arrVarp->user3(true);

                // Add write_var call to init task
                AstNodeExpr* const arrVarNamep
                    = new AstCExpr{fl, AstCExpr::Pure{}, "\"" + smtArrayName + "\"", elemWidth};
                AstCMethodHard* const writeVarCallp
                    = new AstCMethodHard{fl, new AstVarRef{fl, genModulep, m_genp, VAccess::READ},
                                         VCMethod::RANDOMIZER_WRITE_VAR};
                writeVarCallp->addPinsp(new AstVarRef{fl, arrModulep, arrVarp, VAccess::READ});
                writeVarCallp->addPinsp(
                    new AstConst{fl, AstConst::Unsized64{}, static_cast<uint64_t>(elemWidth)});
                writeVarCallp->addPinsp(arrVarNamep);
                const uint32_t unpackedDims = arrVarp->dtypep()->dimensions(false).second;
                UASSERT_OBJ(unpackedDims == 1, arrVarp, "Array isn't 1-D");
                writeVarCallp->addPinsp(new AstConst{fl, 1});  // Dimension

                const RandomizeMode randMode = {.asUQuad = arrVarp->user1()};
                if (randMode.usesMode) {
                    writeVarCallp->addPinsp(
                        new AstConst{fl, AstConst::Unsized64{}, randMode.index});
                }
                writeVarCallp->dtypeSetVoid();
                AstBegin* initp = m_inlineInitBlockp;
                if (!initp) {
                    AstNodeFTask* const taskp
                        = VN_AS(m_memberMap.findMember(arrModulep, "new"), NodeFTask);
                    UASSERT_OBJ(taskp, arrModulep, "No new() in class");
                    initp = newInitBlockp(taskp);
                }
                initp->addStmtsp(writeVarCallp->makeStmt());

                // Create solver constraints
                AstSFormatF* const idxFormatp = new AstSFormatF{
                    fl, "#x%08x", false, new AstVarRef{fl, loopVarp, VAccess::READ}};
                iterateChildren(nodep);
                AstSFormatF* const varNamep
                    = createSolverArrDerefp(fl, nodep->fromp()->unlinkFrBack(), idxFormatp);

                bodyp = newTermAppendp(fl, textVarp, varNamep);
            }

            // Build final expression
            AstForeach* const foreachp = new AstForeach{fl, headerp, bodyp};
            if (withp) {
                // For 'with' clause: the nested operator terms, built from the identity
                nodep->replaceWith(newTextBuildp(fl, textVarp, identity, foreachp,
                                                 new AstVarRef{fl, textVarp, VAccess::READ}));
            } else {
                // For without 'with' clause: the operator applied to the element terms
                nodep->replaceWith(newTextBuildp(fl, textVarp, "", foreachp,
                                                 newTextApplyp(fl, textVarp, smtOp, identity)));
            }
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            return;
        }

        // We've handled DYN_SIZE already if they should be randomized
        if (nodep->method() == VCMethod::DYN_SIZE || nodep->method() == VCMethod::ASSOC_SIZE) {
            AstNodeExpr* nodeExprp = nodep->fromp();
            // Check if it is a pure chain of MemberSel ended with VarRef
            // if not throw warning
            while (VN_IS(nodeExprp, MemberSel)) {
                nodeExprp = VN_AS(nodeExprp, MemberSel)->fromp();
            }
            if (VN_IS(nodeExprp, VarRef)) {
                nodep->replaceWith(getConstFormat(nodep->cloneTreePure(false)));
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
                return;
            }
        }

        nodep->v3warn(CONSTRAINTIGN,
                      "Unsupported: randomizing this expression, treating as state");
        nodep->user1(false);

        if (editFormat(nodep)) return;
        nodep->v3fatalSrc("Method not handled in constraints? " << nodep);
    }
    void visit(AstNodeFTaskRef* nodep) override {
        if (editFormat(nodep)) return;

        AstFunc* const funcp = VN_CAST(nodep->taskp(), Func);
        if (!funcp) {
            // Tasks have no return value and can't appear in expressions.
            // Parser rejects this, so reaching here indicates a compiler bug.
            nodep->v3fatalSrc("Unexpected task call in constraint expression");
            return;
        }

        AstNodeExpr* const retExprp = extractReturnExpr(funcp);
        if (!retExprp) {
            nodep->v3warn(CONSTRAINTIGN,
                          "Unsupported: complex function in constraint, treating as state");
            nodep->user1(false);
            if (editFormat(nodep)) return;
            return;
        }

        // Map formal parameters to actual arguments using V3Task infrastructure
        const V3TaskConnects tconnects
            = V3Task::taskConnects(nodep, funcp->declsp(), nullptr, false);

        // Clone return expression, substitute params with args.
        // Track the root via a local pointer: when the root itself is a VarRef to a port
        // (e.g. body `F = d;`), the cloned root has no back pointer, so foreach's
        // replaceWith would trip the "no back" assertion -- substitute the root pointer
        // directly instead.
        AstNodeExpr* inlinedp = retExprp->cloneTreePure(false);
        for (const auto& tconnect : tconnects) {
            const AstVar* const portp = tconnect.first;
            AstArg* const argp = tconnect.second;
            if (!argp || !argp->exprp()) continue;
            if (AstVarRef* const rootRefp = VN_CAST(inlinedp, VarRef)) {
                if (rootRefp->varp() == portp) {
                    inlinedp = argp->exprp()->cloneTreePure(false);
                    VL_DO_DANGLING(rootRefp->deleteTree(), rootRefp);
                    continue;
                }
            }
            inlinedp->foreach([&](AstVarRef* refp) {
                if (refp->varp() == portp) {
                    refp->replaceWith(argp->exprp()->cloneTreePure(false));
                    VL_DO_DANGLING(refp->deleteTree(), refp);
                }
            });
        }

        inlinedp->dtypep(nodep->dtypep());
        propagateUser1InlineRecurse(inlinedp);
        nodep->replaceWith(inlinedp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
        iterate(inlinedp);
    }
    // Skip non-constraint stmts appended to the iterating list during inline randomize-with
    void visit(AstNodeStmt* nodep) override {}
    void visit(AstNodeExpr* nodep) override {
        if (editFormat(nodep)) return;
        nodep->v3fatalSrc(
            "Visit function missing? Constraint function missing for math node: " << nodep);
    }
    void visit(AstNode* nodep) override {
        nodep->v3fatalSrc(
            "Visit function missing? Constraint function missing for node: " << nodep);
    }

    // Build the runtime statement that calls RANDOMIZER_DISABLE_SOFT on the
    // variable referenced by the given AstConstraintExpr.  Parser enforces
    // constraint_primary operand (verilog.y, IEEE 1800-2023 18.5.13).
    AstNodeStmt* buildDisableSoftCallStmt(AstConstraintExpr* nodep) {
        std::string varName;
        if (const AstNodeVarRef* const vrefp = VN_CAST(nodep->exprp(), NodeVarRef)) {
            varName = vrefp->name();
        } else if (const AstMemberSel* const mselp = VN_CAST(nodep->exprp(), MemberSel)) {
            varName = mselp->name();
        } else {
            nodep->v3fatalSrc("Unexpected expression type in disable soft");
        }
        AstCMethodHard* const callp = new AstCMethodHard{
            nodep->fileline(),
            new AstVarRef{nodep->fileline(), VN_AS(m_genp->user2p(), NodeModule), m_genp,
                          VAccess::READWRITE},
            VCMethod::RANDOMIZER_DISABLE_SOFT,
            new AstConst{nodep->fileline(), AstConst::String{}, varName}};
        callp->dtypeSetVoid();
        return callp->makeStmt();
    }

    // Pre-pass: for every AstConstraintExpr(isDisableSoft) nested inside an
    // AstConstraintIf subtree (any depth), return a list of runtime AstIf
    // statements `if (accumulated_cond) randomizer.disable_soft(var);` where
    // accumulated_cond AND-folds the enclosing then/else branch conditions.
    // The original ConstraintExpr is replaced with `1'b1` so editSingle()
    // folds the surrounding boolean cleanly.  Caller appends the returned
    // list to the constraint-items chain; that chain becomes the setup task
    // body, which runs before the solver on every randomize() call -- giving
    // disable-soft real conditional semantics per IEEE 1800-2023 18.5.13.
    AstNode* extractConditionalDisableSofts(AstNode* itemsp, AstNodeExpr* outerCondp) {
        AstNode* hoistListp = nullptr;
        for (AstNode *stmtp = itemsp, *nextp; stmtp; stmtp = nextp) {
            nextp = stmtp->nextp();
            if (AstConstraintIf* const ifp = VN_CAST(stmtp, ConstraintIf)) {
                FileLine* const fl = ifp->fileline();
                // then branch: accumulated = outer && this.cond
                AstNodeExpr* const thenCondp
                    = outerCondp ? static_cast<AstNodeExpr*>(
                                       new AstLogAnd{fl, outerCondp->cloneTreePure(false),
                                                     ifp->condp()->cloneTreePure(false)})
                                 : ifp->condp()->cloneTreePure(false);
                if (AstNode* const thenHoistp
                    = extractConditionalDisableSofts(ifp->thensp(), thenCondp)) {
                    hoistListp
                        = hoistListp ? AstNode::addNext(hoistListp, thenHoistp) : thenHoistp;
                }
                VL_DO_DANGLING(thenCondp->deleteTree(), thenCondp);
                if (ifp->elsesp()) {
                    // else branch: accumulated = outer && !this.cond
                    AstNodeExpr* const notInnerp
                        = new AstLogNot{fl, ifp->condp()->cloneTreePure(false)};
                    AstNodeExpr* const elseCondp
                        = outerCondp ? static_cast<AstNodeExpr*>(new AstLogAnd{
                                           fl, outerCondp->cloneTreePure(false), notInnerp})
                                     : notInnerp;
                    if (AstNode* const elseHoistp
                        = extractConditionalDisableSofts(ifp->elsesp(), elseCondp)) {
                        hoistListp
                            = hoistListp ? AstNode::addNext(hoistListp, elseHoistp) : elseHoistp;
                    }
                    VL_DO_DANGLING(elseCondp->deleteTree(), elseCondp);
                }
            } else if (AstConstraintExpr* const exprp = VN_CAST(stmtp, ConstraintExpr)) {
                if (exprp->isDisableSoft() && outerCondp) {
                    FileLine* const fl = exprp->fileline();
                    AstIf* const hoistIfp = new AstIf{fl, outerCondp->cloneTreePure(false),
                                                      buildDisableSoftCallStmt(exprp), nullptr};
                    hoistListp = hoistListp ? AstNode::addNext(hoistListp,
                                                               static_cast<AstNode*>(hoistIfp))
                                            : static_cast<AstNode*>(hoistIfp);
                    // Replace in-tree disable-soft with a no-op boolean
                    // constraint so editSingle() folds cleanly.
                    AstConstraintExpr* const truep
                        = new AstConstraintExpr{fl, new AstConst{fl, AstConst::BitTrue{}}};
                    exprp->replaceWith(truep);
                    VL_DO_DANGLING(exprp->deleteTree(), exprp);
                }
            }
            // foreach/unique bodies are left untouched: disable-soft inside
            // a foreach would need per-iteration condition support, and
            // unique cannot legally contain disable-soft.
        }
        return hoistListp;
    }

public:
    // CONSTRUCTORS
    explicit ConstraintExprVisitor(AstClass* classp, VMemberMap& memberMap, AstNode* nodep,
                                   AstBegin* inlineInitp, AstVar* genp, AstVar* randModeVarp,
                                   std::set<std::string>& writtenVars,
                                   uint32_t* uniqueConstraintIdp, V3UniqueNames& uniqueNames,
                                   AstNodeFTask* memberselInitTaskp = nullptr,
                                   VInsertionSet<AstVar*>* sizeConstrainedArraysp = nullptr,
                                   AstNodeFTask* prepareConstrainedArraysp = nullptr)
        : m_classp{classp}
        , m_inlineInitBlockp{inlineInitp}
        , m_memberselInitTaskp{memberselInitTaskp}
        , m_genp{genp}
        , m_randModeVarp{randModeVarp}
        , m_memberMap{memberMap}
        , m_writtenVars{writtenVars}
        , m_sizeConstrainedArraysp{sizeConstrainedArraysp}
        , m_prepareConstrainedArraysp{prepareConstrainedArraysp}
        , m_uniqueConstraintIdp{uniqueConstraintIdp}
        , m_uniqueNames{uniqueNames} {
        // Pre-pass before SMT lowering: extract conditional disable-soft
        // directives as runtime AstIf statements and append them to the
        // constraint-items chain so they reach the setup task body.  The SMT
        // visitor skips these via visit(AstIf) above.
        if (AstNode* const hoistListp
            = nodep ? extractConditionalDisableSofts(nodep, nullptr) : nullptr) {
            nodep->addNext(hoistListp);
        }
        iterateAndNextNull(nodep);
    }
};

//######################################################################
// SMT-LIB solver back-end

class SolverSmtLowering final : public V3SolverLowering {
    // STATE
    int m_distNum = 0;  // Dist bucket variable counter within a class for var naming
    std::set<std::string> m_writtenVars;  // Track write_var calls per class to avoid duplicates
    std::map<AstClass*, VInsertionSet<AstVar*>> m_sizeConstrainedArrays;  // Per-class arrays
    uint32_t m_uniqueConstraintId = 0;  // current ID of unique call

    // METHODS
    AstVar* getStaticRandModeVar(AstClass* const classp) {
        return m_modeVars.staticRandModeVarp(classp);
    }
    AstVar* getStaticConstraintModeVar(AstClass* const classp) {
        return m_modeVars.staticConstraintModeVarp(classp);
    }
    static AstVar* getConstraintModeVar(AstClass* const classp) {
        return RandModeVars::constraintModeVarp(classp);
    }

    // Expand unique{a,b,c} with explicit elements into pairwise != constraints.
    // Whole-array unique{arr} is left for ConstraintExprVisitor's rand_unique handling.
    // Recurses into conditional and foreach bodies, so that the pairwise
    // constraints stay under the guard they were written under.
    static void expandUniqueElementList(AstNode* itemsp) {
        AstNode* itemp = itemsp;
        while (itemp) {
            AstNode* const nextp = itemp->nextp();
            if (const AstConstraintIf* const ifp = VN_CAST(itemp, ConstraintIf)) {
                expandUniqueElementList(ifp->thensp());
                expandUniqueElementList(ifp->elsesp());
                itemp = nextp;
                continue;
            }
            if (const AstConstraintForeach* const foreachp = VN_CAST(itemp, ConstraintForeach)) {
                expandUniqueElementList(foreachp->bodyp());
                itemp = nextp;
                continue;
            }
            AstConstraintUnique* const uniquep = VN_CAST(itemp, ConstraintUnique);
            if (!uniquep) {
                itemp = nextp;
                continue;
            }

            std::vector<AstNodeExpr*> exprItems;
            bool hasArrayVarRef = false;
            for (AstNode* const rp : uniquep->rangespList()) {
                if (const AstVarRef* const vrp = VN_CAST(rp, VarRef)) {
                    // A container's elements are made distinct by rand_unique, not pairwise
                    const AstNodeDType* const dtypep = vrp->varp()->dtypep()->skipRefp();
                    if (VN_IS(dtypep, NodeArrayDType) || VN_IS(dtypep, QueueDType)
                        || VN_IS(dtypep, DynArrayDType) || VN_IS(dtypep, AssocArrayDType)
                        || VN_IS(dtypep, WildcardArrayDType)) {
                        hasArrayVarRef = true;
                        continue;
                    }
                }
                exprItems.push_back(VN_AS(rp, NodeExpr));
            }

            if (exprItems.size() >= 2) {
                FileLine* const fl = uniquep->fileline();
                for (size_t i = 0; i < exprItems.size(); i++) {
                    for (size_t j = i + 1; j < exprItems.size(); j++) {
                        AstNodeExpr* const lhsp = exprItems[i]->cloneTree(false);
                        AstNodeExpr* const rhsp = exprItems[j]->cloneTree(false);
                        AstNeq* const neqp = new AstNeq{fl, lhsp, rhsp};
                        neqp->user1(true);
                        AstConstraintExpr* const cexprp = new AstConstraintExpr{fl, neqp};
                        uniquep->addNextHere(cexprp);
                    }
                }
                if (!hasArrayVarRef) {
                    uniquep->unlinkFrBack();
                    VL_DO_DANGLING(uniquep->deleteTree(), uniquep);
                }
            } else if (exprItems.size() == 1 && !hasArrayVarRef) {
                // A set of one element is unique whatever that element holds
                uniquep->unlinkFrBack();
                VL_DO_DANGLING(uniquep->deleteTree(), uniquep);
            }
            itemp = nextp;
        }
    }
    void createRandomGenerator(AstClass* const classp) {
        if (classp->user3p()) return;
        if (classp->extendsp()) {
            createRandomGenerator(classp->extendsp()->classp());
            return;
        }
        AstVar* const genp = new AstVar{classp->fileline(), VVarType::MEMBER, "constraint",
                                        classp->findBasicDType(VBasicDTypeKwd::RANDOM_GENERATOR)};
        genp->user2p(classp);
        classp->addMembersp(genp);
        classp->user3p(genp);
    }
    AstTask* createPrepareConstrainedArraysTask(AstClass* const classp) {
        static const char* const name = "__Vprepare_constrained_arrays";
        AstTask* const taskp = new AstTask{classp->fileline(), name};
        taskp->classMethod(true);
        classp->addMembersp(taskp);
        m_memberMap.insert(classp, taskp);
        return taskp;
    }
    AstTask* getCreateAggrResizeTask(AstClass* const classp) {
        static constexpr const char* const name = "__Vresize_constrained_arrays";
        AstTask* resizeTaskp = VN_AS(m_memberMap.findMember(classp, name), Task);
        if (resizeTaskp) return resizeTaskp;
        resizeTaskp = new AstTask{classp->fileline(), name};
        resizeTaskp->classMethod(true);
        resizeTaskp->isVirtual(true);
        classp->addMembersp(resizeTaskp);
        m_memberMap.insert(classp, resizeTaskp);
        return resizeTaskp;
    }
    static void addSetRandMode(AstNodeFTask* const ftaskp, AstVar* const genp,
                               AstVar* const randModeVarp) {
        FileLine* const fl = ftaskp->fileline();
        AstCMethodHard* const setRandModep = new AstCMethodHard{
            fl, new AstVarRef{fl, VN_AS(genp->user2p(), NodeModule), genp, VAccess::WRITE},
            VCMethod::CLASS_SET_RANDMODE,
            new AstVarRef{fl, VN_AS(randModeVarp->user2p(), NodeModule), randModeVarp,
                          VAccess::READ}};
        setRandModep->dtypeSetVoid();
        ftaskp->addStmtsp(setRandModep->makeStmt());
    }
    static void addSetStaticRandMode(AstNodeFTask* const ftaskp, AstVar* const genp,
                                     AstVar* const staticRandModeVarp) {
        FileLine* const fl = ftaskp->fileline();
        AstCMethodHard* const setp = new AstCMethodHard{
            fl, new AstVarRef{fl, VN_AS(genp->user2p(), NodeModule), genp, VAccess::WRITE},
            VCMethod::RANDOMIZER_SET_STATIC_RANDMODE,
            new AstVarRef{fl, VN_AS(staticRandModeVarp->user2p(), NodeModule), staticRandModeVarp,
                          VAccess::READ}};
        setp->dtypeSetVoid();
        ftaskp->addStmtsp(setp->makeStmt());
    }
    AstNodeStmt* wrapIfConstraintMode(AstClass* classp, AstConstraint* const constrp,
                                      AstNodeStmt* stmtp) {
        const RandomizeMode rmode = {.asUQuad = constrp->user1()};
        AstVar* const modeVarp = constrp->isStatic() ? getStaticConstraintModeVar(classp)
                                                     : getConstraintModeVar(classp);
        return RandModeVars::wrapIfMode(rmode, modeVarp, stmtp);
    }
    AstTask* newSetupConstraintTask(AstClass* const nodep, const std::string& name) {
        AstTask* const taskp = new AstTask{nodep->fileline(), name + "_setup_constraint"};
        taskp->classMethod(true);
        nodep->addMembersp(taskp);
        return taskp;
    }
    AstTask* newResizeConstrainedArrayTask(AstClass* const nodep, const std::string& name) {
        AstTask* const taskp = new AstTask{nodep->fileline(), name + "_resize_constrained_array"};
        taskp->classMethod(true);
        nodep->addMembersp(taskp);
        return taskp;
    }
    AstNodeStmt* implementConstraintsClear(FileLine* const fileline, AstVar* const genp) {
        AstCMethodHard* const clearp = new AstCMethodHard{
            fileline,
            new AstVarRef{fileline, VN_AS(genp->user2p(), NodeModule), genp, VAccess::READWRITE},
            VCMethod::RANDOMIZER_CLEARCONSTRAINTS};
        clearp->dtypeSetVoid();
        return clearp->makeStmt();
    }
    AstNodeStmt* implementConstraintsClearAll(FileLine* const fileline, AstVar* const genp) {
        AstCMethodHard* const clearp = new AstCMethodHard{
            fileline,
            new AstVarRef{fileline, VN_AS(genp->user2p(), NodeModule), genp, VAccess::READWRITE},
            VCMethod::RANDOMIZER_CLEARALL};
        clearp->dtypeSetVoid();
        return clearp->makeStmt();
    }
    // Get or create a size variable for a constrained dynamic/queue/assoc array.
    // Returns the size variable. Sets wasCreated=true if a new variable was made.
    AstVar* createOrGetSizeVar(AstClass* const classp, AstVar* const arrVarp, FileLine* const fl,
                               AstNodeDType* const signed32DTypep, bool& wasCreated) {
        AstVar* sizeVarp = VN_CAST(arrVarp->user4p(), Var);
        wasCreated = false;
        if (!sizeVarp) {
            sizeVarp = new AstVar{fl, VVarType::MEMBER, "__V" + arrVarp->name() + "_size",
                                  signed32DTypep};
            classp->addMembersp(sizeVarp);
            m_memberMap.insert(classp, sizeVarp);
            sizeVarp->user2p(classp);
            arrVarp->user4p(sizeVarp);
            wasCreated = true;
        }
        return sizeVarp;
    }
    // Build a size >= 0 constraint expression (signed int size must be non-negative).
    // Returns a new AstConstraintExpr with user1 bits set for solver visibility.
    AstConstraintExpr* createSizeGteZeroConstraint(FileLine* const fl, AstVar* const sizeVarp,
                                                   AstNodeExpr* derefFromp = nullptr) {
        AstNodeExpr* sizeNodeExprp = nullptr;
        if (derefFromp) {
            sizeNodeExprp = buildMemberSelExprp(derefFromp, sizeVarp);
        } else {
            sizeNodeExprp = new AstVarRef{fl, sizeVarp, VAccess::READ};
        }
        sizeNodeExprp->user1(true);
        AstGteS* const sizeGtep = new AstGteS{fl, sizeNodeExprp, new AstConst{fl, 0}};
        sizeGtep->user1(true);
        return new AstConstraintExpr{fl, sizeGtep};
    }
    // Returns MemberSel chain, with deepest VarRef being reference to deepestVarp
    AstNodeExpr* buildMemberSelExprp(AstNodeExpr* exprp, AstVar* deepestVarp) {
        UASSERT_OBJ(VN_IS(exprp, MemberSel) || VN_IS(exprp, VarRef), exprp,
                    "Should be MemberSel or VarRef");

        AstNodeExpr* resExprp = nullptr;
        if (const AstMemberSel* const memberSelp = VN_CAST(exprp, MemberSel)) {
            resExprp = buildMemberSelExprp(memberSelp->fromp(), nullptr);
            AstVar* varp = memberSelp->varp();
            if (deepestVarp) varp = deepestVarp;
            resExprp = new AstMemberSel{exprp->fileline(), resExprp, varp};
        } else if (const AstVarRef* const varRefp = VN_CAST(exprp, VarRef)) {
            AstVar* varp = varRefp->varp();
            if (deepestVarp) varp = deepestVarp;
            resExprp = new AstVarRef{exprp->fileline(), VN_AS(varp->user2p(), NodeModule), varp,
                                     VAccess::READWRITE};
        }

        resExprp->user1(true);
        return resExprp;
    }

    static void addUpdateRandVarsStmts(AstFunc* const updatep, AstNode* const stmtsp) {
        for (AstNode* stmtp = stmtsp; stmtp; stmtp = stmtp->nextp()) {
            if (AstBegin* const blockp = VN_CAST(stmtp, Begin)) {
                addUpdateRandVarsStmts(updatep, blockp->stmtsp());
                continue;
            }
            AstStmtExpr* const stmtExprp = VN_CAST(stmtp, StmtExpr);
            if (!stmtExprp) continue;
            AstCMethodHard* const methodp = VN_CAST(stmtExprp->exprp(), CMethodHard);
            if (!methodp || methodp->method() != VCMethod::RANDOMIZER_WRITE_VAR) continue;

            AstNodeVarRef* const varRefp = VN_AS(methodp->pinsp(), NodeVarRef);
            if (varRefp->varp()->lifetime().isStatic()) {
                // There is no need to update pointer to a static variable
                continue;
            }
            AstCMethodHard* const updateMethodp = new AstCMethodHard{
                methodp->fileline(), methodp->fromp()->cloneTreePure(false),
                VCMethod::RANDOMIZER_UPDATE_VAR, varRefp->cloneTreePure(false)};
            updateMethodp->dtypeSetVoid();
            AstNodeExpr* const namep = VN_AS(varRefp->nextp()->nextp(), NodeExpr);
            updateMethodp->addPinsp(namep->cloneTreePure(false));
            updateMethodp->method(VCMethod::RANDOMIZER_UPDATE_VAR);
            updatep->addStmtsp(updateMethodp->makeStmt());
        }
    }

    void addUpdateRandVarsBody(AstClass* const nodep, AstFunc* const randomizep) {
        UASSERT_OBJ(!nodep->hasRandVarsUpdate(), nodep, "__VupdateRandVars already exists");
        AstFunc* const updatep = new AstFunc{nodep->fileline(), "__VupdateRandVars"};
        updatep->classMethod(true);
        updatep->isVirtual(true);
        updatep->keepAlive(true);
        updatep->needsSyms(false);
        nodep->addMembersp(updatep);
        nodep->hasRandVarsUpdate(true);

        for (AstClass* classp = nodep; classp;
             classp = classp->extendsp() ? classp->extendsp()->classp() : nullptr) {
            AstNodeFTask* const newp = VN_AS(m_memberMap.findMember(classp, "new"), NodeFTask);
            addUpdateRandVarsStmts(updatep, newp->stmtsp());
        }
    }

    // Rewrite a LogIf-of-Dist chain into nested AstConstraintIf. The outermost
    // AstLogIf shell is left for the caller's AstConstraintExpr to free; inner
    // shells are deleted here once their children are transplanted.
    AstConstraintIf* liftLogIfChainToConstraintIf(AstLogIf* logIfp) {
        FileLine* const fl = logIfp->fileline();
        AstNodeExpr* const condp = logIfp->lhsp()->unlinkFrBack();
        AstNodeExpr* const rhsp = logIfp->rhsp()->unlinkFrBack();
        AstNodeStmt* thenBodyp;
        if (AstLogIf* const innerLogIfp = VN_CAST(rhsp, LogIf)) {
            thenBodyp = liftLogIfChainToConstraintIf(innerLogIfp);
            VL_DO_DANGLING(pushDeletep(innerLogIfp), innerLogIfp);
        } else {
            thenBodyp = new AstConstraintExpr{fl, rhsp};
        }
        return new AstConstraintIf{fl, condp, thenBodyp, nullptr};
    }

    static bool distBoundRefsRandVar(const AstNode* boundp) {
        return boundp->exists(
            [](const AstVarRef* vrefp) { return vrefp->varp()->rand().isRandomizable(); });
    }

    static bool distBoundRefsModeVar(const AstNode* boundp) {
        return boundp->exists([](const AstVarRef* vrefp) {
            if (!vrefp->varp()->rand().isRandomizable()) return false;
            const RandomizeMode rmode = {.asUQuad = vrefp->varp()->user1()};
            return rmode.usesMode;
        });
    }

    // (distExpr >= lo) && (distExpr <= hi); signed comparisons for signed vars
    static AstNodeExpr* newDistRangeMembership(AstDist* distp, const AstInsideRange* irp) {
        FileLine* const fl = distp->fileline();
        const bool isSigned = distp->exprp()->isSigned();
        AstNodeExpr* const distExprGtep = distp->exprp()->cloneTreePure(false);
        AstNodeExpr* const distExprLtep = distp->exprp()->cloneTreePure(false);
        distExprGtep->user1(true);
        distExprLtep->user1(true);
        AstNodeExpr* const gep
            = isSigned ? static_cast<AstNodeExpr*>(
                             new AstGteS{fl, distExprGtep, irp->lhsp()->cloneTreePure(false)})
                       : static_cast<AstNodeExpr*>(
                             new AstGte{fl, distExprGtep, irp->lhsp()->cloneTreePure(false)});
        AstNodeExpr* const lep
            = isSigned ? static_cast<AstNodeExpr*>(
                             new AstLteS{fl, distExprLtep, irp->rhsp()->cloneTreePure(false)})
                       : static_cast<AstNodeExpr*>(
                             new AstLte{fl, distExprLtep, irp->rhsp()->cloneTreePure(false)});
        gep->user1(true);
        lep->user1(true);
        AstNodeExpr* const andp = new AstLogAnd{fl, gep, lep};
        andp->user1(true);
        return andp;
    }

    struct DistBucket final {
        AstNodeExpr* rangep;  // A single value or an InsideRange
        AstNodeExpr* weightExprp;  // Effective 64-bit weight (range weight scaled by size)
    };

    // Non-zero-weight buckets with each weight extended to 64 bits.
    std::vector<DistBucket> collectDistBuckets(AstDist* const distp) {
        FileLine* const fl = distp->fileline();
        std::vector<DistBucket> buckets;
        for (AstDistItem* const ditemp : distp->itemspList()) {
            if (const AstConst* const constp = VN_CAST(ditemp->weightp(), Const)) {
                if (constp->toUQuad() == 0) continue;
            }
            AstNodeExpr* weightExprp
                = new AstExtend{fl, ditemp->weightp()->cloneTreePure(false), 64};
            // := on a range weights every element, so scale by the range size.
            if (!ditemp->isWhole()) {
                if (const AstInsideRange* const irp = VN_CAST(ditemp->rangep(), InsideRange)) {
                    const AstConst* const lop = VN_CAST(irp->lhsp(), Const);
                    const AstConst* const hip = VN_CAST(irp->rhsp(), Const);
                    AstNodeExpr* rangeSizep;
                    if (lop && hip) {
                        const uint64_t rangeSize = hip->toUQuad() - lop->toUQuad() + 1;
                        rangeSizep = new AstConst{fl, AstConst::Unsized64{}, rangeSize};
                    } else {
                        rangeSizep = new AstAdd{
                            fl, new AstConst{fl, AstConst::Unsized64{}, 1},
                            new AstSub{fl,
                                       new AstExtend{fl, irp->rhsp()->cloneTreePure(false), 64},
                                       new AstExtend{fl, irp->lhsp()->cloneTreePure(false), 64}}};
                    }
                    weightExprp = new AstMul{fl, weightExprp, rangeSizep};
                }
            }
            buckets.push_back({ditemp->rangep(), weightExprp});
        }
        return buckets;
    }

    // Membership test for one bucket: a range comparison or an equality.
    static AstNodeExpr* newDistMembershipTerm(AstDist* distp, AstNodeExpr* rangep) {
        if (const AstInsideRange* const irp = VN_CAST(rangep, InsideRange)) {
            return newDistRangeMembership(distp, irp);
        }
        FileLine* const fl = distp->fileline();
        AstNodeExpr* const eqExprp = distp->exprp()->cloneTreePure(false);
        eqExprp->user1(true);
        AstNodeExpr* const eqp = new AstEq{fl, eqExprp, rangep->cloneTreePure(false)};
        eqp->user1(true);
        return eqp;
    }

    // Hard constraint that the dist value stays inside the union of its ranges
    // (IEEE 1800-2023 18.5.3: values outside the set must never appear).
    AstConstraintExpr* buildDistMembership(AstDist* distp,
                                           const std::vector<DistBucket>& buckets) {
        FileLine* const fl = distp->fileline();
        AstNodeExpr* unionExprp = nullptr;
        for (const auto& bucket : buckets) {
            AstNodeExpr* const memberp = newDistMembershipTerm(distp, bucket.rangep);
            if (!unionExprp) {
                unionExprp = memberp;
            } else {
                unionExprp = new AstLogOr{fl, memberp, unionExprp};
                unionExprp->user1(true);
            }
        }
        return new AstConstraintExpr{fl, unionExprp};
    }

    // Gate junction with constants folded and identical terms merged.
    AstNodeExpr* newGateJoin(FileLine* fl, AstNodeExpr* ap, AstNodeExpr* bp, bool isAnd) {
        if (ap->sameTree(bp)) {
            VL_DO_DANGLING(pushDeletep(bp), bp);
            return ap;
        }
        if (VN_IS(bp, Const)) std::swap(ap, bp);
        if (VN_IS(ap, Const)) {
            const bool constWins = VN_AS(ap, Const)->isZero() == isAnd;
            if (!constWins) std::swap(ap, bp);
            VL_DO_DANGLING(pushDeletep(bp), bp);
            return ap;
        }
        if (isAnd) return new AstLogAnd{fl, ap, bp};
        return new AstLogOr{fl, ap, bp};
    }
    AstNodeExpr* newGateOr(FileLine* fl, AstNodeExpr* ap, AstNodeExpr* bp) {
        return newGateJoin(fl, ap, bp, false);
    }
    AstNodeExpr* newGateAnd(FileLine* fl, AstNodeExpr* ap, AstNodeExpr* bp) {
        return newGateJoin(fl, ap, bp, true);
    }

    // The rand_mode bit of varp: static class var, owner object's array via the
    // member select, or this object's array.
    AstNodeExpr* newModeBitRead(AstVar* varp, const AstMemberSel* mselp, AstVar* randModeVarp,
                                FileLine* fl) {
        AstNodeExpr* arrayp = nullptr;
        if (varp->lifetime().isStatic()) {
            AstClass* const ownerp = VN_CAST(varp->user2p(), Class);
            UASSERT_OBJ(ownerp, varp, "usesMode static var without an owning class");
            AstVar* const smodep = getStaticRandModeVar(ownerp);
            UASSERT_OBJ(smodep, varp, "usesMode static var without a static rand-mode array");
            arrayp = new AstVarRef{fl, VN_AS(smodep->user2p(), NodeModule), smodep, VAccess::READ};
        } else if (mselp) {
            AstVar* const memberModep
                = RandModeVars::randModeVarp(VN_AS(varp->user2p(), NodeModule));
            UASSERT_OBJ(memberModep, varp, "usesMode member without a class rand-mode array");
            arrayp = new AstMemberSel{fl, mselp->fromp()->cloneTreePure(false), memberModep};
        } else {
            UASSERT_OBJ(randModeVarp, varp, "rand_mode variable without a class mode array");
            arrayp = new AstVarRef{fl, VN_AS(randModeVarp->user2p(), NodeModule), randModeVarp,
                                   VAccess::READ};
        }
        const RandomizeMode rmode = {.asUQuad = varp->user1()};
        AstCMethodHard* const atp
            = new AstCMethodHard{fl, arrayp, VCMethod::ARRAY_AT, new AstConst{fl, rmode.index}};
        atp->dtypeSetUInt32();
        return atp;
    }

    // The rand_mode bit of one variable access, or a constant when it has none.
    // A non-rand value can never be re-drawn; a non-rand owner level is skipped.
    AstNodeExpr* newVarGate(AstVar* varp, const AstMemberSel* mselp, bool ownerLevel,
                            AstVar* randModeVarp, FileLine* fl) {
        if (!varp->rand().isRandomizable()) {
            return new AstConst{fl, AstConst::BitTrue{}, ownerLevel};
        }
        const RandomizeMode rmode = {.asUQuad = varp->user1()};
        if (!rmode.usesMode) return new AstConst{fl, AstConst::BitTrue{}};
        return newModeBitRead(varp, mselp, randModeVarp, fl);
    }

    // Change bit of one variable access, ANDed level by level down the
    // member-select owner path.
    AstNodeExpr* newAccessGate(const AstNode* nodep, bool ownerLevel, AstVar* randModeVarp,
                               FileLine* fl) {
        if (const AstMemberSel* const mselp = VN_CAST(nodep, MemberSel)) {
            return newGateAnd(fl, newVarGate(mselp->varp(), mselp, ownerLevel, randModeVarp, fl),
                              newAccessGate(mselp->fromp(), true, randModeVarp, fl));
        }
        if (const AstNodeVarRef* const refp = VN_CAST(nodep, NodeVarRef)) {
            return newVarGate(refp->varp(), nullptr, ownerLevel, randModeVarp, fl);
        }
        if (const AstNodeSel* const selp = VN_CAST(nodep, NodeSel)) {
            return newAccessGate(selp->fromp(), true, randModeVarp, fl);
        }
        if (distBoundRefsModeVar(nodep)) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: 'rand_mode' on a variable used inside this form of"
                          " 'dist' expression");
        }
        return new AstConst{fl, AstConst::BitTrue{}};
    }

    // Gate of one dist expression node: nonzero while its value can still be
    // freshly drawn. Constant when no runtime rand_mode bit is involved.
    AstNodeExpr* newDistGate(const AstNode* nodep, AstVar* randModeVarp, FileLine* fl) {
        if (VN_IS(nodep, NodeVarRef) || VN_IS(nodep, MemberSel)) {
            return newAccessGate(nodep, false, randModeVarp, fl);
        }
        // A selection is drawn through its base; the index never gates.
        if (const AstNodeSel* const selp = VN_CAST(nodep, NodeSel)) {
            return newDistGate(selp->fromp(), randModeVarp, fl);
        }
        if (const AstSel* const selp = VN_CAST(nodep, Sel)) {
            return newDistGate(selp->fromp(), randModeVarp, fl);
        }
        if (const AstStructSel* const selp = VN_CAST(nodep, StructSel)) {
            return newDistGate(selp->fromp(), randModeVarp, fl);
        }
        if (const AstCMethodHard* const methodp = VN_CAST(nodep, CMethodHard)) {
            if (methodp->method() == VCMethod::ARRAY_AT
                && VN_IS(methodp->fromp()->dtypep()->skipRefp(),  // LCOV_EXCL_BR_LINE
                         DynArrayDType)) {  // Queue form is rejected before dist lowering
                return newDistGate(methodp->fromp(), randModeVarp, fl);
            }
        }
        // A conditional re-draws through an active selector or the selected arm.
        if (const AstCond* const condp = VN_CAST(nodep, Cond)) {
            AstNodeExpr* const thenGatep = newDistGate(condp->thenp(), randModeVarp, fl);
            AstNodeExpr* const elseGatep = newDistGate(condp->elsep(), randModeVarp, fl);
            AstNodeExpr* armGatep = thenGatep;
            if (thenGatep->sameTree(elseGatep)) {
                VL_DO_DANGLING(pushDeletep(elseGatep), elseGatep);
            } else {
                armGatep
                    = new AstCond{fl, condp->condp()->cloneTreePure(false), thenGatep, elseGatep};
            }
            return newGateOr(fl, newDistGate(condp->condp(), randModeVarp, fl), armGatep);
        }
        if (const AstNodeUniop* const uopp = VN_CAST(nodep, NodeUniop)) {
            return newDistGate(uopp->lhsp(), randModeVarp, fl);
        }
        if (const AstNodeBiop* const bopp = VN_CAST(nodep, NodeBiop)) {
            return newGateOr(fl, newDistGate(bopp->lhsp(), randModeVarp, fl),
                             newDistGate(bopp->rhsp(), randModeVarp, fl));
        }
        if (distBoundRefsModeVar(nodep)) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: 'rand_mode' on a variable used inside this form of"
                          " 'dist' expression");
        }
        // Constants and remaining forms re-draw only if a rand var is inside.
        return new AstConst{fl, AstConst::BitTrue{}, distBoundRefsRandVar(nodep)};
    }

    // Membership union of the dist set, with runtime-zero weights excluded.
    AstConstraintExpr* buildFrozenMembership(AstDist* distp,
                                             const std::vector<DistBucket>& buckets) {
        FileLine* const fl = distp->fileline();
        AstNodeExpr* unionExprp = nullptr;
        for (const auto& bucket : buckets) {
            AstNodeExpr* termp = newDistMembershipTerm(distp, bucket.rangep);
            // A weight that is zero only at runtime excludes the bucket's values too.
            const bool runtimeWeight
                = bucket.weightExprp->exists([](const AstNodeVarRef*) { return true; });
            if (runtimeWeight) {
                AstNeq* const nzp = new AstNeq{fl, bucket.weightExprp->cloneTreePure(false),
                                               new AstConst{fl, AstConst::Unsized64{}, 0}};
                nzp->user1(true);
                termp = new AstLogAnd{fl, termp, nzp};
                termp->user1(true);
            }
            if (unionExprp) {
                unionExprp = new AstLogOr{fl, unionExprp, termp};
                unionExprp->user1(true);
            } else {
                unionExprp = termp;
            }
        }
        return new AstConstraintExpr{fl, unionExprp};
    }

    // Weighted chain while the dist value can still be freshly drawn, membership
    // once it is frozen; membership only when it can never be re-drawn.
    AstNodeStmt* gateFrozenDist(AstNodeStmt* chainp, AstDist* distp,
                                const std::vector<DistBucket>& buckets, AstVar* randModeVarp) {
        FileLine* const fl = distp->fileline();
        AstNodeExpr* gatep = newDistGate(distp->exprp(), randModeVarp, fl);
        if (VN_IS(gatep, Const)) {
            const bool drawable = !VN_AS(gatep, Const)->isZero();
            VL_DO_DANGLING(pushDeletep(gatep), gatep);
            if (drawable) return chainp;
            VL_DO_DANGLING(pushDeletep(chainp), chainp);
            return buildFrozenMembership(distp, buckets);
        }
        return new AstConstraintIf{fl, gatep, chainp, buildFrozenMembership(distp, buckets)};
    }

    AstNodeExpr* newUniformRangePick(AstDist* distp, const AstInsideRange* irp) {
        FileLine* const fl = distp->fileline();
        AstNodeExpr* const distExprCopyp = distp->exprp()->cloneTreePure(false);
        distExprCopyp->user1(true);
        const int distWidth = distp->exprp()->width();
        const AstConst* const lopCp = VN_CAST(irp->lhsp(), Const);
        const AstConst* const hipCp = VN_CAST(irp->rhsp(), Const);
        AstNodeExpr* rangeSzp;
        if (lopCp && hipCp) {
            const uint64_t rsz = hipCp->toUQuad() - lopCp->toUQuad() + 1;
            rangeSzp = new AstConst{fl, AstConst::Unsized64{}, rsz};
        } else {
            const bool isSigned = irp->lhsp()->isSigned();
            AstNodeExpr* const lo64p
                = isSigned ? static_cast<AstNodeExpr*>(
                                 new AstExtendS{fl, irp->lhsp()->cloneTreePure(false), 64})
                           : static_cast<AstNodeExpr*>(
                                 new AstExtend{fl, irp->lhsp()->cloneTreePure(false), 64});
            AstNodeExpr* const hi64p
                = isSigned ? static_cast<AstNodeExpr*>(
                                 new AstExtendS{fl, irp->rhsp()->cloneTreePure(false), 64})
                           : static_cast<AstNodeExpr*>(
                                 new AstExtend{fl, irp->rhsp()->cloneTreePure(false), 64});
            rangeSzp = new AstAdd{fl, new AstConst{fl, AstConst::Unsized64{}, 1ULL},
                                  new AstSub{fl, hi64p, lo64p}};
        }
        AstNodeExpr* const rand64p = new AstRand{fl, nullptr, false};
        rand64p->dtypeSetUInt64();
        AstNodeExpr* const offsetp
            = new AstCCast{fl, new AstModDiv{fl, rand64p, rangeSzp}, distWidth};
        AstNodeExpr* const valuep = new AstAdd{fl, irp->lhsp()->cloneTreePure(false), offsetp};
        AstNodeExpr* const eqp = new AstEq{fl, distExprCopyp, valuep};
        eqp->user1(true);
        return eqp;
    }

    // Soft weighted bucket chain: select a bucket by bucketVar against cumulative weights.
    AstConstraintExpr* buildWeightedBucketChain(AstDist* distp,
                                                const std::vector<DistBucket>& buckets,
                                                AstVar* bucketVarp,
                                                const std::vector<AstNodeExpr*>& cumSums) {
        FileLine* const fl = distp->fileline();
        AstNodeExpr* chainp = nullptr;
        for (int i = static_cast<int>(buckets.size()) - 1; i >= 0; --i) {
            AstNodeExpr* constraintExprp;
            const AstInsideRange* const irp = VN_CAST(buckets[i].rangep, InsideRange);
            if (irp && (distBoundRefsRandVar(irp->lhsp()) || distBoundRefsRandVar(irp->rhsp()))) {
                constraintExprp = newDistRangeMembership(distp, irp);
            } else if (irp) {
                constraintExprp = newUniformRangePick(distp, irp);
            } else {
                AstNodeExpr* const distExprCopyp = distp->exprp()->cloneTreePure(false);
                distExprCopyp->user1(true);
                constraintExprp
                    = new AstEq{fl, distExprCopyp, buckets[i].rangep->cloneTreePure(false)};
                constraintExprp->user1(true);
            }
            if (!chainp) {
                chainp = constraintExprp;
            } else {
                AstNodeExpr* const condp
                    = new AstLte{fl, new AstVarRef{fl, bucketVarp, VAccess::READ}, cumSums[i]};
                condp->user1(true);
                chainp = new AstCond{fl, condp, constraintExprp, chainp};
                chainp->user1(true);
            }
        }
        AstConstraintExpr* const chainExprp = new AstConstraintExpr{fl, chainp};
        chainExprp->isSoft(true);
        return chainExprp;
    }

    // Replace AstDist with weighted bucket selection via AstConstraintIf chain.
    // Supports both constant and variable weight expressions.
    void lowerDistConstraints(AstTask* taskp, AstNode* constrItemsp, AstVar* randModeVarp,
                              AstConstraintForeach* foreachp = nullptr) {
        // When inside a foreach, bucket preamble stmts are stored in foreachp->user3p()
        // (as a linked list) so visit(AstConstraintForeach*) can inject them into the
        // real AstForeach body. Outside a foreach, they go directly into taskp. The
        // variables are always declared in taskp, assigned before use in each iteration.
        AstNodeStmt* foreachTailp = nullptr;
        auto addStmt = [&](AstNodeStmt* nodep) {
            if (foreachp) {
                if (!foreachTailp) {
                    foreachp->user3p(nodep);
                    foreachTailp = nodep;
                } else {
                    foreachTailp->addNext(nodep);
                    foreachTailp = nodep;
                }
            } else {
                taskp->addStmtsp(nodep);
            }
        };

        for (AstNode *nextip, *itemp = constrItemsp; itemp; itemp = nextip) {
            nextip = itemp->nextp();

            // dist can appear inside an if/else or foreach constraint.
            if (AstConstraintIf* const cifp = VN_CAST(itemp, ConstraintIf)) {
                UASSERT_OBJ(cifp->thensp(), cifp, "constraint if without a then body");
                lowerDistConstraints(taskp, cifp->thensp(), randModeVarp, foreachp);
                if (cifp->elsesp()) {
                    lowerDistConstraints(taskp, cifp->elsesp(), randModeVarp, foreachp);
                }
                continue;
            }
            if (AstConstraintForeach* const cfep = VN_CAST(itemp, ConstraintForeach)) {
                UASSERT_OBJ(cfep->bodyp(), cfep, "constraint foreach without a body");
                lowerDistConstraints(taskp, cfep->bodyp(), randModeVarp, cfep);
                continue;
            }

            AstConstraintExpr* const constrExprp = VN_CAST(itemp, ConstraintExpr);
            if (!constrExprp) continue;

            // `cond -> x dist {...}` parses as ConstraintExpr(LogIf(cond, Dist)).
            // This pass only scans ConstraintExpr/If/Foreach for Dist, so lift the
            // LogIf chain into nested ConstraintIf first. Chains like
            // `a -> b -> dist` nest accordingly.
            if (AstLogIf* const topLogIfp = VN_CAST(constrExprp->exprp(), LogIf)) {
                AstNode* chainEndp = topLogIfp->rhsp();
                while (AstLogIf* const innerp = VN_CAST(chainEndp, LogIf)) {
                    chainEndp = innerp->rhsp();
                }
                if (VN_IS(chainEndp, Dist)) {
                    AstConstraintIf* const liftedp = liftLogIfChainToConstraintIf(topLogIfp);
                    constrExprp->replaceWith(liftedp);
                    VL_DO_DANGLING(pushDeletep(constrExprp), constrExprp);
                    lowerDistConstraints(taskp, liftedp->thensp(), randModeVarp, foreachp);
                    continue;
                }
            }

            AstDist* const distp = VN_CAST(constrExprp->exprp(), Dist);
            if (!distp) continue;

            FileLine* const fl = distp->fileline();

            std::vector<DistBucket> buckets = collectDistBuckets(distp);

            if (buckets.empty()) {
                // All weights are zero: dist is vacuously true (unconstrained)
                AstConstraintExpr* const truep
                    = new AstConstraintExpr{fl, new AstConst{fl, AstConst::BitTrue{}}};
                constrExprp->replaceWith(truep);
                VL_DO_DANGLING(pushDeletep(constrExprp), constrExprp);
                continue;
            }

            AstConstraintExpr* const membershipp = buildDistMembership(distp, buckets);

            // Build totalWeight expression: w[0] + w[1] + ... + w[N-1]
            AstNodeExpr* totalWeightExprp = nullptr;
            for (auto& bucket : buckets) {
                if (!totalWeightExprp) {
                    totalWeightExprp = bucket.weightExprp->cloneTreePure(false);
                } else {
                    totalWeightExprp = new AstAdd{fl, totalWeightExprp,
                                                  bucket.weightExprp->cloneTreePure(false)};
                    totalWeightExprp->dtypeSetUInt64();
                }
            }

            // Store totalWeight in temp var (evaluated once, used twice)
            const int distId = m_distNum++;
            const std::string totalName = "__Vdist_total" + cvtToStr(distId);
            AstVar* const totalVarp
                = new AstVar{fl, VVarType::BLOCKTEMP, totalName, taskp->findUInt64DType()};
            totalVarp->noSubst(true);
            totalVarp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
            totalVarp->funcLocal(true);
            totalVarp->isInternal(true);
            taskp->addDeclsp(totalVarp);
            addStmt(
                new AstAssign{fl, new AstVarRef{fl, totalVarp, VAccess::WRITE}, totalWeightExprp});

            // bucketVar = (rand64() % totalWeight) + 1
            const std::string bucketName = "__Vdist_bucket" + cvtToStr(distId);
            AstVar* const bucketVarp
                = new AstVar{fl, VVarType::BLOCKTEMP, bucketName, taskp->findUInt64DType()};
            bucketVarp->noSubst(true);
            bucketVarp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
            bucketVarp->funcLocal(true);
            bucketVarp->isInternal(true);
            taskp->addDeclsp(bucketVarp);

            AstNodeExpr* const randp = new AstRand{fl, nullptr, false};
            randp->dtypeSetUInt64();
            addStmt(new AstAssign{
                fl, new AstVarRef{fl, bucketVarp, VAccess::WRITE},
                new AstAdd{
                    fl, new AstConst{fl, AstConst::Unsized64{}, 1},
                    new AstModDiv{fl, randp, new AstVarRef{fl, totalVarp, VAccess::READ}}}});

            // Build cumulative sum expressions forward: cumSum[i] = w[0]+...+w[i]
            std::vector<AstNodeExpr*> cumSums;
            AstNodeExpr* runningSump = nullptr;
            for (size_t i = 0; i < buckets.size(); ++i) {
                if (!runningSump) {
                    runningSump = buckets[i].weightExprp->cloneTreePure(false);
                } else {
                    runningSump = new AstAdd{fl, runningSump,
                                             buckets[i].weightExprp->cloneTreePure(false)};
                    runningSump->dtypeSetUInt64();
                }
                cumSums.push_back(runningSump->cloneTreePure(true));
            }

            AstNodeStmt* chainp = buildWeightedBucketChain(distp, buckets, bucketVarp, cumSums);

            chainp = gateFrozenDist(chainp, distp, buckets, randModeVarp);

            constrExprp->replaceWith(chainp);
            VL_DO_DANGLING(pushDeletep(constrExprp), constrExprp);
            // Hard membership precedes the soft bucket chain in the constraint list.
            chainp->addHereThisAsNext(membershipp);

            // Clean up nodes used only as clone templates (never inserted into tree)
            for (auto& bucket : buckets) {
                VL_DO_DANGLING(pushDeletep(bucket.weightExprp), bucket.weightExprp);
            }
            VL_DO_DANGLING(pushDeletep(runningSump), runningSump);
            // Last cumSum is unused (last bucket is unconditional default)
            pushDeletep(cumSums.back());
        }
    }

    static bool isDynArrOfClassTypeRecurse(const AstNodeDType* const dtypep) {
        const AstNodeDType* const refp = dtypep->skipRefp();
        if (VN_IS(refp, DynArrayDType) || VN_IS(refp, QueueDType)) {
            return isDynArrOfClassTypeRecurse(refp->subDTypep());
        } else if (VN_IS(refp, ClassRefDType)) {
            return true;
        }
        return false;
    }

    // Add write_var calls for each array element after resizing it with array-size constraint
    void addArrayElemRefresh(FileLine* const fl, AstVar* const arrVarp, AstFunc* const randomizep,
                             AstVar* const genp) {
        AstNodeModule* const genModp = VN_AS(genp->user2p(), NodeModule);
        // Array elements of class data type are passed to the solver as separate
        // variables, so passing the original array variable is redundant, because it
        // won't be referenced
        const uint32_t unpackedDims = arrVarp->dtypep()->dimensions(false).second;
        if (isDynArrOfClassTypeRecurse(arrVarp->dtypep())) {
            if (unpackedDims > 1) {
                arrVarp->v3warn(E_UNSUPPORTED,
                                "Unsupported: Nested array element access in global constraint");
            }
            return;
        }
        AstCMethodHard* const methodp
            = new AstCMethodHard{fl, new AstVarRef{fl, genModp, genp, VAccess::READWRITE},
                                 VCMethod::RANDOMIZER_WRITE_VAR};
        methodp->dtypeSetVoid();

        AstNodeModule* const classp = VN_AS(arrVarp->user2p(), NodeModule);
        AstVarRef* const varRefp = new AstVarRef{fl, classp, arrVarp, VAccess::WRITE};
        varRefp->classOrPackagep(classp);
        methodp->addPinsp(varRefp);

        const size_t width = SmtUtil::arrayElementDTypep(arrVarp->dtypep())->width();

        methodp->addPinsp(new AstConst{fl, AstConst::Unsized64{}, width});
        AstNodeExpr* const varnamep
            = new AstCExpr{fl, AstCExpr::Pure{}, "\"" + arrVarp->name() + "\"", arrVarp->width()};
        varnamep->dtypep(arrVarp->dtypep());
        methodp->addPinsp(varnamep);
        methodp->addPinsp(new AstConst{fl, AstConst::Unsized64{}, unpackedDims});
        const RandomizeMode rmode = {.asUQuad = arrVarp->user1()};
        if (rmode.usesMode) {
            methodp->addPinsp(new AstConst{fl, AstConst::Unsized64{}, rmode.index});
        }

        randomizep->addStmtsp(methodp->makeStmt());
    }

    AstNodeStmt* newPinSizeVariable(FileLine* const fl, AstVar* const arrVarp,
                                    AstVar* const genp) {
        AstNodeModule* const genModp = VN_AS(genp->user2p(), NodeModule);
        AstVar* const sizeVarp = VN_AS(arrVarp->user4p(), Var);
        AstCMethodHard* const pinp
            = new AstCMethodHard{fl, new AstVarRef{fl, genModp, genp, VAccess::READWRITE},
                                 VCMethod::RANDOMIZER_PIN_VAR};
        pinp->dtypeSetVoid();
        AstCExpr* const namep = new AstCExpr{fl, AstCExpr::Pure{}, "\"" + sizeVarp->name() + "\""};
        namep->dtypeSetUInt32();
        pinp->addPinsp(namep);
        pinp->addPinsp(
            new AstConst{fl, AstConst::Unsized64{}, static_cast<uint64_t>(sizeVarp->width())});
        // sizeVarp may live in a base class when the constrained array is inherited; route the
        // reference through its declaring class so V3Scope can resolve it.
        AstVarRef* const sizeVarRefp = new AstVarRef{fl, sizeVarp, VAccess::READ};
        sizeVarRefp->classOrPackagep(VN_AS(sizeVarp->user2p(), NodeModule));
        pinp->addPinsp(sizeVarRefp);
        return pinp->makeStmt();
    }

    void addFrozenSizePin(FileLine* const fl, AstVar* const arrVarp, AstFunc* const randomizep,
                          AstVar* const genp, AstVar* const randModeVarp) {
        const RandomizeMode rmode = {.asUQuad = arrVarp->user1()};
        if (!rmode.usesMode) return;
        AstVar* const sizeVarp = VN_AS(arrVarp->user4p(), Var);
        AstNodeModule* const arrClassp = VN_AS(arrVarp->user2p(), NodeModule);
        AstNodeModule* const sizeClassp = VN_AS(sizeVarp->user2p(), NodeModule);
        AstVarRef* const sizeWritep = new AstVarRef{fl, sizeClassp, sizeVarp, VAccess::WRITE};
        const VCMethod sizeMethod = VN_IS(arrVarp->dtypep()->skipRefp(), AssocArrayDType)
                                        ? VCMethod::ASSOC_SIZE
                                        : VCMethod::DYN_SIZE;
        AstCMethodHard* const currentSizep = new AstCMethodHard{
            fl, new AstVarRef{fl, arrClassp, arrVarp, VAccess::READ}, sizeMethod};
        currentSizep->dtypep(sizeVarp->dtypep());
        randomizep->addStmtsp(new AstAssign{fl, sizeWritep, currentSizep});
        AstNodeExpr* const modep = newModeBitRead(arrVarp, nullptr, randModeVarp, fl);
        randomizep->addStmtsp(
            new AstIf{fl, new AstLogNot{fl, modep}, newPinSizeVariable(fl, arrVarp, genp)});
    }

    void collectSizeConstrainedArrays(AstClass* classp,
                                      VInsertionSet<AstVar*>& sizeArrayVars) const {
        while (classp) {
            const auto sizeArraysIt = m_sizeConstrainedArrays.find(classp);
            if (sizeArraysIt != m_sizeConstrainedArrays.end()) {
                sizeArrayVars.insert(sizeArraysIt->second.begin(), sizeArraysIt->second.end());
            }
            classp = classp->extendsp() ? classp->extendsp()->classp() : nullptr;
        }
    }

    static void copyVariableRegistrations(AstFunc* const sourcep, AstFunc* const targetp) {
        for (AstNodeStmt* const stmtp : sourcep->stmtspList()) {
            bool hasRegistration = false;
            bool foundClearConstraints = false;
            // stmtp is possibly begin containing a few statements
            stmtp->foreach([&](AstCMethodHard* methodp) {
                if (methodp->method() == VCMethod::RANDOMIZER_WRITE_VAR
                    || methodp->method() == VCMethod::RANDOMIZER_MARK_RANDC) {
                    hasRegistration = true;
                } else if (methodp->method() == VCMethod::RANDOMIZER_CLEARCONSTRAINTS) {
                    foundClearConstraints = true;
                }
            });
            UASSERT_OBJ(!(hasRegistration && foundClearConstraints), stmtp,
                        "Block containing both variable registration and constraint clearing");
            if (hasRegistration) targetp->addStmtsp(stmtp->cloneTree(false));
            if (foundClearConstraints) break;
        }
    }

    static AstCExpr* newSolverCallp(AstVar* const genp) {
        AstCExpr* const callp = new AstCExpr{genp->fileline()};
        callp->dtypeSetBit();
        callp->add(new AstVarRef{genp->fileline(), VN_CAST(genp->user2p(), NodeModule), genp,
                                 VAccess::READWRITE});
        callp->add(".next(__Vm_rng)");
        return callp;
    }

    AstVar* addSizeSolvep(AstFunc* const randomizep, AstVar* const genp,
                          AstVar* const randModeVarp,
                          const VInsertionSet<AstVar*>& sizeArrayVars) {
        FileLine* const fl = randomizep->fileline();
        AstVar* const sizeOkVarp = new AstVar{fl, VVarType::BLOCKTEMP, "__Vsize_ok",
                                              randomizep->findBasicDType(VBasicDTypeKwd::BIT)};
        sizeOkVarp->funcLocal(true);
        randomizep->addDeclsp(sizeOkVarp);
        // A disabled array keeps its current size. Pin its size proxy before solving so
        // an incompatible size constraint fails instead of resizing the frozen array.
        for (AstVar* const arrVarp : sizeArrayVars) {
            addFrozenSizePin(fl, arrVarp, randomizep, genp, randModeVarp);
        }
        randomizep->addStmtsp(new AstAssign{fl, new AstVarRef{fl, sizeOkVarp, VAccess::WRITE},
                                            newSolverCallp(genp)});
        return sizeOkVarp;
    }

    // Rebuild constraints after resize
    void addConstraintRebuild(AstFunc* const randomizep, AstVar* const setupGenp,
                              AstVar* const solveGenp, const VInsertionSet<AstVar*>& sizeArrayVars,
                              AstNodeStmt* const setupStmtsp) {
        FileLine* const fl = randomizep->fileline();
        for (AstVar* const arrVarp : sizeArrayVars) {
            addArrayElemRefresh(fl, arrVarp, randomizep, setupGenp);
        }
        randomizep->addStmtsp(implementConstraintsClear(fl, setupGenp));
        randomizep->addStmtsp(setupStmtsp);
        for (AstVar* const arrVarp : sizeArrayVars) {
            randomizep->addStmtsp(newPinSizeVariable(fl, arrVarp, solveGenp));
        }
    }

public:
    // CONSTRUCTORS
    SolverSmtLowering(VMemberMap& memberMap, V3UniqueNames& uniqueNames,
                      const RandModeVars& modeVars, VNDeleter& deleter)
        : V3SolverLowering{memberMap, uniqueNames, modeVars, deleter} {}
    ~SolverSmtLowering() override = default;

    // V3SolverLowering
    void prepareClass(AstClass* classp) override { createRandomGenerator(classp); }
    void startClass(AstClass*) override {
        m_writtenVars.clear();  // Each class has its own set of written variables
    }
    void lowerConstraintMethod(AstNodeModule* modp, AstConstraint* constrp,
                               AstCMethodHard* nodep) override {
        // Replace '.size()' of a constrained array with a solver size variable
        FileLine* const fl = nodep->fileline();
        if (nodep->fromp()->user1()
            && (nodep->method() == VCMethod::ASSOC_SIZE
                || nodep->method() == VCMethod::DYN_SIZE)) {
            AstClass* const classp = VN_AS(modp, Class);
            AstVarRef* const queueVarRefp = VN_CAST(nodep->fromp(), VarRef);
            if (!queueVarRefp) {
                // Warning from ConstraintExprVisitor will be thrown
                return;
            }
            AstVar* const queueVarp = queueVarRefp->varp();
            bool wasCreated = false;
            AstVar* const sizeVarp
                = createOrGetSizeVar(classp, queueVarp, fl, nodep->findIntDType(), wasCreated);
            if (wasCreated) {
                // Associative arrays have no resize(); only generate resize
                // for dynamic arrays and queues
                if (!VN_IS(queueVarp->dtypep()->skipRefp(), AssocArrayDType)) {
                    AstTask* resizerTaskp = VN_AS(constrp->user3p(), Task);
                    if (!resizerTaskp) {
                        resizerTaskp = newResizeConstrainedArrayTask(classp, constrp->name());
                        constrp->user3p(resizerTaskp);
                    }
                    AstVarRef* const sizeVarRefp = new AstVarRef{
                        fl, VN_AS(sizeVarp->user2p(), NodeModule), sizeVarp, VAccess::READ};
                    AstCMethodHard* const resizep = new AstCMethodHard{
                        fl, nodep->fromp()->unlinkFrBack(), VCMethod::DYN_RESIZE, sizeVarRefp};
                    resizep->dtypep(nodep->findVoidDType());
                    resizerTaskp->addStmtsp(new AstStmtExpr{fl, resizep});
                }

                // Since size variable is signed int, we need additional constraint
                // to make sure it is always >= 0.
                constrp->addItemsp(createSizeGteZeroConstraint(fl, sizeVarp));
            }
            AstVarRef* const sizeVarRefp = new AstVarRef{fl, VN_AS(sizeVarp->user2p(), NodeModule),
                                                         sizeVarp, VAccess::READ};
            sizeVarRefp->user1(true);
            nodep->replaceWith(sizeVarRefp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }
    AstNodeExpr* lowerClassRandomize(AstClass* nodep, AstFunc* randomizep,
                                     AstVar* randModeVarp) override {
        m_distNum = 0;
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* beginValp = nullptr;
        AstVar* genp = SmtUtil::getRandomGenerator(nodep);
        if (genp) {
            // Phase 1: Process all constraints (create tasks, run ConstraintExprVisitor)
            // Setup task refs are NOT added to setupAllTaskp here -- done in phase 2
            AstTask* const prepareArraysTaskp = createPrepareConstrainedArraysTask(nodep);
            nodep->foreachMember([&](AstClass* const classp, AstConstraint* const constrp) {
                AstTask* taskp = VN_AS(constrp->user2p(), Task);
                if (!taskp) {
                    taskp = newSetupConstraintTask(classp, constrp->name());
                    constrp->user2p(taskp);
                }

                if (AstTask* const resizeTaskp = VN_CAST(constrp->user3p(), Task)) {
                    AstTask* const resizeAllTaskp = getCreateAggrResizeTask(nodep);
                    AstTaskRef* const resizeTaskRefp
                        = new AstTaskRef{constrp->fileline(), resizeTaskp};
                    resizeTaskRefp->classOrPackagep(classp);
                    resizeAllTaskp->addStmtsp(resizeTaskRefp->makeStmt());
                }

                if (constrp->itemsp()) expandUniqueElementList(constrp->itemsp());
                if (constrp->itemsp()) {
                    lowerDistConstraints(taskp, constrp->itemsp(), randModeVarp);
                }
                VInsertionSet<AstVar*>& sizeArrays = m_sizeConstrainedArrays[classp];
                ConstraintExprVisitor{
                    classp,        m_memberMap,  constrp->itemsp(), nullptr,
                    genp,          randModeVarp, m_writtenVars,     &m_uniqueConstraintId,
                    m_uniqueNames, randomizep,   &sizeArrays,       prepareArraysTaskp};
                if (constrp->itemsp()) {
                    taskp->addStmtsp(wrapIfConstraintMode(
                        nodep, constrp,
                        VN_AS(constrp->itemsp()->unlinkFrBackWithNext(), NodeStmt)));
                }
            });

            // Phase 2: Add setup task refs in depth order (deepest first = lowest priority)
            // Ensures outer-scope soft constraints override inner-scope (IEEE 18.5.13)
            {
                // Count nesting depth by GLOBAL_CONSTRAINT_SEPARATOR occurrences
                const auto constraintDepth = [](const AstConstraint* constrp) {
                    int depth = 0;
                    size_t pos = 0;
                    while ((pos = constrp->name().find(GLOBAL_CONSTRAINT_SEPARATOR, pos))
                           != std::string::npos) {
                        ++depth;
                        pos += std::strlen(GLOBAL_CONSTRAINT_SEPARATOR);
                    }
                    return depth;
                };
                int maxDepth = 0;
                nodep->foreachMember([&](AstClass* const, AstConstraint* const constrp) {
                    maxDepth = std::max(maxDepth, constraintDepth(constrp));
                });
                AstTask* const setupAllTaskp
                    = SmtUtil::getCreateConstraintSetupFunc(nodep, m_memberMap);
                for (int d = maxDepth; d >= 0; --d) {
                    nodep->foreachMember(
                        [&](AstClass* const classp, AstConstraint* const constrp) {
                            if (constraintDepth(constrp) != d) return;
                            AstTask* const taskp = VN_AS(constrp->user2p(), Task);
                            AstTaskRef* const setupTaskRefp
                                = new AstTaskRef{constrp->fileline(), taskp};
                            setupTaskRefp->classOrPackagep(classp);
                            setupAllTaskp->addStmtsp(setupTaskRefp->makeStmt());
                        });
                }
            }
            // For derived classes: clone write_var calls from parent's randomize()
            // and save every array that has is size-constrained array to generate
            // array element refresh later
            VInsertionSet<AstVar*> sizeArrayVars;
            if (nodep->extendsp()) {
                AstClass* parentClassp = nodep->extendsp()->classp();
                collectSizeConstrainedArrays(parentClassp, sizeArrayVars);
                while (parentClassp) {
                    AstFunc* const parentRandomizep
                        = VN_CAST(m_memberMap.findMember(parentClassp, "randomize"), Func);
                    if (parentRandomizep) copyVariableRegistrations(parentRandomizep, randomizep);
                    parentClassp
                        = parentClassp->extendsp() ? parentClassp->extendsp()->classp() : nullptr;
                }
            }
            randomizep->addStmtsp(implementConstraintsClear(fl, genp));

            const auto sizeArraysIt = m_sizeConstrainedArrays.find(nodep);
            if (sizeArraysIt != m_sizeConstrainedArrays.end()) {
                for (AstVar* const arrVarp : sizeArraysIt->second) sizeArrayVars.insert(arrVarp);
            }
            AstTask* const setupAllTaskp
                = SmtUtil::getCreateConstraintSetupFunc(nodep, m_memberMap);
            if (!sizeArrayVars.empty() && prepareArraysTaskp->stmtsp()) {
                AstNodeStmt* const preparep = (new AstTaskRef{fl, prepareArraysTaskp})->makeStmt();
                // A size-constrained array always has a preceding write_var registration.
                for (AstNode* stmtp = randomizep->stmtsp(); stmtp;  // LCOV_EXCL_BR_LINE
                     stmtp = stmtp->nextp()) {
                    bool writesArray = false;
                    stmtp->foreach([&](AstCMethodHard* methodp) {
                        writesArray |= methodp->method() == VCMethod::RANDOMIZER_WRITE_VAR;
                    });
                    if (!writesArray) continue;
                    stmtp->addHereThisAsNext(preparep);
                    break;
                }
            }
            AstTaskRef* const setupTaskRefp = new AstTaskRef{fl, setupAllTaskp};
            randomizep->addStmtsp(setupTaskRefp->makeStmt());

            if (!sizeArrayVars.empty()) {
                AstVar* const sizeOkVarp
                    = addSizeSolvep(randomizep, genp, randModeVarp, sizeArrayVars);
                if (AstTask* const resizeAllTaskp
                    = VN_AS(m_memberMap.findMember(nodep, "__Vresize_constrained_arrays"), Task)) {
                    randomizep->addStmtsp(
                        new AstIf{fl, new AstVarRef{fl, sizeOkVarp, VAccess::READ},
                                  (new AstTaskRef{fl, resizeAllTaskp})->makeStmt(), nullptr});
                }
                addConstraintRebuild(randomizep, genp, genp, sizeArrayVars,
                                     (new AstTaskRef{fl, setupAllTaskp})->makeStmt());

                AstVar* const finalOkVarp = new AstVar{fl, VVarType::BLOCKTEMP, "__Vfinal_ok",
                                                       nodep->findBasicDType(VBasicDTypeKwd::BIT)};
                finalOkVarp->funcLocal(true);
                randomizep->addDeclsp(finalOkVarp);
                randomizep->addStmtsp(new AstAssign{
                    fl, new AstVarRef{fl, finalOkVarp, VAccess::WRITE}, newSolverCallp(genp)});

                beginValp = new AstAnd{fl, new AstVarRef{fl, sizeOkVarp, VAccess::READ},
                                       new AstVarRef{fl, finalOkVarp, VAccess::READ}};
            } else {
                beginValp = newSolverCallp(genp);
            }
            if (randModeVarp) {
                AstNodeModule* const randModeClassp = VN_AS(randModeVarp->user2p(), Class);
                AstNodeFTask* const newp
                    = VN_AS(m_memberMap.findMember(randModeClassp, "new"), NodeFTask);
                UASSERT_OBJ(newp, randModeClassp, "No new() in class");
                addSetRandMode(newp, genp, randModeVarp);
            }
            if (AstVar* const staticRandModeVarp = getStaticRandModeVar(nodep)) {
                // Wire the shared static rand_mode queue into the class generator.
                AstNodeFTask* const newp = VN_AS(m_memberMap.findMember(nodep, "new"), NodeFTask);
                UASSERT_OBJ(newp, nodep, "No new() in class");
                addSetStaticRandMode(newp, genp, staticRandModeVarp);
            }
        } else {
            beginValp = new AstConst{fl, AstConst::WidthedValue{}, 32, 1};
        }

        addUpdateRandVarsBody(nodep, randomizep);
        return beginValp;
    }
    void addAfterClassSolve(AstClass* nodep, AstFunc* randomizep) override {
        const auto sizeArraysIt = m_sizeConstrainedArrays.find(nodep);
        const bool needsSizePhase
            = sizeArraysIt != m_sizeConstrainedArrays.end() && !sizeArraysIt->second.empty();
        // Size-only resize fallback (no element constraint, so no two-pass phase).
        // Must run after the solver .next() that sets the size variable.
        if (needsSizePhase) return;
        if (AstTask* const resizeAllTaskp
            = VN_AS(m_memberMap.findMember(nodep, "__Vresize_constrained_arrays"), Task)) {
            AstTaskRef* const resizeTaskRefp = new AstTaskRef{nodep->fileline(), resizeAllTaskp};
            randomizep->addStmtsp(resizeTaskRefp->makeStmt());
        }
    }
    void lowerInlineRandomize(AstNodeFTaskRef* nodep, AstClass* classp, AstFunc* randomizeFuncp,
                              AstNode* capturedTreep, const AstVar* thisVarp,
                              AstNodeExpr* basicRandomizeFuncCallp) override {
        AstVar* const classGenp = SmtUtil::getRandomGenerator(classp);
        AstVar* const localGenp
            = new AstVar{nodep->fileline(), VVarType::BLOCKTEMP, "randomizer",
                         classp->findBasicDType(VBasicDTypeKwd::RANDOM_GENERATOR)};
        localGenp->funcLocal(true);

        // Add constraints clearing code
        if (classGenp) {
            // Clone write_var calls from main randomize() for path-connected variables
            AstFunc* const mainRandomizep
                = VN_CAST(m_memberMap.findMember(classp, "randomize"), Func);
            if (mainRandomizep) copyVariableRegistrations(mainRandomizep, randomizeFuncp);
            randomizeFuncp->addStmtsp(
                implementConstraintsClear(randomizeFuncp->fileline(), classGenp));
        }

        randomizeFuncp->addDeclsp(localGenp);

        // Copy (derive) class constraints if present
        if (classGenp) {
            AstTask* const constrSetupFuncp
                = SmtUtil::getCreateConstraintSetupFunc(classp, m_memberMap);
            AstTaskRef* const callp = new AstTaskRef{nodep->fileline(), constrSetupFuncp};
            randomizeFuncp->addStmtsp(callp->makeStmt());
            randomizeFuncp->addStmtsp(new AstAssign{
                nodep->fileline(), new AstVarRef{nodep->fileline(), localGenp, VAccess::WRITE},
                new AstVarRef{nodep->fileline(), VN_AS(classGenp->user2p(), NodeModule), classGenp,
                              VAccess::READ}});
        }

        // Set rand mode if present (not needed if classGenp exists and was copied)
        AstVar* const randModeVarp = RandModeVars::randModeVarp(classp);
        if (!classGenp && randModeVarp) addSetRandMode(randomizeFuncp, localGenp, randModeVarp);
        if (!classGenp) {
            if (AstVar* const sVarp = getStaticRandModeVar(classp)) {
                addSetStaticRandMode(randomizeFuncp, localGenp, sVarp);
            }
        }

        // Generate constraint setup code and a hardcoded call to the solver
        AstBegin* const setupBlockp = new AstBegin{nodep->fileline(), "__Vsetup_constraints",
                                                   VN_AS(capturedTreep, NodeStmt), true};
        randomizeFuncp->addStmtsp(setupBlockp);

        // Pre-scan captured tree for .size on dynamic/assoc arrays and replace
        // with size variables, using shared createOrGetSizeVar helper.
        // After CaptureVisitor, fromp() of .size is AstMemberSel (not VarRef),
        // so extract the underlying variable from the MemberSel chain.
        // Collect the class-wide resize call and the with-block's own resize
        // statements to run after a successful solver call.
        AstNodeStmt* resizeStmtsp = nullptr;
        if (AstTask* const resizeAllTaskp
            = VN_AS(m_memberMap.findMember(classp, "__Vresize_constrained_arrays"), Task)) {
            resizeStmtsp = (new AstTaskRef{nodep->fileline(), resizeAllTaskp})->makeStmt();
        }
        {
            std::vector<AstCMethodHard*> sizeMethodps;
            capturedTreep->foreachAndNext([&](AstCMethodHard* methodp) {
                if (methodp->method() == VCMethod::DYN_SIZE
                    || methodp->method() == VCMethod::ASSOC_SIZE) {
                    sizeMethodps.push_back(methodp);
                }
            });
            for (AstCMethodHard* const methodp : sizeMethodps) {
                // Extract array variable from fromp (VarRef or MemberSel after capture)
                AstVar* arrVarp = nullptr;
                AstNodeExpr* const rootExprp = methodp->fromp();
                if (AstMemberSel* memberSelp = VN_CAST(rootExprp, MemberSel)) {
                    arrVarp = memberSelp->varp();
                    while (VN_IS(memberSelp->fromp(), MemberSel)) {
                        memberSelp = VN_CAST(memberSelp->fromp(), MemberSel);
                    }
                    // Only variables that are part of object that randomize is called on shall be
                    // randomized (18.6.1), skip randomization if deepest variable is reference to
                    // __Vthis
                    const AstNodeExpr* const fromp = memberSelp->fromp();
                    if (const AstVarRef* const varRefp = VN_CAST(fromp, VarRef)) {
                        if (varRefp->varp() == thisVarp) continue;
                    } else {
                        fromp->v3warn(E_UNSUPPORTED, "Unsupported: Unsupported size constraint "
                                                     "inside 'with' statement of type "
                                                         << fromp->dtypep()->prettyTypeName());
                    }
                } else if (AstVarRef* const varRefp = VN_CAST(rootExprp, VarRef)) {
                    arrVarp = varRefp->varp();
                }
                if (!arrVarp) continue;
                // Only handle rand-declared dynamic/assoc array variables
                if (!arrVarp->rand().isRandomizable()) continue;
                // Do not randomize associative array size (IEEE 18.4)
                if (VN_IS(arrVarp->dtypep()->skipRefp(), AssocArrayDType)) continue;
                FileLine* const fl = methodp->fileline();
                bool wasCreated = false;
                AstClass* const varClassp = VN_AS(arrVarp->user2p(), Class);
                AstVar* const sizeVarp = createOrGetSizeVar(varClassp, arrVarp, fl,
                                                            methodp->findIntDType(), wasCreated);
                // arrVarp and sizeVarp may live in a base class when the
                // array is inherited; route VarRefs through their declaring
                // class so V3Scope can resolve them.
                if (wasCreated) {
                    AstNodeExpr* const resizeVarRefp = buildMemberSelExprp(rootExprp, arrVarp);
                    AstNodeExpr* const sizeExprp = buildMemberSelExprp(rootExprp, sizeVarp);
                    // Append size >= 0 constraint so ConstraintExprVisitor processes it
                    capturedTreep->addNext(createSizeGteZeroConstraint(fl, sizeVarp, rootExprp));
                    AstCMethodHard* const resizep
                        = new AstCMethodHard{fl, resizeVarRefp, VCMethod::DYN_RESIZE, sizeExprp};
                    resizep->dtypep(methodp->findVoidDType());
                    resizeStmtsp = AstNode::addNext(resizeStmtsp, new AstStmtExpr{fl, resizep});
                }
                AstNodeExpr* const sizeNodeExprp = buildMemberSelExprp(rootExprp, sizeVarp);
                methodp->replaceWith(sizeNodeExprp);
                VL_DO_DANGLING(methodp->deleteTree(), methodp);
            }
        }

        // A pristine copy of the with-block's own constraint tree, taken before any
        // mutation, in case a size phase (below) needs to re-lower it a second time
        // against post-resize arrays.
        AstNode* const capturedClonep = capturedTreep->cloneTree(true);

        // Arrays that gain a size var from THIS with-block's own inline .size()==expr
        // constraint (as opposed to a class-level one) and are also referenced by a
        // unique{} constraint here; see the m_sizeConstrainedArraysp comment in
        // ConstraintExprVisitor::visit(AstConstraintUnique). Merged below with any
        // class-level size-constrained arrays.
        VInsertionSet<AstVar*> allSizeArrays;
        expandUniqueElementList(capturedTreep);
        ConstraintExprVisitor{classp,        m_memberMap,  capturedTreep, setupBlockp,
                              localGenp,     randModeVarp, m_writtenVars, &m_uniqueConstraintId,
                              m_uniqueNames, nullptr,      &allSizeArrays};

        // A with-block touching a size-constrained array (class-level, or made so by
        // its own inline .size()==expr above) needs the same two-phase solve as the
        // plain randomize() path above: solve once to pin down sizes, resize, then
        // rebuild and solve again so unique{}/element constraints see the arrays'
        // final (post-resize) length rather than their pre-solve (usually empty) one.
        FileLine* const fl = nodep->fileline();
        collectSizeConstrainedArrays(classp, allSizeArrays);
        const bool needsSizePhase = !allSizeArrays.empty();
        AstVar* const retVarp = randomizeFuncp->fvarp();

        if (needsSizePhase) {
            // Call __VBasicRand and stash its result FIRST, as its own statement,
            // before either solve. The single-statement form below (basicRandomizeFuncCallp
            // combined inline with the solver call) relies on statement hoisting emitting
            // __VBasicRand before the (one) solve call, so the solver's answer -- not
            // __VBasicRand's fallback fill of every rand array element -- is what sticks.
            // With two explicit solves as separate statements, that implicit ordering no
            // longer holds (the hoisted __VBasicRand call would land right before the LAST
            // statement that references it, i.e. after the final solve), so it is made
            // explicit here instead.
            AstVar* const basicOkVarp = new AstVar{fl, VVarType::BLOCKTEMP, "__Vbasic_ok",
                                                   classp->findBasicDType(VBasicDTypeKwd::BIT)};
            basicOkVarp->funcLocal(true);
            randomizeFuncp->addDeclsp(basicOkVarp);
            randomizeFuncp->addStmtsp(new AstAssign{
                fl, new AstVarRef{fl, basicOkVarp, VAccess::WRITE}, basicRandomizeFuncCallp});

            AstVar* const finalOkVarp = new AstVar{fl, VVarType::BLOCKTEMP, "__Vfinal_ok",
                                                   classp->findBasicDType(VBasicDTypeKwd::BIT)};
            finalOkVarp->funcLocal(true);
            randomizeFuncp->addDeclsp(finalOkVarp);

            // First pass: solve to determine sizes
            AstVar* const sizeOkVarp
                = addSizeSolvep(randomizeFuncp, localGenp, randModeVarp, allSizeArrays);

            // Resize constrained arrays before rebuilding constraints: both any
            // class-wide resize task (class-level size constraints) and this
            // with-block's own inline-size resize statements.
            if (resizeStmtsp) {
                AstIf* const ifp
                    = new AstIf{fl, new AstVarRef{fl, sizeOkVarp, VAccess::READ}, resizeStmtsp};
                randomizeFuncp->addStmtsp(ifp);
            }

            // Clear this call's constraints, then rebuild them fresh against the
            // resized arrays: the class's own constraints (re-copied from a freshly
            // re-run class setup, if any), and this with-block's own constraints
            // (re-lowered from the pristine clone snapshotted above).
            {
                AstCMethodHard* const clearp
                    = new AstCMethodHard{fl, new AstVarRef{fl, localGenp, VAccess::READWRITE},
                                         VCMethod::RANDOMIZER_CLEARCONSTRAINTS};
                clearp->dtypeSetVoid();
                randomizeFuncp->addStmtsp(clearp->makeStmt());
            }
            if (classGenp) {
                randomizeFuncp->addStmtsp(implementConstraintsClear(fl, classGenp));
                AstTask* const constrSetupFuncp2
                    = SmtUtil::getCreateConstraintSetupFunc(classp, m_memberMap);
                randomizeFuncp->addStmtsp((new AstTaskRef{fl, constrSetupFuncp2})->makeStmt());
                randomizeFuncp->addStmtsp(
                    new AstAssign{fl, new AstVarRef{fl, localGenp, VAccess::WRITE},
                                  new AstVarRef{fl, VN_AS(classGenp->user2p(), NodeModule),
                                                classGenp, VAccess::READ}});
            }

            // Refresh array element tables after resize, on localGenp -- AFTER the
            // classGenp copy above, so this overwrites whatever (possibly now-stale,
            // pre-resize) entry that copy brought in. write_var's compile-time,
            // once-ever registration (AstVar::user3()) does not re-run on the second
            // lowering pass below, so it is redone here by hand, same as the
            // class-level pattern above.
            for (AstVar* const arrVarp : allSizeArrays) {
                // The size var itself needs write_var'ing here too, unconditionally:
                // the pin below always references it by name, but nothing else in
                // THIS with-block's own (re-)lowered tree is guaranteed to touch it --
                // unlike the class-level pattern, where the class's constraint setup
                // always re-asserts the arr.size() == expr equality (and so always
                // write_vars the size var as a side effect), a with-block that adds
                // unique{} to an array sized by a *different* call/constraint has no
                // size-var reference of its own to trigger that.
                if (AstVar* const sizeVarp = VN_CAST(arrVarp->user4p(), Var)) {
                    AstCMethodHard* const sizeMethodp
                        = new AstCMethodHard{fl, new AstVarRef{fl, localGenp, VAccess::READWRITE},
                                             VCMethod::RANDOMIZER_WRITE_VAR};
                    sizeMethodp->dtypeSetVoid();
                    AstNodeModule* const sizeClassp = VN_AS(sizeVarp->user2p(), NodeModule);
                    AstVarRef* const sizeVarRefp
                        = new AstVarRef{fl, sizeClassp, sizeVarp, VAccess::WRITE};
                    sizeVarRefp->classOrPackagep(sizeClassp);
                    sizeMethodp->addPinsp(sizeVarRefp);
                    sizeMethodp->addPinsp(new AstConst{fl, AstConst::Unsized64{},
                                                       static_cast<uint64_t>(sizeVarp->width())});
                    AstNodeExpr* const sizeNamep = new AstCExpr{
                        fl, AstCExpr::Pure{}, "\"" + sizeVarp->name() + "\"", sizeVarp->width()};
                    sizeMethodp->addPinsp(sizeNamep);
                    sizeMethodp->addPinsp(new AstConst{fl, AstConst::Unsized64{}, 0});
                    randomizeFuncp->addStmtsp(sizeMethodp->makeStmt());
                }

                if (isDynArrOfClassTypeRecurse(arrVarp->dtypep())) {
                    const uint32_t unpackedDims = arrVarp->dtypep()->dimensions(false).second;
                    if (unpackedDims > 1) {
                        // A genuinely nested (unpackedDims > 1) dynamic array of
                        // class-typed elements already hits unrelated, pre-existing
                        // unsupported-constraint/internal-error paths well before
                        // reaching a randomize() with {} two-phase solve, so this
                        // can't currently be exercised from here.
                        arrVarp->v3warn(  // LCOV_EXCL_LINE
                            E_UNSUPPORTED,
                            "Unsupported: Nested array element access in global constraint");
                    }
                    continue;
                }
                AstCMethodHard* const methodp
                    = new AstCMethodHard{fl, new AstVarRef{fl, localGenp, VAccess::READWRITE},
                                         VCMethod::RANDOMIZER_WRITE_VAR};
                methodp->dtypeSetVoid();

                AstNodeModule* const arrClassp = VN_AS(arrVarp->user2p(), NodeModule);
                AstVarRef* const varRefp = new AstVarRef{fl, arrClassp, arrVarp, VAccess::WRITE};
                varRefp->classOrPackagep(arrClassp);
                methodp->addPinsp(varRefp);

                uint32_t dimension = 0;
                if (VN_IS(arrVarp->dtypep(), UnpackArrayDType)
                    || VN_IS(arrVarp->dtypep(), DynArrayDType)
                    || VN_IS(arrVarp->dtypep(), QueueDType)
                    || VN_IS(arrVarp->dtypep(), AssocArrayDType)) {
                    const std::pair<uint32_t, uint32_t> dims
                        = arrVarp->dtypep()->dimensions(/*includeBasic=*/true);
                    dimension = dims.second;
                }

                const size_t width = SmtUtil::arrayElementDTypep(arrVarp->dtypep())->width();
                methodp->addPinsp(new AstConst{fl, AstConst::Unsized64{}, width});
                AstNodeExpr* const varnamep = new AstCExpr{
                    fl, AstCExpr::Pure{}, "\"" + arrVarp->name() + "\"", arrVarp->width()};
                varnamep->dtypep(arrVarp->dtypep());
                methodp->addPinsp(varnamep);
                methodp->addPinsp(new AstConst{fl, AstConst::Unsized64{}, dimension});

                randomizeFuncp->addStmtsp(methodp->makeStmt());
            }

            expandUniqueElementList(capturedClonep);
            AstBegin* const elementSetupBlockp
                = new AstBegin{fl, "__Vsetup_constraints", VN_AS(capturedClonep, NodeStmt), true};
            randomizeFuncp->addStmtsp(elementSetupBlockp);
            ConstraintExprVisitor{
                classp,       m_memberMap,   capturedClonep,        elementSetupBlockp, localGenp,
                randModeVarp, m_writtenVars, &m_uniqueConstraintId, m_uniqueNames,      nullptr};

            // Pin the sizes so the final solve can't move them
            for (AstVar* const arrVarp : allSizeArrays) {
                randomizeFuncp->addStmtsp(newPinSizeVariable(fl, arrVarp, localGenp));
            }

            // Final solve: element values with sizes pinned
            AstCExpr* const solverCall2p = newSolverCallp(localGenp);
            randomizeFuncp->addStmtsp(
                new AstAssign{fl, new AstVarRef{fl, finalOkVarp, VAccess::WRITE}, solverCall2p});

            randomizeFuncp->addStmtsp(new AstAssign{
                fl, new AstVarRef{fl, retVarp, VAccess::WRITE},
                new AstAnd{fl,
                           new AstAnd{fl, new AstVarRef{fl, basicOkVarp, VAccess::READ},
                                      new AstVarRef{fl, sizeOkVarp, VAccess::READ}},
                           new AstVarRef{fl, finalOkVarp, VAccess::READ}}});
        } else {
            VL_DO_DANGLING(capturedClonep->deleteTree(), capturedClonep);

            // Call the solver and set return value
            AstCExpr* const solverCallp = newSolverCallp(localGenp);
            randomizeFuncp->addStmtsp(
                new AstAssign{fl, new AstVarRef{fl, retVarp, VAccess::WRITE},
                              new AstAnd{fl, basicRandomizeFuncCallp, solverCallp}});

            // Resize constrained arrays only when solver succeeds
            if (resizeStmtsp) {
                AstIf* const ifp
                    = new AstIf{fl, new AstVarRef{fl, retVarp, VAccess::READ}, resizeStmtsp};
                randomizeFuncp->addStmtsp(ifp);
            }
        }
    }
    AstNodeExpr* lowerStdRandomizeWith(AstNodeFTaskRef* nodep, AstFunc* randomizeFuncp,
                                       AstNode* capturedTreep, AstVar* stdrandp) override {
        FileLine* const fl = nodep->fileline();
        // Clear old constraints and variables for std::randomize with clause
        randomizeFuncp->addStmtsp(
            implementConstraintsClearAll(randomizeFuncp->fileline(), stdrandp));
        AstBegin* const setupBlockp
            = new AstBegin{fl, "__Vsetup_constraints", VN_AS(capturedTreep, NodeStmt), true};
        randomizeFuncp->addStmtsp(setupBlockp);
        {
            expandUniqueElementList(capturedTreep);
            ConstraintExprVisitor{nullptr,       m_memberMap, capturedTreep, setupBlockp,
                                  stdrandp,      nullptr,     m_writtenVars, &m_uniqueConstraintId,
                                  m_uniqueNames, nullptr};
        }
        AstCExpr* const solverCallp = new AstCExpr{fl};
        solverCallp->dtypeSetBit();
        solverCallp->add(new AstVarRef{fl, stdrandp, VAccess::READWRITE});
        solverCallp->add(".next()");
        return solverCallp;
    }
    AstNodeExpr* lowerCheckOnly(AstClass* classp, AstFunc* funcp) override {
        FileLine* const fl = classp->fileline();
        AstVar* const classGenp = SmtUtil::getRandomGenerator(classp);
        if (!classGenp) return new AstConst{fl, AstConst::WidthedValue{}, 32, 1};
        AstNodeModule* const genModp = VN_AS(classGenp->user2p(), NodeModule);
        funcp->addStmtsp(implementConstraintsClear(fl, classGenp));
        AstTask* const setupAllTaskp = SmtUtil::getCreateConstraintSetupFunc(classp, m_memberMap);
        funcp->addStmtsp((new AstTaskRef{fl, setupAllTaskp})->makeStmt());
        AstCExpr* const solverCallp = new AstCExpr{fl};
        solverCallp->dtypeSetBit();
        solverCallp->add(new AstVarRef{fl, genModp, classGenp, VAccess::READWRITE});
        solverCallp->add(".next_check_only(__Vm_rng)");
        classp->needRNG(true);
        return solverCallp;
    }
};

//######################################################################
// V3SolverSmt class functions

std::unique_ptr<V3SolverLowering> V3SolverSmt::newLowering(VMemberMap& memberMap,
                                                           V3UniqueNames& uniqueNames,
                                                           const RandModeVars& modeVars,
                                                           VNDeleter& deleter) const {
    return std::unique_ptr<V3SolverLowering>{
        new SolverSmtLowering{memberMap, uniqueNames, modeVars, deleter}};
}

std::vector<std::string> V3SolverSmt::runtimeCFlags() const {
    std::vector<std::string> cflags;
    const std::string solver = V3Options::getenvVERILATOR_SOLVER();
    if (solver != "") {
        cflags.emplace_back("-DVM_SOLVER_DEFAULT='\"" + V3OutFormatter::quoteNameControls(solver)
                            + "\"'");
    }
    const std::string sampler = V3Options::getenvVERILATOR_RAND_SAMPLER();
    if (sampler != "") {
        cflags.emplace_back("-DVM_RAND_SAMPLER_DEFAULT='\""
                            + V3OutFormatter::quoteNameControls(sampler) + "\"'");
    }
    return cflags;
}
