// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Parse module/signal name references
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
// LinkParse TRANSFORMATIONS:
//      Top-down traversal
//          Move some attributes around
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3LinkParse.h"

#include "V3Control.h"
#include "V3MemberMap.h"
#include "V3Stats.h"

#include <set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Link state, as a visitor of each AstNode

class LinkParseVisitor final : public VNVisitor {
    // NODE STATE
    // Cleared on netlist
    //  AstNode::user1()        -> bool.  True if processed
    //  AstNode::user2()        -> bool.  True if fileline recomputed
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;

    // TYPES
    using ImplTypedefMap = std::map<std::string, AstTypedef*>;

    // STATE - across all visitors
    std::unordered_set<FileLine*> m_filelines;  // Filelines that have been seen
    VMemberMap m_memberMap;  // for lookup of process class methods

    // STATE - for current visit position (use VL_RESTORER)
    // If set, move AstVar->valuep() initial values to this module
    ImplTypedefMap m_implTypedef;  // Created typedefs for each <container,name>
    AstVar* m_varp = nullptr;  // Variable we're under
    AstNodeModule* m_valueModp = nullptr;
    AstNodeModule* m_modp = nullptr;  // Current module
    bool m_inInterface = false;  // True when inside interface declaration
    AstNodeProcedure* m_procedurep = nullptr;  // Current procedure
    AstNodeFTask* m_ftaskp = nullptr;  // Current task
    AstNodeBlock* m_blockp = nullptr;  // Current AstNodeBlock
    AstNodeDType* m_dtypep = nullptr;  // Current data type
    AstNodeExpr* m_defaultInSkewp = nullptr;  // Current default input skew
    AstNodeExpr* m_defaultOutSkewp = nullptr;  // Current default output skew
    int m_anonUdpId = 0;  // Counter for anonymous UDP instances
    int m_genblkAbove = 0;  // Begin block number of if/case/for above
    int m_genblkNum = 0;  // Begin block number, 0=none seen
    int m_beginDepth = 0;  // How many begin blocks above current node within current AstNodeModule
    int m_randSequenceNum = 0;  // RandSequence uniqify number
    VLifetime m_lifetime = VLifetime::STATIC_IMPLICIT;  // Propagating lifetime
    bool m_insideLoop = false;  // True if the node is inside a loop
    bool m_lifetimeAllowed = false;  // True to allow lifetime settings
    bool m_moduleWithGenericIface = false;  // If current module contains generic interface

    // STATE - Statistic tracking
    VDouble0 m_statModules;  // Number of modules seen

    bool m_unprotectedStdProcess
        = false;  // Set when std::process internals were unprotected, we only need to do this once

    // METHODS
    void cleanFileline(AstNode* nodep) {
        if (nodep->user2SetOnce()) return;  // Process once
        // We make all filelines unique per AstNode.  This allows us to
        // later turn off messages on a fileline when an issue is found
        // so that messages on replicated blocks occur only once,
        // without suppressing other token's messages as a side effect.
        // We could have verilog.l create a new one on every token,
        // but that's a lot more structures than only doing AST nodes.
        // TODO: Many places copy the filename when suppressing warnings,
        // perhaps audit to make consistent and this is no longer needed
        if (m_filelines.find(nodep->fileline()) != m_filelines.end()) {
            nodep->fileline(new FileLine{nodep->fileline()});
        }
        m_filelines.insert(nodep->fileline());
    }

    string nameFromTypedef(AstNode* nodep) {
        // Try to find a name for a typedef'ed enum/struct
        if (const AstTypedef* const typedefp = VN_CAST(nodep->backp(), Typedef)) {
            // Create a name for the enum, to aid debug and tracing
            // This name is not guaranteed to be globally unique (due to later parameterization)
            string above;
            if (m_modp && VN_IS(m_modp, Package)) {
                above = m_modp->name() + "::";
            } else if (m_modp) {
                above = m_modp->name() + ".";
            }
            return above + typedefp->name();
        }
        return "";
    }

    void unprotectStdProcessHandle() {
        if (m_unprotectedStdProcess) return;
        m_unprotectedStdProcess = true;
        if (!v3Global.opt.protectIds()) return;
        if (AstPackage* const stdp = v3Global.rootp()->stdPackagep()) {
            if (AstClass* const processp
                = VN_CAST(m_memberMap.findMember(stdp, "process"), Class)) {
                if (AstVar* const handlep
                    = VN_CAST(m_memberMap.findMember(processp, "m_process"), Var)) {
                    handlep->protect(false);
                }
            }
        }
    }

    void visitIterateNodeDType(AstNodeDType* nodep) {
        if (nodep->user1SetOnce()) return;  // Process only once.
        cleanFileline(nodep);
        VL_RESTORER(m_dtypep);
        m_dtypep = nodep;
        iterateChildren(nodep);
    }

    bool nestedIfBegin(AstGenBlock* nodep) {  // Point at begin inside the GenIf
        // IEEE says directly nested item is not a new block
        // The genblk name will get attached to the if true/false LOWER begin block(s)
        //    1: GENIF
        // -> 1:3: GENBLOCK [IMPLIED]  // nodep passed to this function
        //    1:3:1: GENIF
        //    1:3:1:2: GENBLOCK genblk1 [IMPLIED]
        const AstNode* const backp = nodep->backp();
        return (nodep->implied()  // User didn't provide begin/end
                && VN_IS(backp, GenIf) && VN_CAST(backp, GenIf)->elsesp() == nodep
                && !nodep->nextp()  // No other statements under upper genif else
                && (VN_IS(nodep->itemsp(), GenIf))  // Begin has if underneath
                && !nodep->itemsp()->nextp());  // Has only one item
    }

    void checkIndent(AstNode* nodep, AstNode* childp) {
        // Try very hard to avoid false positives
        AstNode* nextp = nodep->nextp();
        if (!childp) return;
        if (!nextp && VN_IS(nodep, Loop) && VN_IS(nodep->backp(), Begin))
            nextp = nodep->backp()->nextp();
        if (!nextp) return;
        if (VN_IS(childp, Begin) || VN_IS(childp, GenBlock)) return;
        FileLine* const nodeFlp = nodep->fileline();
        FileLine* const childFlp = childp->fileline();
        FileLine* const nextFlp = nextp->fileline();
        // UINFO(0, "checkInd " << nodeFlp->firstColumn() << " " << nodep);
        // UINFO(0, "  child  " << childFlp->firstColumn() << " " << childp);
        // UINFO(0, " next    " << nextFlp->firstColumn() << " " << nextp);
        // Same filename, later line numbers (no macro magic going on)
        if (nodeFlp->filenameno() != childFlp->filenameno()) return;
        if (nodeFlp->filenameno() != nextFlp->filenameno()) return;
        if (nodeFlp->lastLineno() >= childFlp->firstLineno()) return;
        if (childFlp->lastLineno() >= nextFlp->firstLineno()) return;
        // This block has indent 'a'
        // Child block has indent 'b' where indent('b') > indent('a')
        // Next block has indent 'b'
        // (note similar code below)
        if (!(nodeFlp->firstColumn() < childFlp->firstColumn()
              && nextFlp->firstColumn() >= childFlp->firstColumn()))
            return;
        // Might be a tab difference in spaces up to the node prefix, if so
        // just ignore this warning
        // Note it's correct we look at nodep's column in all of these
        const std::string nodePrefix = nodeFlp->sourcePrefix(nodeFlp->firstColumn());
        const std::string childPrefix = childFlp->sourcePrefix(nodeFlp->firstColumn());
        const std::string nextPrefix = nextFlp->sourcePrefix(nodeFlp->firstColumn());
        if (childPrefix != nodePrefix) return;
        if (nextPrefix != childPrefix) return;
        // Some file lines start after the indentation, so make another check
        // using actual file contents
        const std::string nodeSource = nodeFlp->source();
        const std::string childSource = childFlp->source();
        const std::string nextSource = nextFlp->source();
        if (!(VString::leadingWhitespaceCount(nodeSource)
                  < VString::leadingWhitespaceCount(childSource)
              && VString::leadingWhitespaceCount(nextSource)
                     >= VString::leadingWhitespaceCount(childSource)))
            return;
        nextp->v3warn(MISINDENT,
                      "Misleading indentation\n"
                          << nextp->warnContextPrimary() << '\n'
                          << nodep->warnOther()
                          << "... Expected indentation matching this earlier statement's line:\n"
                          << nodep->warnContextSecondary());
    }

    void addForkParentProcess(AstFork* forkp) {
        FileLine* const fl = forkp->fileline();

        const std::string parentName = "__VforkParent";
        AstRefDType* const dtypep = new AstRefDType{fl, "process"};
        AstVar* const parentVar
            = new AstVar{fl, VVarType::BLOCKTEMP, parentName, VFlagChildDType{}, dtypep};
        parentVar->lifetime(VLifetime::AUTOMATIC_EXPLICIT);

        AstParseRef* const lhsp = new AstParseRef{fl, parentName, nullptr, nullptr};
        AstClassOrPackageRef* const processRefp
            = new AstClassOrPackageRef{fl, "process", nullptr, nullptr};
        AstParseRef* const selfRefp = new AstParseRef{fl, "self", nullptr, nullptr};
        AstDot* const processSelfp = new AstDot{fl, true, processRefp, selfRefp};
        AstMethodCall* const callp = new AstMethodCall{fl, processSelfp, "self", nullptr};
        AstAssign* const initp = new AstAssign{fl, lhsp, callp};

        AstVarRef* const parentRefp = new AstVarRef{fl, parentVar, VAccess::READ};
        forkp->parentProcessp(parentRefp);

        VNRelinker relinker;
        forkp->unlinkFrBack(&relinker);

        parentVar->addNextHere(initp);
        initp->addNextHere(forkp);

        AstBegin* const beginp = new AstBegin{
            fl, forkp->name() == "" ? "" : forkp->name() + "__VgetForkParent", parentVar, true};

        relinker.relink(beginp);
    }

    // VISITORS
    void visit(AstNodeFTask* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process only once.
        // Mark class methods
        if (VN_IS(m_modp, Class)) nodep->classMethod(true);

        V3Control::applyFTask(m_modp, nodep);
        cleanFileline(nodep);
        VL_RESTORER(m_ftaskp);
        m_ftaskp = nodep;
        VL_RESTORER(m_lifetime);
        VL_RESTORER(m_lifetimeAllowed);
        m_lifetimeAllowed = true;
        if (!nodep->lifetime().isNone()) {
            m_lifetime = nodep->lifetime().makeImplicit();
        } else {
            if (nodep->classMethod()) {
                // Class methods are automatic by default
                m_lifetime = VLifetime::AUTOMATIC_IMPLICIT;
            } else if (nodep->dpiImport() || VN_IS(nodep, Property)) {
                // DPI-imported functions and properties don't have lifetime specifiers
                m_lifetime = VLifetime::NONE;
            }
            nodep->lifetime(m_lifetime);
        }
        if (nodep->classMethod() && nodep->lifetime().isStatic()) {
            nodep->v3error("Class function/task cannot be static lifetime ('"
                           << nodep->verilogKwd() << " static') (IEEE 1800-2023 6.21)\n"
                           << nodep->warnMore() << "... May have intended 'static "
                           << nodep->verilogKwd() << "'");
        }
        iterateChildren(nodep);
    }
    void visit(AstNodeDType* nodep) override { visitIterateNodeDType(nodep); }
    void visit(AstConstraint* nodep) override {
        v3Global.useRandomizeMethods(true);
        iterateChildren(nodep);
    }
    void visit(AstEnumDType* nodep) override {
        if (nodep->name() == "") {
            nodep->name(nameFromTypedef(nodep));  // Might still remain ""
        }
        visitIterateNodeDType(nodep);
    }
    void visit(AstNodeUOrStructDType* nodep) override {
        if (nodep->name() == "") {
            nodep->name(nameFromTypedef(nodep));  // Might still remain ""
        }
        visitIterateNodeDType(nodep);
    }
    void visit(AstEnumItem* nodep) override {
        // Expand ranges
        cleanFileline(nodep);
        iterateChildren(nodep);
        if (nodep->rangep()) {
            if (VL_UNCOVERABLE(!VN_IS(nodep->rangep()->leftp(), Const)  // LCOV_EXCL_START
                               || !VN_IS(nodep->rangep()->rightp(), Const))) {
                // We check this rule in the parser, so shouldn't fire
                nodep->v3error("Enum ranges must be integral, per spec");
            }  // LCOV_EXCL_STOP
            const int left = nodep->rangep()->leftConst();
            const int right = nodep->rangep()->rightConst();
            const int increment = (left > right) ? -1 : 1;
            uint32_t offset_from_init = 0;
            AstEnumItem* addp = nullptr;
            FileLine* const flp = nodep->fileline();
            for (int i = left; i != (right + increment); i += increment, ++offset_from_init) {
                const string name = nodep->name() + cvtToStr(i);
                AstNodeExpr* valuep = nullptr;
                if (nodep->valuep()) {
                    // V3Width looks for Adds with same fileline as the EnumItem
                    valuep
                        = new AstAdd{flp, nodep->valuep()->cloneTree(true),
                                     new AstConst{flp, AstConst::Unsized32{}, offset_from_init}};
                }
                addp = AstNode::addNext(addp, new AstEnumItem{flp, name, nullptr, valuep});
            }
            nodep->replaceWith(addp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }

    void visit(AstVar* nodep) override {
        cleanFileline(nodep);
        if (nodep->lifetime().isStatic() && m_insideLoop && nodep->valuep()) {
            nodep->lifetime(VLifetime::AUTOMATIC_IMPLICIT);
            nodep->v3warn(STATICVAR, "Static variable with assignment declaration declared in a "
                                     "loop converted to automatic");
        } else if (nodep->valuep() && nodep->lifetime().isNone() && m_lifetime.isStatic()
                   && !nodep->isIO()
                   && !nodep->isParam()
                   // In task, or a procedure but not Initial/Final as executed only once
                   && ((m_ftaskp && !m_ftaskp->lifetime().isStaticExplicit())
                       || (m_procedurep && !VN_IS(m_procedurep, Initial)
                           && !VN_IS(m_procedurep, Final)))) {
            if (VN_IS(m_modp, Module) && m_ftaskp) {
                m_ftaskp->v3warn(
                    IMPLICITSTATIC,
                    "Function/task's lifetime implicitly set to static\n"
                        << m_ftaskp->warnMore() << "... Suggest use '" << m_ftaskp->verilogKwd()
                        << " automatic' or '" << m_ftaskp->verilogKwd() << " static'\n"
                        << m_ftaskp->warnContextPrimary() << '\n'
                        << nodep->warnOther() << "... Location of implicit static variable\n"
                        << nodep->warnMore() << "... The initializer value will only be set once\n"
                        << nodep->warnContextSecondary());
            } else {
                nodep->v3warn(IMPLICITSTATIC,
                              "Variable's lifetime implicitly set to static\n"
                                  << nodep->warnMore()
                                  << "... The initializer value will only be set once\n"
                                  << nodep->warnMore()
                                  << "... Suggest use 'static' before variable declaration'");
            }
        }
        if (!m_lifetimeAllowed && nodep->lifetime().isAutomatic()) {
            nodep->v3error(
                "Module variables cannot have automatic lifetime (IEEE 1800-2023 6.21): "
                << nodep->prettyNameQ());
            nodep->lifetime(VLifetime::STATIC_IMPLICIT);
        }
        if (!nodep->direction().isAny()) {  // Not a port
            if (nodep->lifetime().isNone()) {
                if (m_lifetimeAllowed) {
                    nodep->lifetime(m_lifetime);
                } else {  // Module's always static per IEEE 1800-2023 6.21
                    nodep->lifetime(VLifetime::STATIC_IMPLICIT);
                }
            }
        } else if (m_ftaskp) {
            if (!nodep->lifetime().isAutomatic()) nodep->lifetime(VLifetime::AUTOMATIC_IMPLICIT);
        } else if (nodep->lifetime().isNone()) {
            // lifetime shouldn't be unknown, set static if none
            nodep->lifetime(VLifetime::STATIC_IMPLICIT);
        }

        if (nodep->isGParam() && !nodep->isAnsi()) {  // shadow some parameters into localparams
            if (m_beginDepth > 0
                || (m_beginDepth == 0
                    && (m_modp->hasParameterList() || VN_IS(m_modp, Class)
                        || VN_IS(m_modp, Package)))) {
                nodep->varType(VVarType::LPARAM);
            }
        }
        if (nodep->isGParam() && m_modp) m_modp->hasGParam(true);

        if (nodep->isParam() && !nodep->valuep()
            && nodep->fileline()->language() < V3LangCode::L1800_2009) {
            nodep->v3warn(NEWERSTD,
                          "Parameter requires default value, or use IEEE 1800-2009 or later.");
        }

        // Mark parameters declared inside interfaces
        if (nodep->isParam() && m_inInterface) { nodep->isIfaceParam(true); }
        if (AstParseTypeDType* const ptypep = VN_CAST(nodep->subDTypep(), ParseTypeDType)) {
            // It's a parameter type. Use a different node type for this.
            AstNode* dtypep = nodep->valuep();
            if (dtypep) {
                dtypep->unlinkFrBack();
                // Transform right-associative Dot tree to left-associative
                // This handles typedef with arrayed interface on first component:
                //   typedef if0[0].x_if0.rq_t my_t;
                // Grammar produces: DOT(SELBIT, DOT(x_if0, rq_t))
                // We need:          DOT(DOT(SELBIT, x_if0), rq_t)
                if (AstNodeExpr* exprp = VN_CAST(dtypep, NodeExpr)) {
                    AstDot* dotp = VN_CAST(exprp, Dot);
                    while (dotp) {
                        AstDot* rhsDotp = VN_CAST(dotp->rhsp(), Dot);
                        if (!rhsDotp) break;
                        FileLine* const fl = dotp->fileline();
                        const bool colon = dotp->colon();
                        AstNodeExpr* const lhs = VN_AS(dotp->lhsp()->unlinkFrBack(), NodeExpr);
                        AstNodeExpr* const rhsLhs
                            = VN_AS(rhsDotp->lhsp()->unlinkFrBack(), NodeExpr);
                        AstNodeExpr* const rhsRhs
                            = VN_AS(rhsDotp->rhsp()->unlinkFrBack(), NodeExpr);
                        FileLine* const rhsFl = rhsDotp->fileline();
                        const bool rhsColon = rhsDotp->colon();
                        AstDot* const newLhs = new AstDot{fl, colon, lhs, rhsLhs};
                        exprp = new AstDot{rhsFl, rhsColon, newLhs, rhsRhs};
                        VL_DO_DANGLING(dotp->deleteTree(), dotp);
                        dotp = VN_CAST(exprp, Dot);
                    }
                    dtypep = exprp;
                }
            } else {
                dtypep = new AstVoidDType{nodep->fileline()};
            }

            AstNode* const newp = new AstParamTypeDType{
                nodep->fileline(), nodep->varType(),
                ptypep->fwdType(), nodep->name(),
                VFlagChildDType{}, new AstRequireDType{nodep->fileline(), dtypep}};
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            return;
        }
        m_moduleWithGenericIface |= VN_IS(nodep->childDTypep(), IfaceGenericDType);

        // Maybe this variable has a signal attribute
        V3Control::applyVarAttr(m_modp, m_ftaskp, nodep);

        if (v3Global.opt.anyPublicFlat() && nodep->varType().isVPIAccessible()) {
            if (v3Global.opt.publicFlatRW()) {
                nodep->sigUserRWPublic(true);
            } else if (v3Global.opt.publicParams() && nodep->isParam()) {
                nodep->sigUserRWPublic(true);
            } else if (m_modp && v3Global.opt.publicDepth()) {
                if ((m_modp->depth() - 1) <= v3Global.opt.publicDepth()) {
                    nodep->sigUserRWPublic(true);
                } else if (VN_IS(m_modp, Package) && nodep->isParam()) {
                    nodep->sigUserRWPublic(true);
                }
            }
        }

        // We used modTrace before leveling, and we may now
        // want to turn it off now that we know the levelizations
        if (v3Global.opt.traceDepth() && m_modp
            && (m_modp->depth() - 1) > v3Global.opt.traceDepth()) {
            m_modp->modTrace(false);
            nodep->trace(false);
        }
        m_varp = nodep;

        iterateChildren(nodep);
        m_varp = nullptr;
        // temporaries under an always aren't expected to be blocking
        if (m_procedurep && VN_IS(m_procedurep, Always))
            nodep->fileline()->modifyWarnOff(V3ErrorCode::BLKSEQ, true);
        if (nodep->valuep()) {
            FileLine* const fl = nodep->valuep()->fileline();
            // A variable with an = value can be 4 things:
            if (nodep->isParam() || (m_ftaskp && nodep->isNonOutput())) {
                // 1. Parameters and function inputs: It's a default to use if not overridden
            } else if (!m_ftaskp && !VN_IS(m_modp, Class) && nodep->isNonOutput()
                       && !nodep->isInput()) {
                // 2. Module inout/ref/constref: const default to use
                nodep->v3warn(E_UNSUPPORTED,
                              "Unsupported: Default value on module inout/ref/constref: "
                                  << nodep->prettyNameQ());
                nodep->valuep()->unlinkFrBack()->deleteTree();
            } else if (m_blockp) {
                // 3. Under blocks, it's an initial value to be under an assign
                // TODO: This is wrong if it's a static variable right?
                FileLine* const newfl = new FileLine{fl};
                newfl->warnOff(V3ErrorCode::E_CONSTWRITTEN, true);
                m_blockp->addStmtsp(
                    new AstAssign{newfl, new AstVarRef{newfl, nodep, VAccess::WRITE},
                                  VN_AS(nodep->valuep()->unlinkFrBack(), NodeExpr)});
            } else if (m_valueModp) {
                // 4. Under modules/class, it's the time 0 initialziation value
                // Making an AstAssign (vs AstAssignW) to a wire is an error, suppress it
                FileLine* const newfl = new FileLine{fl};
                newfl->warnOff(V3ErrorCode::PROCASSWIRE, true);
                newfl->warnOff(V3ErrorCode::E_CONSTWRITTEN, true);
                // Create a ParseRef to the wire. We cannot use the var as it may be deleted if
                // it's a port (see t_var_set_link.v)
                AstAssign* const assp
                    = new AstAssign{newfl, new AstParseRef{newfl, nodep->name()},
                                    VN_AS(nodep->valuep()->unlinkFrBack(), NodeExpr)};
                if (nodep->lifetime().isAutomatic()) {
                    nodep->addNextHere(new AstInitialAutomatic{newfl, assp});
                } else {
                    nodep->addNextHere(new AstInitialStatic{newfl, assp});
                }
            } else {
                nodep->v3fatalSrc("Variable with initializer in unexpected position");
            }
        }
    }
    void visit(AstConst* nodep) override {
        if (nodep->num().autoExtend() && nodep->fileline()->language() < V3LangCode::L1800_2005) {
            nodep->v3warn(NEWERSTD, "Unbased unsized literals require IEEE 1800-2005 or later.");
        }
    }

    void visit(AstAttrOf* nodep) override {
        cleanFileline(nodep);
        iterateChildren(nodep);
        if (nodep->attrType() == VAttrType::DT_PUBLIC) {
            AstTypedef* const typep = VN_AS(nodep->backp(), Typedef);
            UASSERT_OBJ(typep, nodep, "Attribute not attached to typedef");
            typep->attrPublic(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (nodep->attrType() == VAttrType::VAR_FORCEABLE) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->setForceable();
            v3Global.setHasForceableSignals();
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (nodep->attrType() == VAttrType::VAR_PUBLIC) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->sigUserRWPublic(true);
            m_varp->sigModPublic(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (nodep->attrType() == VAttrType::VAR_PUBLIC_FLAT) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->sigUserRWPublic(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (nodep->attrType() == VAttrType::VAR_PUBLIC_FLAT_RD) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->sigUserRdPublic(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (nodep->attrType() == VAttrType::VAR_PUBLIC_FLAT_RW) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->sigUserRWPublic(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (nodep->attrType() == VAttrType::VAR_ISOLATE_ASSIGNMENTS) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->attrIsolateAssign(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (nodep->attrType() == VAttrType::VAR_SFORMAT) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->attrSFormat(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (nodep->attrType() == VAttrType::VAR_SPLIT_VAR) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            if (!VN_IS(m_modp, Module)) {
                m_varp->v3warn(
                    SPLITVAR,
                    m_varp->prettyNameQ()
                        << " has split_var metacomment, "
                           "but will not be split because it is not declared in a module.");
            } else {
                m_varp->attrSplitVar(true);
            }
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (nodep->attrType() == VAttrType::VAR_SC_BIGUINT) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->attrScBigUint(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (nodep->attrType() == VAttrType::VAR_SC_BV) {
            UASSERT_OBJ(m_varp, nodep, "Attribute not attached to variable");
            m_varp->attrScBv(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        }
    }

    void visit(AstDefImplicitDType* nodep) override {
        cleanFileline(nodep);
        UINFO(8, "   DEFIMPLICIT " << nodep);
        // Must remember what names we've already created, and combine duplicates
        // so that for "var enum {...} a,b" a & b will share a common typedef.
        // Change to unique name space per module so that an addition of
        // a new type won't change every verilated module.
        AstTypedef* defp = nullptr;
        const ImplTypedefMap::iterator it = m_implTypedef.find(nodep->name());
        if (it != m_implTypedef.end()) {
            defp = it->second;
            UINFO(9, "Reused impltypedef " << nodep << "  -->  " << defp);
        } else {
            // Definition must be inserted right after the variable (etc) that needed it
            // AstVar, AstTypedef, AstNodeFTask, AstParamTypeDType are common containers
            AstNode* backp = nodep->backp();
            for (; backp; backp = backp->backp()) {
                if (VN_IS(backp, Var) || VN_IS(backp, Typedef) || VN_IS(backp, NodeFTask)
                    || VN_IS(backp, ParamTypeDType))
                    break;
            }
            UASSERT_OBJ(backp, nodep,
                        "Implicit enum/struct type created under unexpected node type");
            AstNodeDType* const dtypep = nodep->childDTypep();
            dtypep->unlinkFrBack();
            if (VN_IS(backp, Typedef) || VN_IS(backp, ParamTypeDType)) {
                // A typedef doesn't need us to make yet another level of typedefing
                // For typedefs just remove the AstRefDType level of abstraction
                nodep->replaceWith(dtypep);
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
                return;
            } else {
                defp = new AstTypedef{nodep->fileline(), nodep->name(), nullptr, VFlagChildDType{},
                                      dtypep};
                m_implTypedef.emplace(defp->name(), defp);
                // Rename so that name doesn't change if a type is added/removed elsewhere
                // But the m_implTypedef is stil by old name so we can find it for next new lookups
                defp->name("__typeimpmod" + cvtToStr(m_implTypedef.size()));
                UINFO(9, "New impltypedef " << defp);
                backp->addNextHere(defp);
            }
        }
        nodep->replaceWith(new AstRefDType{nodep->fileline(), defp->name()});
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }

    void visit(AstDelay* nodep) override {
        cleanFileline(nodep);
        UASSERT_OBJ(m_modp, nodep, "Delay not under module");
        nodep->timeunit(m_modp->timeunit());
        iterateChildren(nodep);
    }

    void visit(AstNodeForeach* nodep) override {
        // FOREACH(array, loopvars, body)
        UINFO(9, "FOREACH " << nodep);
        cleanFileline(nodep);
        // Separate iteration vars from base from variable
        // Input:
        //      v--- arrayp
        //   1. DOT(DOT(first, second), ASTSELLOOPVARS(third, var0..var1))
        // Separated:
        //   bracketp = ASTSELLOOPVARS(...)
        //   arrayp = DOT(DOT(first, second), third)
        //   firstVarp = var0..var1
        // Other examples
        //   2. ASTSELBIT(first, var0))
        //   3. ASTSELLOOPVARS(first, var0..var1))
        //   4. DOT(DOT(first, second), ASTSELBIT(third, var0))
        VL_RESTORER(m_insideLoop);
        m_insideLoop = true;
        AstNode* bracketp = nodep->arrayp();
        while (AstDot* dotp = VN_CAST(bracketp, Dot)) bracketp = dotp->rhsp();
        if (AstSelBit* const selp = VN_CAST(bracketp, SelBit)) {
            // Convert to AstSelLoopVars so V3LinkDot knows what's being defined
            AstNode* const newp
                = new AstSelLoopVars{selp->fileline(), selp->fromp()->unlinkFrBack(),
                                     selp->bitp()->unlinkFrBackWithNext()};
            selp->replaceWith(newp);
            VL_DO_DANGLING2(selp->deleteTree(), selp, bracketp);
        } else if (VN_IS(bracketp, SelLoopVars)) {
            // Ok
        } else {
            nodep->v3error("Foreach missing bracketed loop variable is no-operation"
                           " (IEEE 1800-2023 12.7.3)");
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            return;
        }
        iterateChildren(nodep);
    }
    void visit(AstRepeat* nodep) override {
        cleanFileline(nodep);
        VL_RESTORER(m_insideLoop);
        m_insideLoop = true;
        checkIndent(nodep, nodep->stmtsp());
        iterateChildren(nodep);
    }
    void visit(AstLoop* nodep) override {
        cleanFileline(nodep);
        VL_RESTORER(m_insideLoop);
        m_insideLoop = true;
        if (VN_IS(nodep->stmtsp(), LoopTest)) {
            checkIndent(nodep, nodep->stmtsp()->nextp());
        } else {
            checkIndent(nodep, nodep->stmtsp());
        }
        iterateChildren(nodep);
    }
    void visit(AstWait* nodep) override {
        cleanFileline(nodep);
        iterateChildren(nodep);
        if (nodep->condp()->isZero()) {
            // Special case "wait(0)" we won't throw WAITCONST as user wrote
            // it that way with presumed intent - UVM does this.
            FileLine* const newfl = nodep->fileline();
            newfl->warnOff(V3ErrorCode::WAITCONST, true);
            nodep->fileline(newfl);
        }
    }
    void visit(AstNodeModule* nodep) override {
        V3Control::applyModule(nodep);
        ++m_statModules;
        if (VN_IS(nodep, Class) && VN_CAST(nodep, Class)->isInterfaceClass()
            && VN_IS(m_modp, Class) && VN_CAST(m_modp, Class)->isInterfaceClass()) {
            nodep->v3error("Interface class shall not be nested within another interface class."
                           " (IEEE 1800-2023 8.26)");
        }

        VL_RESTORER(m_modp);
        VL_RESTORER(m_inInterface);
        VL_RESTORER(m_anonUdpId);
        VL_RESTORER(m_genblkAbove);
        VL_RESTORER(m_genblkNum);
        VL_RESTORER(m_beginDepth);
        VL_RESTORER(m_implTypedef);
        VL_RESTORER(m_lifetime);
        VL_RESTORER(m_lifetimeAllowed);
        VL_RESTORER(m_moduleWithGenericIface);
        VL_RESTORER(m_randSequenceNum);
        VL_RESTORER(m_valueModp);

        // Module: Create sim table for entire module and iterate
        cleanFileline(nodep);
        // Classes inherit from upper package
        if (m_modp && nodep->timeunit().isNone()) nodep->timeunit(m_modp->timeunit());
        m_modp = nodep;
        if (VN_IS(nodep, Iface)) m_inInterface = true;  // Start or stay within interface
        m_anonUdpId = 0;
        m_genblkAbove = 0;
        m_genblkNum = 0;
        m_beginDepth = 0;
        m_implTypedef.clear();
        m_valueModp = nodep;
        m_lifetime = nodep->lifetime().makeImplicit();
        m_lifetimeAllowed = VN_IS(nodep, Class);
        m_moduleWithGenericIface = false;
        m_randSequenceNum = 0;

        if (m_lifetime.isNone()) {
            m_lifetime
                = VN_IS(nodep, Class) ? VLifetime::AUTOMATIC_IMPLICIT : VLifetime::STATIC_IMPLICIT;
        }
        if (nodep->name() == "TOP") {
            // May mess up scope resolution and cause infinite loop
            nodep->v3warn(E_UNSUPPORTED, "Module cannot be named 'TOP' as conflicts with "
                                         "Verilator top-level internals");
        }
        iterateChildren(nodep);
        if (AstModule* const modp = VN_CAST(nodep, Module)) {
            modp->hasGenericIface(m_moduleWithGenericIface);
        }
    }
    void visitIterateNoValueMod(AstNode* nodep) {
        // Iterate a node which any Var within shouldn't create an InitialAutomatic procedure
        cleanFileline(nodep);
        VL_RESTORER(m_valueModp);
        m_valueModp = nullptr;
        iterateChildren(nodep);
    }
    void visit(AstNodeProcedure* nodep) override {
        VL_RESTORER(m_lifetimeAllowed);
        m_lifetimeAllowed = true;
        VL_RESTORER(m_procedurep);
        m_procedurep = nodep;
        visitIterateNoValueMod(nodep);
    }
    void visit(AstCover* nodep) override { visitIterateNoValueMod(nodep); }
    void visit(AstRestrict* nodep) override { visitIterateNoValueMod(nodep); }

    void visit(AstGenBlock* nodep) override {
        V3Control::applyCoverageBlock(m_modp, nodep);
        cleanFileline(nodep);
        VL_RESTORER(m_beginDepth);
        ++m_beginDepth;
        const AstNode* const backp = nodep->backp();
        // IEEE says directly nested item is not a new block
        // The genblk name will get attached to the if true/false LOWER begin block(s)
        const bool nestedIf = nestedIfBegin(nodep);
        // It's not FOR(BEGIN(...)) but we earlier changed it to BEGIN(FOR(...))
        int assignGenBlkNum = -1;
        if (nodep->genforp()) {
            ++m_genblkNum;
            if (nodep->name() == "") assignGenBlkNum = m_genblkNum;
        } else if (nodep->name() == "" && (VN_IS(backp, GenCaseItem) || VN_IS(backp, GenIf))
                   && !nestedIf) {
            assignGenBlkNum = m_genblkAbove;
        }
        if (assignGenBlkNum != -1) {
            nodep->name("genblk" + cvtToStr(assignGenBlkNum));
            if (nodep->itemsp()) {
                nodep->v3warn(GENUNNAMED,
                              "Unnamed generate block "
                                  << nodep->prettyNameQ() << " (IEEE 1800-2023 27.6)\n"
                                  << nodep->warnMore()
                                  << "... Suggest assign a label with 'begin : gen_<label_name>'");
            }
        }

        if (nodep->name() != "") {
            VL_RESTORER(m_genblkAbove);
            VL_RESTORER(m_genblkNum);
            m_genblkAbove = 0;
            m_genblkNum = 0;
            iterateChildren(nodep);
        } else {
            iterateChildren(nodep);
        }
    }
    void visit(AstGenCase* nodep) override {
        ++m_genblkNum;
        cleanFileline(nodep);
        VL_RESTORER(m_genblkAbove);
        VL_RESTORER(m_genblkNum);
        m_genblkAbove = m_genblkNum;
        m_genblkNum = 0;
        iterateChildren(nodep);
    }
    void visit(AstGenIf* nodep) override {
        cleanFileline(nodep);
        checkIndent(nodep, nodep->elsesp() ? nodep->elsesp() : nodep->thensp());
        const bool nestedIf = (VN_IS(nodep->backp(), GenBlock)
                               && nestedIfBegin(VN_CAST(nodep->backp(), GenBlock)));
        if (nestedIf) {
            iterateChildren(nodep);
        } else {
            ++m_genblkNum;
            VL_RESTORER(m_genblkAbove);
            VL_RESTORER(m_genblkNum);
            m_genblkAbove = m_genblkNum;
            m_genblkNum = 0;
            iterateChildren(nodep);
        }
    }
    void visit(AstCell* nodep) override {
        if (nodep->origName().empty()) {
            if (!VN_IS(nodep->modp(), Primitive)) {  // Module/Program/Iface
                nodep->modNameFileline()->v3error("Instance of " << nodep->modp()->verilogKwd()
                                                                 << " must be named");
            }
            // UDPs can have empty instance names. Assigning unique names for them to prevent any
            // conflicts
            const string newName = "$unnamedudp" + cvtToStr(++m_anonUdpId);
            nodep->name(newName);
            nodep->origName(newName);
        }
        iterateChildren(nodep);
    }
    void visit(AstNodeBlock* nodep) override {
        {
            VL_RESTORER(m_blockp);
            m_blockp = nodep;
            // Temporarily unlink the statements so variable initializers can be inserted in order
            AstNode* const stmtsp = nodep->stmtsp();
            if (stmtsp) stmtsp->unlinkFrBackWithNext();
            iterateAndNextNull(nodep->declsp());
            nodep->addStmtsp(stmtsp);
        }

        if (AstBegin* const beginp = VN_CAST(nodep, Begin)) {
            V3Control::applyCoverageBlock(m_modp, beginp);
        }
        cleanFileline(nodep);
        iterateAndNextNull(nodep->stmtsp());
        if (AstFork* const forkp = VN_CAST(nodep, Fork)) {
            iterateAndNextNull(forkp->forksp());
            if (!forkp->parentProcessp() && forkp->joinType().joinNone() && forkp->forksp())
                addForkParentProcess(forkp);
        }
    }
    void visit(AstCase* nodep) override {
        V3Control::applyCase(nodep);
        cleanFileline(nodep);
        iterateChildren(nodep);
    }
    void visit(AstDot* nodep) override {
        cleanFileline(nodep);
        iterateChildren(nodep);
        if (VN_IS(nodep->lhsp(), ParseRef) && nodep->lhsp()->name() == "super"
            && VN_IS(nodep->rhsp(), New)) {
            // Look for other statements until hit function start
            AstNode* scanp = nodep;
            // Skip over the New's statement
            for (; scanp && !VN_IS(scanp, StmtExpr); scanp = scanp->backp()) {}
            if (VN_IS(scanp, StmtExpr)) {  // Ignore warning if something not understood
                scanp = scanp->backp();
                for (; scanp; scanp = scanp->backp()) {
                    if (VN_IS(scanp, NodeStmt) || VN_IS(scanp, NodeModule)
                        || VN_IS(scanp, NodeFTask))
                        break;
                }
                if (!VN_IS(scanp, NodeFTask)) {
                    nodep->rhsp()->v3error(
                        "'super.new' not first statement in new function (IEEE 1800-2023 8.15)\n"
                        << nodep->rhsp()->warnContextPrimary() << scanp->warnOther()
                        << "... Location of earlier statement\n"
                        << scanp->warnContextSecondary());
                }
            }
        }
    }
    void visit(AstIf* nodep) override {
        cleanFileline(nodep);
        checkIndent(nodep, nodep->elsesp() ? nodep->elsesp() : nodep->thensp());
        iterateChildren(nodep);
    }
    void visit(AstPrintTimeScale* nodep) override {
        // Inlining may change hierarchy, so just save timescale where needed
        cleanFileline(nodep);
        iterateChildren(nodep);
        nodep->name(m_modp->name());
        nodep->timeunit(m_modp->timeunit());
    }
    void visit(AstRandSequence* nodep) override {
        cleanFileline(nodep);
        nodep->name("__Vrs" + std::to_string(m_randSequenceNum++));
        iterateChildren(nodep);
    }
    void visit(AstSFormatF* nodep) override {
        cleanFileline(nodep);
        iterateChildren(nodep);
        nodep->timeunit(m_modp->timeunit());
    }
    void visit(AstSScanF* nodep) override {
        cleanFileline(nodep);
        iterateChildren(nodep);
        nodep->timeunit(m_modp->timeunit());
    }
    void visit(AstTime* nodep) override {
        cleanFileline(nodep);
        iterateChildren(nodep);
        nodep->timeunit(m_modp->timeunit());
    }
    void visit(AstTimeD* nodep) override {
        cleanFileline(nodep);
        iterateChildren(nodep);
        nodep->timeunit(m_modp->timeunit());
    }
    void visit(AstTimeImport* nodep) override {
        cleanFileline(nodep);
        iterateChildren(nodep);
        nodep->timeunit(m_modp->timeunit());
    }
    void visit(AstTimeUnit* nodep) override {
        cleanFileline(nodep);
        iterateChildren(nodep);
        nodep->timeunit(m_modp->timeunit());
    }
    void visit(AstEventControl* nodep) override {
        cleanFileline(nodep);
        iterateChildren(nodep);
        AstAlways* const alwaysp = VN_CAST(nodep->backp(), Always);
        if (alwaysp && alwaysp->keyword() == VAlwaysKwd::ALWAYS_COMB) {
            alwaysp->v3error("Event control statements not legal under always_comb "
                             "(IEEE 1800-2023 9.2.2.2.2)\n"
                             << alwaysp->warnMore() << "... Suggest use a normal 'always'");
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (alwaysp && !alwaysp->sentreep()) {
            // If the event control is at the top, move the sentree to the always
            if (AstSenTree* const sentreep = nodep->sentreep()) {
                sentreep->unlinkFrBackWithNext();
                alwaysp->sentreep(sentreep);
            }
            if (nodep->stmtsp()) alwaysp->addStmtsp(nodep->stmtsp()->unlinkFrBackWithNext());
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        }
    }
    void visit(AstClocking* nodep) override {
        cleanFileline(nodep);
        VL_RESTORER(m_defaultInSkewp);
        VL_RESTORER(m_defaultOutSkewp);
        // Find default input and output skews
        for (AstNode *nextp, *itemp = nodep->itemsp(); itemp; itemp = nextp) {
            nextp = itemp->nextp();
            if (AstClockingItem* citemp = VN_CAST(itemp, ClockingItem)) {
                if (citemp->exprp() || citemp->assignp()) continue;
                if (citemp->skewp()) {
                    if (citemp->direction() == VDirection::INPUT) {
                        // Disallow default redefinition; note some simulators allow this
                        if (m_defaultInSkewp) {
                            citemp->skewp()->v3error("Multiple default input skews not allowed");
                        }
                        m_defaultInSkewp = citemp->skewp();
                    } else if (citemp->direction() == VDirection::OUTPUT) {
                        // Disallow default redefinition; note some simulators allow this
                        if (m_defaultOutSkewp) {
                            citemp->skewp()->v3error("Multiple default output skews not allowed");
                        }
                        m_defaultOutSkewp = citemp->skewp();
                    } else {
                        citemp->v3fatalSrc("Incorrect direction");
                    }
                }
                VL_DO_DANGLING2(pushDeletep(citemp->unlinkFrBack()), citemp, itemp);
            }
        }
        iterateChildren(nodep);
    }
    void visit(AstClockingItem* nodep) override {
        cleanFileline(nodep);
        if (nodep->direction() == VDirection::OUTPUT) {
            if (!nodep->skewp()) {
                if (m_defaultOutSkewp) {
                    nodep->skewp(m_defaultOutSkewp->cloneTree(false));
                } else {
                    // Default is 0 (IEEE 1800-2023 14.3)
                    nodep->skewp(new AstConst{nodep->fileline(), 0});
                }
            }
        } else if (nodep->direction() == VDirection::INPUT) {
            if (!nodep->skewp()) {
                if (m_defaultInSkewp) {
                    nodep->skewp(m_defaultInSkewp->cloneTree(false));
                } else {
                    // Default is 1step (IEEE 1800-2023 14.3)
                    nodep->skewp(new AstConst{nodep->fileline(), AstConst::OneStep{}});
                }
            }
        }
        iterateChildren(nodep);
    }
    void visit(AstPackageImport* nodep) override {
        cleanFileline(nodep);
        if (m_modp && !m_ftaskp && VN_IS(m_modp, Class)) {
            nodep->v3error("Import statement directly within a class scope is illegal");
        }
        iterateChildren(nodep);
    }

    void visit(AstNode* nodep) override {
        // Default: Just iterate
        cleanFileline(nodep);
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit LinkParseVisitor(AstNetlist* rootp) {
        unprotectStdProcessHandle();
        iterate(rootp);
    }
    ~LinkParseVisitor() override {
        V3Stats::addStatSum(V3Stats::STAT_SOURCE_MODULES, m_statModules);
    }
};

//######################################################################
// Link class functions

void V3LinkParse::linkParse(AstNetlist* rootp) {
    UINFO(4, __FUNCTION__ << ": ");
    { LinkParseVisitor{rootp}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("linkparse", 0, dumpTreeEitherLevel() >= 6);
}
