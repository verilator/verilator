// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Build the run time model descriptors (RTMD)
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
// V3Rtmd's Transformations:
//
// Builds (buildAll) the run time model descriptors (RTMD), which describe the model state as
// data for whatever reads it at run time, tracing first. Runs after V3LinkLevel::wrapTop, and
// before V3Begin, while the source hierarchy (generate and begin blocks, function and task
// statics) is still intact.
//
//  Data types:
//      One AstNodeRtmdDataType per distinct data type, and one AstRtmdVarType per distinct
//      data type, variable kind and direction, all held by the AstTypeTable. Built bottom up, and
//      deduplicated structurally. A data type that cannot be represented has no descriptor, and
//      variables of that type are not described.
//
//  Hierarchy levels:
//      One AstRtmdHier per module, interface and package, except the constant pool. The level
//      of the top module ($root) is the ROOT. Its items are, in source order, the variables, the
//      interface references, the instances (partitions for --lib-create models), and nested
//      levels for named generate and begin blocks, forks, functions and tasks. The variables of
//      the ROOT are instead under a nested ROOTIO level, which is not part of any path. V3Scope
//      then clones the levels per instance, and inlines each into the level of the instance above,
//      leaving a single tree under the AstTopScope, which is emitted flattened as PUSH, items,
//      POP.
//
//  Scoped (scopedAll, in V3RtmdScoped.cpp):
//      After V3Scope, finishes the descriptors, knowing the hierarchical path of each variable.
//
// Only static variables are described. SystemC variables, virtual interface references,
// classes and primitives are not.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Rtmd.h"

#include "V3Ast.h"
#include "V3DupFinder.h"
#include "V3Error.h"
#include "V3String.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Builds the data type descriptors held by the AstTypeTable

class RtmdTypeBuilder final {
    // NODE STATE
    //  AstNodeDType::user1()   -> bool. user2p is valid
    //  AstNodeDType::user2p()  -> AstNodeRtmdDataType*. RTMD data type (might be nullptr)
    // VNUser4InUse     In V3Hasher via V3DupFinder

    const VNUser1InUse m_user1InUse;
    const VNUser2InUse m_user2InUse;

    // STATE
    // The TypeTable holding every type descriptor
    AstTypeTable* const m_typeTablep;
    // The primitive 'bit' type
    AstNodeDType* const m_bitDtypep = m_typeTablep->findBitDType();
    // The primitive 'logic' type
    AstNodeDType* const m_logicDtypep = m_typeTablep->findLogicDType();
    // To share structurally identical descriptor instances
    V3DupFinder m_dupFinder;

    // METHODS
    AstNodeRtmdDataType* newRtmdDataType(const AstBasicDType* dtypep) {
        FileLine* const flp = dtypep->fileline();

        const VBasicDTypeKwd kwd = dtypep->keyword();

        // Ranged bit/logic types are really packed arrays
        if (dtypep->isRanged() && kwd.isBitLogic()) {
            const int l = dtypep->left();
            const int r = dtypep->right();
            AstNodeRtmdDataType* const elemp = kwd.isBit() ? dataType(m_bitDtypep)  //
                                                           : dataType(m_logicDtypep);
            return new AstRtmdDTPackedArray{flp, elemp, l, r, dtypep->isSigned()};
        }

        switch (kwd) {
        case VBasicDTypeKwd::BIT:
        case VBasicDTypeKwd::LOGIC:
        case VBasicDTypeKwd::BYTE:
        case VBasicDTypeKwd::SHORTINT:
        case VBasicDTypeKwd::INT:
        case VBasicDTypeKwd::LONGINT:
        case VBasicDTypeKwd::INTEGER:
        case VBasicDTypeKwd::DOUBLE:
        case VBasicDTypeKwd::CHANDLE:
        case VBasicDTypeKwd::TIME:
        case VBasicDTypeKwd::EVENT:
            // Supported in RTMD
            return new AstRtmdDTAtom{flp, kwd, dtypep->isSigned()};

        case VBasicDTypeKwd::UINT32:
        case VBasicDTypeKwd::UINT64:
            // Internal unsigned values are 'bit [width-1:0]'
            return new AstRtmdDTPackedArray{flp, dataType(m_bitDtypep), kwd.width() - 1, 0, false};

        default:  // Unsupported in RTMD
            return nullptr;
        }
    }

    AstNodeRtmdDataType* newRtmdDataType(AstEnumDType* dtypep) {
        // Descriptor of the underlying type
        AstNodeRtmdDataType* const basep = dataType(dtypep->subDTypep());
        if (!basep) return nullptr;

        AstRtmdDTEnum* const enump
            = new AstRtmdDTEnum{dtypep->fileline(), dtypep->prettyName(), basep};
        for (AstEnumItem* const itemp : dtypep->itemspList()) {
            const AstConst* const constp = VN_AS(itemp->valuep(), Const);
            const std::string value = constp->num().displayed(dtypep, "%0b");
            enump->addItemsp(new AstRtmdEnumItem{itemp->fileline(), itemp->prettyName(), value});
        }
        return enump;
    }

    AstNodeRtmdDataType* newRtmdDataType(AstPackArrayDType* dtypep) {
        // Descriptor of the element type
        AstNodeRtmdDataType* const elemp = dataType(dtypep->subDTypep());
        if (!elemp) return nullptr;

        FileLine* const flp = dtypep->fileline();
        const int l = dtypep->left();
        const int r = dtypep->right();
        const bool isSigned = dtypep->isSigned();
        return new AstRtmdDTPackedArray{flp, elemp, l, r, isSigned};
    }

    AstNodeRtmdDataType* newRtmdDataType(AstUnpackArrayDType* dtypep) {
        // Descriptor of the element type
        AstNodeRtmdDataType* const elemp = dataType(dtypep->subDTypep());
        if (!elemp) return nullptr;

        FileLine* const flp = dtypep->fileline();
        const int l = dtypep->left();
        const int r = dtypep->right();
        return new AstRtmdDTUnpackedArray{flp, dtypep, elemp, l, r};
    }

    AstNodeRtmdDataType* newRtmdDataType(AstStructDType* dtypep) {
        // Gather all members
        AstRtmdMember* membersp = nullptr;
        for (AstMemberDType* const memberDTypep : dtypep->memberspList()) {
            AstNodeRtmdDataType* const typep = dataType(memberDTypep->subDTypep());
            // If member is not representable, the whole type is not representable
            if (!typep) {
                if (membersp) VL_DO_DANGLING(membersp->deleteTree(), membersp);
                return nullptr;
            }
            FileLine* const flp = memberDTypep->fileline();
            const std::string name = memberDTypep->prettyName();
            // Packed members record their bit offset, unpacked ones are located by the emitter
            const uint32_t lsb = dtypep->packed() ? memberDTypep->lsb() : 0;
            membersp = AstNode::addNext(membersp, new AstRtmdMember{flp, name, typep, lsb});
        }

        FileLine* const flp = dtypep->fileline();
        if (dtypep->packed()) return new AstRtmdDTPackedStruct{flp, dtypep->isSigned(), membersp};
        return new AstRtmdDTUnpackedStruct{flp, dtypep, membersp};
    }

    AstNodeRtmdDataType* newRtmdDataType(AstUnionDType* dtypep) {
        // Only packed unions are supported for now
        if (!dtypep->packed()) return nullptr;

        // Gather all members
        AstRtmdMember* membersp = nullptr;
        for (AstMemberDType* const memberDTypep : dtypep->memberspList()) {
            AstNodeRtmdDataType* const typep = dataType(memberDTypep->subDTypep());
            // If member is not representable, the whole type is not representable
            if (!typep) {
                if (membersp) VL_DO_DANGLING(membersp->deleteTree(), membersp);
                return nullptr;
            }
            FileLine* const flp = memberDTypep->fileline();
            const std::string name = memberDTypep->prettyName();
            const uint32_t lsb = memberDTypep->lsb();
            membersp = AstNode::addNext(membersp, new AstRtmdMember{flp, name, typep, lsb});
        }

        FileLine* const flp = dtypep->fileline();
        return new AstRtmdDTPackedUnion{flp, dtypep->isSigned(), membersp};
    }
    // Build the descriptor for the given data type
    AstNodeRtmdDataType* newDataType(AstNodeDType* dtypep) {
        // Dispatch to type specific function above
        AstNodeRtmdDataType* const descp = [&]() -> AstNodeRtmdDataType* {
            if (AstBasicDType* const dtp = VN_CAST(dtypep, BasicDType)) {
                return newRtmdDataType(dtp);
            }
            if (AstRefDType* const dtp = VN_CAST(dtypep, RefDType)) {
                return dataType(dtp->subDTypep());  // TODO: eventually should be emitted
            }
            if (AstParamTypeDType* const dtp = VN_CAST(dtypep, ParamTypeDType)) {
                return dataType(dtp->subDTypep());
            }
            if (AstConstDType* const dtp = VN_CAST(dtypep, ConstDType)) {
                return dataType(dtp->subDTypep());
            }
            if (AstEnumDType* const dtp = VN_CAST(dtypep, EnumDType)) {
                return newRtmdDataType(dtp);
            }
            if (AstPackArrayDType* const dtp = VN_CAST(dtypep, PackArrayDType)) {
                return newRtmdDataType(dtp);
            }
            if (AstUnpackArrayDType* const dtp = VN_CAST(dtypep, UnpackArrayDType)) {
                return newRtmdDataType(dtp);
            }
            if (AstStructDType* const dtp = VN_CAST(dtypep, StructDType)) {
                return newRtmdDataType(dtp);
            }
            if (AstUnionDType* const dtp = VN_CAST(dtypep, UnionDType)) {
                return newRtmdDataType(dtp);
            }
            // Straight unsupported types (for now)
            if (VN_IS(dtypep, AssocArrayDType)) return nullptr;
            if (VN_IS(dtypep, WildcardArrayDType)) return nullptr;
            if (VN_IS(dtypep, DynArrayDType)) return nullptr;
            if (VN_IS(dtypep, QueueDType)) return nullptr;
            if (VN_IS(dtypep, ClassRefDType)) return nullptr;
            if (VN_IS(dtypep, IfaceRefDType)) return nullptr;
            // Fatal error for all other types
            dtypep->v3fatalSrc("Unhandled data type: " + dtypep->prettyTypeNameQ());
            return nullptr;  // LCOV_EXCL_LINE - unreachable
        }();

        // Might not be representable
        if (!descp) return nullptr;

        // Might already be the canonical node (is under the TypeTable), dupFinder won't find it
        if (descp->backp()) return descp;

        // Reuse equivalent descriptor if there is one
        const auto it = m_dupFinder.findDuplicate(descp);
        if (it != m_dupFinder.end()) {
            VL_DO_DANGLING(descp->deleteTree(), descp);
            return VN_AS(it->second, NodeRtmdDataType);
        }

        // Use the new descriptor
        m_typeTablep->addRtmdDataTypesp(descp);
        m_dupFinder.insert(descp);
        return descp;
    }

public:
    // Return the canonical data type descriptor, or nullptr if cannot be represented
    AstNodeRtmdDataType* dataType(AstNodeDType* dtypep) {
        if (!dtypep->user1SetOnce()) dtypep->user2p(newDataType(dtypep));
        return VN_AS(dtypep->user2p(), NodeRtmdDataType);
    }

    // Return the canonical var type descriptor
    AstRtmdVarType* varType(const AstVar* varp, AstNodeRtmdDataType* rtmdTypep) {
        const VRtmdVarKind kind = varp->varType().rtmdVarKind();
        const VDirection direction = varp->declDirection();
        FileLine* const flp = varp->fileline();
        AstRtmdVarType* const descp = new AstRtmdVarType{flp, rtmdTypep, kind, direction};

        // Reuse equivalent descriptor if there is one
        const auto it = m_dupFinder.findDuplicate(descp);
        if (it != m_dupFinder.end()) {
            VL_DO_DANGLING(descp->deleteTree(), descp);
            return VN_AS(it->second, RtmdVarType);
        }

        // Use the new descriptor
        m_typeTablep->addRtmdVarTypesp(descp);
        m_dupFinder.insert(descp);
        return descp;
    }

    // CONSTRUCTORS
    explicit RtmdTypeBuilder(AstNetlist* netlistp)
        : m_typeTablep{netlistp->typeTablep()} {
        UASSERT_OBJ(!m_typeTablep->rtmdDataTypesp(), netlistp, "Duplicate data type descriptors");
        UASSERT_OBJ(!m_typeTablep->rtmdVarTypesp(), netlistp, "Duplicate var type descriptors");
    }
    ~RtmdTypeBuilder() = default;
    VL_UNCOPYABLE(RtmdTypeBuilder);
};

//######################################################################
// Builds the descriptor of each module, interface and package: a hierarchy level holding its
// variables and instances, and the nested hierarchy levels of its named blocks

class RtmdBuilder final : public VNVisitor {
    // STATE
    RtmdTypeBuilder m_typeBuilder;  // Builds the data type and var type descriptors
    AstRtmdHier* m_levelp = nullptr;  // Hierarchy level being built
    AstRtmdHier* m_rootIop = nullptr;  // The ROOTIO level of the root module being built

    // METHODS

    static std::string rtmdName(const AstNode* nodep) {
        return AstNode::prettyName(VName::dehash(nodep->name()));
    }

    void addItem(AstNodeRtmdItem* itemp, AstRtmdHier* overridep = nullptr) {
        (overridep ? overridep : m_levelp)->addItemsp(itemp);
    }

    void visitModule(AstNodeModule* nodep, VRtmdHierKind kind) {
        UASSERT_OBJ(!m_levelp, nodep, "Should not nest");

        FileLine* const flp = nodep->fileline();
        AstRtmdHier* const levelp
            = new AstRtmdHier{flp, AstNode::prettyName(nodep->origName()), kind};
        VL_RESTORER(m_levelp);
        m_levelp = levelp;
        iterateChildren(nodep);
        nodep->rtmdp(levelp);
    }

    void visitScope(AstNode* nodep, VRtmdHierKind kind, bool transparent) {
        UASSERT_OBJ(m_levelp, nodep, nodep->prettyTypeNameQ() + " not under Module");

        // TODO: Unnamed scopes should not exist here, they should all be named
        if (transparent || nodep->name().empty()) {
            iterateChildren(nodep);
            return;
        }

        FileLine* const flp = nodep->fileline();
        AstRtmdHier* const levelp = new AstRtmdHier{flp, rtmdName(nodep), kind};
        addItem(levelp);
        VL_RESTORER(m_levelp);
        m_levelp = levelp;
        iterateChildren(nodep);
    }

    // VISITORS

    // NodeModule subclasses - They are scopes, hold Rtmd until flattening in V3Scope
    void visit(AstNodeModule* nodep) override {
        nodep->v3fatalSrc("Unhandled NodeModule sub type");  // Everything handled explicitly
    }
    void visit(AstClass* nodep) override {
        // TODO: static vars under classes should be included
    }
    void visit(AstClassPackage* nodep) override {
        nodep->v3fatalSrc("AstClassPackage should not exist at this stage");
    }
    void visit(AstIface* nodep) override {
        UASSERT_OBJ(!nodep->isTop(), nodep, "Interface should not be top");
        visitModule(nodep, VRtmdHierKind::INTERFACE);
    }
    void visit(AstModule* nodep) override {
        if (nodep->verilatorLib()) return;  // Partition wrapper handled in the partitions

        // The $root top wrapper is special
        if (nodep->isTop()) {
            // The variables of the root module are held in its ROOTIO level
            VL_RESTORER(m_rootIop);
            m_rootIop = new AstRtmdHier{nodep->fileline(), "$rootio", VRtmdHierKind::ROOTIO};
            // Walk the root module
            visitModule(nodep, VRtmdHierKind::ROOT);
            // Insert the ROOTIO level
            if (!m_rootIop->itemsp()) {
                // If empty, just drop it
                VL_DO_DANGLING(m_rootIop->deleteTree(), m_rootIop);
            } else {
                // Otherwise add to front of the root module's descriptor
                AstNode* const firstp = nodep->rtmdp()->itemsp();
                UASSERT_OBJ(firstp, nodep, "Root module without instances");
                firstp->addHereThisAsNext(m_rootIop);
            }
            return;
        }

        // Regular module
        visitModule(nodep, VRtmdHierKind::MODULE);
    }
    void visit(AstNotFoundModule* nodep) override {
        nodep->v3fatalSrc("AstNotFoundModule should not exist at this stage");
    }
    void visit(AstPackage* nodep) override {
        if (nodep->isConstPool()) return;  // The constant pool holds no design state
        UASSERT_OBJ(!nodep->isTop(), nodep, "Package should not be top");
        visitModule(nodep, VRtmdHierKind::PACKAGE);
    }
    void visit(AstPrimitive* nodep) override {
        // Skipped
    }

    // Cells - They link hierarchies until flattening in V3Scope
    void visit(AstCell* nodep) override {
        UASSERT_OBJ(m_levelp, nodep, "Cell not under Module");
        UASSERT_OBJ(!nodep->name().empty(), nodep, "Unnamed cell");

        AstNodeModule* const modp = nodep->modp();
        if (modp->isConstPool()) return;  // Skip the constant pool
        if (VN_IS(modp, Primitive)) return;  // Skip primitives

        FileLine* const flp = nodep->fileline();
        if (modp->verilatorLib()) {
            addItem(new AstRtmdPartition{flp, rtmdName(nodep)});
        } else {
            addItem(new AstRtmdInstance{flp, rtmdName(nodep), nodep});
        }
    }

    // Scopes
    void visit(AstGenBlock* nodep) override {  //
        visitScope(nodep, VRtmdHierKind::GENERATE, nodep->implied());
    }
    void visit(AstBegin* nodep) override {  //
        visitScope(nodep, VRtmdHierKind::BEGIN, nodep->implied());
    }
    void visit(AstFork* nodep) override {  //
        visitScope(nodep, VRtmdHierKind::FORK, false);
    }
    void visit(AstFunc* nodep) override {  //
        if (nodep->dpiImport()) return;
        visitScope(nodep, VRtmdHierKind::FUNCTION, false);
    }
    void visit(AstTask* nodep) override {  //
        if (nodep->dpiImport()) return;
        visitScope(nodep, VRtmdHierKind::TASK, false);
    }

    // Variables
    void visit(AstVar* nodep) override {
        UASSERT_OBJ(m_levelp, nodep, "Var not under Module");

        // Only static variables
        if (!nodep->lifetime().isStatic()) return;
        // Skip weird stuff
        if (nodep->isSc()) return;

        FileLine* const flp = nodep->fileline();

        // Interface references need to be recorded explicitly
        if (const AstIfaceRefDType* const irdtypep
            = VN_CAST(nodep->dtypep()->skipRefp(), IfaceRefDType)) {
            // Virtual interface handles, or their targets, are excluded
            if (irdtypep->isVirtual()) return;
            // The interface instance companion is not a design variable
            if (nodep->isIfaceParent()) return;

            // Record the interface reference
            AstVarRef* const refp = new AstVarRef{flp, nodep, VAccess::READ};
            addItem(new AstRtmdIfaceRef{flp, rtmdName(nodep), refp}, m_rootIop);
            return;
        }

        // Build the data type descriptor
        AstNodeRtmdDataType* const rtmdTypep = m_typeBuilder.dataType(nodep->dtypep());
        // Exclude if not representable
        if (!rtmdTypep) return;
        // Build the var type descriptor
        AstRtmdVarType* const varTypep = m_typeBuilder.varType(nodep, rtmdTypep);
        // Build the variable descriptor
        AstVarRef* const refp = nodep->isTrace()  //
                                    ? new AstVarRef{flp, nodep, VAccess::READ}
                                    : nullptr;
        AstRtmdVar* const sigp = new AstRtmdVar{flp, rtmdName(nodep), varTypep, refp};
        sigp->traced(nodep->isTrace());
        addItem(sigp, m_rootIop);
    }

    // Skipped
    void visit(AstRandSequence*) override {}
    void visit(AstNodeSchema*) override {}
    void visit(AstNodeCoverOrAssert*) override {
        // Action blocks are cloned or deleted before V3Begin which messes up
        // RtmdVar references to them. Skip them for now. This means statics
        // in assertion action blocks are not traced.
    }

    // Base case
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

    // CONSTRUCTORS
    explicit RtmdBuilder(AstNetlist* nodep)
        : m_typeBuilder{nodep} {
        iterateAndNextNull(nodep->modulesp());
    }
    ~RtmdBuilder() override = default;

public:
    static void apply(AstNetlist* nodep) { RtmdBuilder{nodep}; }
};

void V3Rtmd::buildAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    RtmdBuilder::apply(nodep);
    V3Global::dumpCheckGlobalTree("rtmdbuild", 0, dumpTreeEitherLevel() >= 3);
}
