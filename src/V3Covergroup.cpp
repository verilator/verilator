// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Transform covergroup AST into runtime calls
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
// V3Covergroup's Transformations:
//
// For each covergroup class (AstClass with isCovergroup()):
//   1. Inject a VlCovergroup member variable (__Vcovergrouprt)
//   2. Transform AstCoverpoint/AstCoverBin nodes in the constructor
//      into runtime initialization calls (AstCStmt with AstVarRef)
//   3. Populate sample() method body with AstCMethodHard calls
//   4. Populate get_inst_coverage() with AstCMethodHard + AstAssign
//   5. Populate set_inst_name() with AstCMethodHard
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Covergroup.h"

#include "V3MemberMap.h"

#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################

class CovergroupVisitor final : public VNVisitor {
    // NODE STATE
    //  AstClass::user1()  -> bool: already processed
    const VNUser1InUse m_user1InUse;

    // STATE
    VMemberMap m_memberMap;  // Member lookup by name
    std::vector<AstCoverpoint*> m_coverpoints;  // Collected from constructor

    // METHODS

    static string cppStr(const string& s) { return "\"" + s + "\""; }

    static string binKindStr(VCoverBinKind kind) {
        switch (kind.m_e) {
        case VCoverBinKind::ILLEGAL_BINS: return "VlCovBinKind::ILLEGAL_BINS";
        case VCoverBinKind::IGNORE_BINS: return "VlCovBinKind::IGNORE_BINS";
        default: return "VlCovBinKind::BINS";
        }
    }

    // Generate bin initialization statements using AstCStmt
    void genBinInit(AstFunc* funcp, FileLine* fl, AstCoverBin* binp, const string& cpVar) {
        if (binp->isArray()) {
            binp->v3warn(E_UNSUPPORTED, "Unsupported: array bins (bins x[] = ...)");
            return;
        }
        if (binp->isDefault()) {
            binp->v3warn(E_UNSUPPORTED, "Unsupported: default bins");
            return;
        }

        // Open block scope for __b
        funcp->addStmtsp(new AstCStmt{fl, "{ VlCovBinDef& __b = " + cpVar + "->addBin("
                                              + cppStr(binp->name()) + ", "
                                              + binKindStr(binp->binKind()) + ");\n"});

        if (binp->isDefault()) {
            funcp->addStmtsp(new AstCStmt{fl, "__b.setDefault(true);\n"});
        } else {
            for (AstNodeExpr* rangep = binp->rangesp(); rangep;
                 rangep = VN_AS(rangep->nextp(), NodeExpr)) {
                if (const AstInsideRange* const irp = VN_CAST(rangep, InsideRange)) {
                    AstCStmt* const addp = new AstCStmt{fl};
                    addp->add("__b.addRange(static_cast<uint64_t>(");
                    addp->add(irp->lhsp()->cloneTree(false));
                    addp->add("), static_cast<uint64_t>(");
                    addp->add(irp->rhsp()->cloneTree(false));
                    addp->add("));\n");
                    funcp->addStmtsp(addp);
                } else {
                    AstCStmt* const addp = new AstCStmt{fl};
                    addp->add("__b.addRange(static_cast<uint64_t>(");
                    addp->add(rangep->cloneTree(false));
                    addp->add("));\n");
                    funcp->addStmtsp(addp);
                }
            }
        }

        if (binp->isArray()) {
            funcp->addStmtsp(
                new AstCStmt{fl, "__b.setArray(true, " + cvtToStr(binp->arraySize()) + ");\n"});
        }

        funcp->addStmtsp(new AstCStmt{fl, "}\n"});
    }

    void processCovergroup(AstClass* classp) {
        if (classp->user1()) return;
        classp->user1(true);

        v3Global.useCovergroup(true);
        FileLine* const fl = classp->fileline();

        // Add VlCovergroup member variable
        AstVar* const cgVarp
            = new AstVar{fl, VVarType::MEMBER, "__Vcovergrouprt",
                         classp->findBasicDType(VBasicDTypeKwd::COVERGROUP_RUNTIME)};
        classp->addMembersp(cgVarp);
        classp->needCovergroup(true);

        // Find the constructor
        AstFunc* const ctorp = VN_CAST(m_memberMap.findMember(classp, "new"), Func);
        if (!ctorp) {
            classp->v3fatalSrc("Covergroup missing constructor");
            return;
        }

        // Collect AstCoverpoint nodes from constructor
        m_coverpoints.clear();
        for (AstNode* stmtp = ctorp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstCoverpoint* const cpp = VN_CAST(stmtp, Coverpoint)) {
                m_coverpoints.push_back(cpp);
            }
        }

        // Remove AstCgOptionAssign from constructor (before early return)
        for (AstNode* stmtp = ctorp->stmtsp(); stmtp;) {
            AstNode* const nextp = stmtp->nextp();
            if (VN_IS(stmtp, CgOptionAssign)) {
                VL_DO_DANGLING(stmtp->unlinkFrBack()->deleteTree(), stmtp);
            }
            stmtp = nextp;
        }

        if (m_coverpoints.empty()) return;

        // 4. Generate constructor initialization code
        // __Vcovergrouprt = VlCovergroup{"name"};
        {
            AstCStmt* const stmtp = new AstCStmt{fl};
            stmtp->add(new AstVarRef{fl, cgVarp, VAccess::WRITE});
            stmtp->add(" = VlCovergroup{" + cppStr(classp->name()) + "};\n");
            ctorp->addStmtsp(stmtp);
        }

        uint32_t cpIdx = 0;
        for (AstCoverpoint* const cpp : m_coverpoints) {
            const string cpVar = "__cp" + cvtToStr(cpIdx);
            const string cpName
                = cpp->name().empty() ? ("__anon_cp" + cvtToStr(cpIdx)) : cpp->name();

            // VlCoverpoint* __cpN = __Vcovergrouprt.addCoverpoint("name");
            {
                AstCStmt* const stmtp = new AstCStmt{fl, "{ VlCoverpoint* " + cpVar + " = "};
                stmtp->add(new AstVarRef{fl, cgVarp, VAccess::READ});
                stmtp->add(".addCoverpoint(" + cppStr(cpName) + ");\n");
                ctorp->addStmtsp(stmtp);
            }

            for (AstNode* binNodep = cpp->binsp(); binNodep; binNodep = binNodep->nextp()) {
                if (AstCoverBin* const binp = VN_CAST(binNodep, CoverBin)) {
                    genBinInit(ctorp, fl, binp, cpVar);
                }
            }

            // Close block
            ctorp->addStmtsp(new AstCStmt{fl, "}\n"});
            ++cpIdx;
        }

        // __Vcovergrouprt.finalize();
        {
            AstCMethodHard* const callp = new AstCMethodHard{
                fl, new AstVarRef{fl, cgVarp, VAccess::READ}, VCMethod::COVERGROUP_FINALIZE};
            callp->dtypeSetVoid();
            ctorp->addStmtsp(callp->makeStmt());
        }

        // 5. Populate sample() method body
        AstFunc* const samplep = VN_CAST(m_memberMap.findMember(classp, "sample"), Func);
        if (samplep) {
            cpIdx = 0;
            for (AstCoverpoint* const cpp : m_coverpoints) {
                // __Vcovergrouprt.sampleCoverpoint(cpIdx, (QData)(expr))
                AstCMethodHard* const callp = new AstCMethodHard{
                    fl, new AstVarRef{fl, cgVarp, VAccess::READ}, VCMethod::COVERGROUP_SAMPLE_CP};
                callp->addPinsp(new AstConst{fl, cpIdx});
                callp->addPinsp(new AstCCast{fl, cpp->exprp()->cloneTree(false), 64});
                callp->dtypeSetVoid();
                samplep->addStmtsp(callp->makeStmt());
                ++cpIdx;
            }
        }

        // 6. Populate get_inst_coverage()
        if (AstFunc* const funcp
            = VN_CAST(m_memberMap.findMember(classp, "get_inst_coverage"), Func)) {
            if (AstVar* const fvarp = VN_CAST(funcp->fvarp(), Var)) {
                // fvarp = __Vcovergrouprt.getInstCoverage()
                AstCMethodHard* const callp
                    = new AstCMethodHard{fl, new AstVarRef{fl, cgVarp, VAccess::READ},
                                         VCMethod::COVERGROUP_GET_INST_COV};
                callp->dtypeSetDouble();
                funcp->addStmtsp(
                    new AstAssign{fl, new AstVarRef{fl, fvarp, VAccess::WRITE}, callp});
            }
        }

        // 7. Populate set_inst_name()
        if (AstFunc* const funcp
            = VN_CAST(m_memberMap.findMember(classp, "set_inst_name"), Func)) {
            // Find the "name" parameter
            AstVar* nameVarp = nullptr;
            for (AstNode* stmtp = funcp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                    if (varp->name() == "name") {
                        nameVarp = varp;
                        break;
                    }
                }
            }
            if (nameVarp) {
                // __Vcovergrouprt.setInstName(name)
                AstCMethodHard* const callp
                    = new AstCMethodHard{fl, new AstVarRef{fl, cgVarp, VAccess::READ},
                                         VCMethod::COVERGROUP_SET_INST_NAME,
                                         new AstVarRef{fl, nameVarp, VAccess::READ}};
                callp->dtypeSetVoid();
                funcp->addStmtsp(callp->makeStmt());
            }
        }

        // 8. Remove original AstCoverpoint nodes from constructor
        for (AstCoverpoint* const cpp : m_coverpoints) {
            VL_DO_DANGLING(cpp->unlinkFrBack()->deleteTree(), cpp);
        }
        m_coverpoints.clear();
    }

    // VISITORS
    void visit(AstClass* nodep) override {
        if (nodep->isCovergroup()) processCovergroup(nodep);
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit CovergroupVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~CovergroupVisitor() override = default;
};

//######################################################################
// V3Covergroup class functions

void V3Covergroup::covergroupAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":" << endl);
    { CovergroupVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("covergroup", 0, dumpTreeEitherLevel() >= 3);
}
