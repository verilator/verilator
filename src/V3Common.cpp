// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add common contents to modules
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2025 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Common's Transformations:
//
//  Each class:
//      Create string access functions
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Common.h"

#include "V3EmitCBase.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Common component builders

string V3Common::makeToStringCall(AstNodeDType* nodep, const std::string& lhs) {
    std::string stmt;
    if (VN_IS(nodep->skipRefp(), BasicDType) && nodep->isWide()) {
        stmt += "VL_TO_STRING_W(";
        stmt += cvtToStr(nodep->widthWords());
        stmt += ", ";
    } else if (VN_IS(nodep->skipRefp(), BasicDType) && nodep->isWide()) {
        stmt += "VL_TO_STRING_W(";
        stmt += cvtToStr(nodep->widthWords());
        stmt += ", ";
    } else {
        stmt += "VL_TO_STRING(";
    }
    stmt += lhs;
    stmt += ")";
    return stmt;
}

static void makeVlToString(AstClass* nodep) {
    AstCFunc* const funcp
        = new AstCFunc{nodep->fileline(), "VL_TO_STRING", nullptr, "std::string"};
    funcp->argTypes("const VlClassRef<" + EmitCUtil::prefixNameProtect(nodep) + ">& obj");
    funcp->isMethod(false);
    funcp->isConst(false);
    funcp->isStatic(false);
    funcp->protect(false);
    AstNodeExpr* const exprp
        = new AstCExpr{nodep->fileline(), "obj ? obj->to_string() : \"null\"", 0};
    exprp->dtypeSetString();
    funcp->addStmtsp(new AstCReturn{nodep->fileline(), exprp});
    nodep->addStmtsp(funcp);
}
static void makeVlToString(AstIface* nodep) {
    AstCFunc* const funcp
        = new AstCFunc{nodep->fileline(), "VL_TO_STRING", nullptr, "std::string"};
    funcp->argTypes("const " + EmitCUtil::prefixNameProtect(nodep) + "* obj");
    funcp->isMethod(false);
    funcp->isConst(false);
    funcp->isStatic(false);
    funcp->protect(false);
    AstNodeExpr* const exprp = new AstCExpr{nodep->fileline(), "obj ? obj->name() : \"null\"", 0};
    exprp->dtypeSetString();
    funcp->addStmtsp(new AstCReturn{nodep->fileline(), exprp});
    nodep->addStmtsp(funcp);
}
static void makeVlToString(AstNodeUOrStructDType* nodep) {
    AstNodeModule* const modp = nodep->classOrPackagep();
    UASSERT_OBJ(modp, nodep, "Unlinked struct package");
    AstCFunc* const funcp
        = new AstCFunc{nodep->fileline(), "VL_TO_STRING", nullptr, "std::string"};
    funcp->argTypes("const " + EmitCUtil::prefixNameProtect(nodep) + "& obj");
    funcp->isMethod(false);
    funcp->isConst(false);
    funcp->isStatic(false);
    funcp->protect(false);
    funcp->addStmtsp(new AstCStmt{nodep->fileline(), "std::string out;"});
    for (const AstMemberDType* itemp = nodep->membersp(); itemp;
         itemp = VN_AS(itemp->nextp(), MemberDType)) {
        std::string stmt = "out += \"";
        if (itemp == nodep->membersp()) {
            stmt += "'{";
        } else {
            stmt += ", ";
        }
        stmt += VIdProtect::protect(itemp->prettyName()) + ":\" + ";
        stmt += V3Common::makeToStringCall(itemp->dtypep(), "obj."s + itemp->nameProtect());
        stmt += ";";
        funcp->addStmtsp(new AstCStmt{nodep->fileline(), stmt});
    }
    funcp->addStmtsp(new AstCStmt{nodep->fileline(), "out += \"}\";"});

    AstCExpr* const exprp = new AstCExpr{nodep->fileline(), "out", 0};
    exprp->dtypeSetString();
    funcp->addStmtsp(new AstCReturn{nodep->fileline(), exprp});

    modp->addStmtsp(funcp);
}
static void makeToString(AstClass* nodep) {
    AstCFunc* const funcp = new AstCFunc{nodep->fileline(), "to_string", nullptr, "std::string"};
    funcp->isConst(true);
    funcp->isStatic(false);
    funcp->protect(false);
    AstCExpr* const exprp
        = new AstCExpr{nodep->fileline(), R"("'{"s + to_string_middle() + "}")", 0};
    exprp->dtypeSetString();
    funcp->addStmtsp(new AstCReturn{nodep->fileline(), exprp});
    nodep->addStmtsp(funcp);
}
static void makeToStringMiddle(AstClass* nodep) {
    AstCFunc* const funcp
        = new AstCFunc{nodep->fileline(), "to_string_middle", nullptr, "std::string"};
    funcp->isConst(true);
    funcp->isStatic(false);
    funcp->protect(false);
    funcp->addStmtsp(new AstCStmt{nodep->fileline(), "std::string out;"});
    std::string comma;
    for (AstNode* itemp = nodep->membersp(); itemp; itemp = itemp->nextp()) {
        if (const auto* const varp = VN_CAST(itemp, Var)) {
            if (!varp->isParam() && !varp->isInternal()
                && !(varp->dtypeSkipRefp()->basicp()
                     && (varp->dtypeSkipRefp()->basicp()->isRandomGenerator()
                         || varp->dtypeSkipRefp()->basicp()->isStdRandomGenerator()))) {
                string stmt = "out += \"";
                stmt += comma;
                comma = ", ";
                stmt += itemp->origNameProtect();
                stmt += ":\" + ";
                stmt += V3Common::makeToStringCall(itemp->dtypep(), itemp->nameProtect());
                stmt += ";";
                nodep->user1(true);  // So what we extend dumps this
                funcp->addStmtsp(new AstCStmt{nodep->fileline(), stmt});
            }
        }
    }
    if (nodep->extendsp()) {
        string stmt = "out += ";
        if (!comma.empty()) stmt += "\", \"+ ";
        // comma = ", ";  // Nothing further so not needed
        stmt += EmitCUtil::prefixNameProtect(nodep->extendsp()->dtypep());
        stmt += "::to_string_middle();";
        nodep->user1(true);  // So what we extend dumps this
        funcp->addStmtsp(new AstCStmt{nodep->fileline(), stmt});
    }

    AstCExpr* const exprp = new AstCExpr{nodep->fileline(), "out", 0};
    exprp->dtypeSetString();
    funcp->addStmtsp(new AstCReturn{nodep->fileline(), exprp});

    nodep->addStmtsp(funcp);
}

//######################################################################
// V3Common class functions

void V3Common::commonAll() {
    UINFO(2, __FUNCTION__ << ":");
    // NODE STATE
    // Entire netlist:
    //  AstClass::user1()     -> bool.  True if class needs to_string dumper
    const VNUser1InUse m_inuser1;
    // Create common contents for each module
    for (AstNode* nodep = v3Global.rootp()->modulesp(); nodep; nodep = nodep->nextp()) {
        if (AstClass* const classp = VN_CAST(nodep, Class)) {
            // Create ToString methods
            makeVlToString(classp);
            makeToString(classp);
            makeToStringMiddle(classp);
        } else if (AstIface* const ifacep = VN_CAST(nodep, Iface)) {
            makeVlToString(ifacep);
        }
    }
    for (AstNode* nodep = v3Global.rootp()->typeTablep()->typesp(); nodep;
         nodep = nodep->nextp()) {
        if (AstNodeUOrStructDType* const dtypep = VN_CAST(nodep, NodeUOrStructDType)) {
            if (!dtypep->packed()) makeVlToString(dtypep);
        }
    }
    V3Global::dumpCheckGlobalTree("common", 0, dumpTreeEitherLevel() >= 3);
}
