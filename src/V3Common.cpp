// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add common contents to modules
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
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

#define VL_MT_DISABLED_CODE_UNIT 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Common.h"

#include "V3Ast.h"
#include "V3EmitCBase.h"
#include "V3Global.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Common component builders

static void makeVlToString(AstClass* nodep) {
    AstCFunc* const funcp
        = new AstCFunc{nodep->fileline(), "VL_TO_STRING", nullptr, "std::string"};
    funcp->argTypes("const VlClassRef<" + EmitCBase::prefixNameProtect(nodep) + ">& obj");
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
    funcp->argTypes("const " + EmitCBase::prefixNameProtect(nodep) + "* obj");
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
    funcp->argTypes("const " + EmitCBase::prefixNameProtect(nodep) + "& obj");
    funcp->isMethod(false);
    funcp->isConst(false);
    funcp->isStatic(false);
    funcp->protect(false);
    funcp->addStmtsp(new AstCStmt{nodep->fileline(), "std::string out;\n"});
    for (const AstMemberDType* itemp = nodep->membersp(); itemp;
         itemp = VN_AS(itemp->nextp(), MemberDType)) {
        std::string stmt = "out += \"";
        if (itemp == nodep->membersp()) {
            stmt += "'{";
        } else {
            stmt += ", ";
        }
        stmt += VIdProtect::protect(itemp->prettyName()) + ":\" + ";
        if (VN_IS(itemp->dtypep()->skipRefp(), BasicDType) && itemp->isWide()) {
            stmt += "VL_TO_STRING_W(";
            stmt += cvtToStr(itemp->widthWords());
            stmt += ", ";
        } else {
            stmt += "VL_TO_STRING(";
        }
        stmt += "obj." + itemp->nameProtect() + ");\n";
        funcp->addStmtsp(new AstCStmt{nodep->fileline(), stmt});
    }
    funcp->addStmtsp(new AstCStmt{nodep->fileline(), "out += \"}\";\n"});
    funcp->addStmtsp(new AstCStmt{nodep->fileline(), "return out;\n"});
    modp->addStmtsp(funcp);
}
static void makeToString(AstClass* nodep) {
    AstCFunc* const funcp = new AstCFunc{nodep->fileline(), "to_string", nullptr, "std::string"};
    funcp->isConst(true);
    funcp->isStatic(false);
    funcp->protect(false);
    AstCExpr* const exprp
        = new AstCExpr{nodep->fileline(), R"(std::string{"'{"} + to_string_middle() + "}")", 0};
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
    funcp->addStmtsp(new AstCStmt{nodep->fileline(), "std::string out;\n"});
    std::string comma;
    for (AstNode* itemp = nodep->membersp(); itemp; itemp = itemp->nextp()) {
        if (const auto* const varp = VN_CAST(itemp, Var)) {
            if (!varp->isParam() && !varp->isInternal()) {
                string stmt = "out += \"";
                stmt += comma;
                comma = ", ";
                stmt += itemp->origNameProtect();
                stmt += ":\" + ";
                if (VN_IS(itemp->dtypep()->skipRefp(), BasicDType) && itemp->isWide()) {
                    stmt += "VL_TO_STRING_W(";
                    stmt += cvtToStr(itemp->widthWords());
                    stmt += ", ";
                } else {
                    stmt += "VL_TO_STRING(";
                }
                stmt += itemp->nameProtect();
                stmt += ");\n";
                nodep->user1(true);  // So what we extend dumps this
                funcp->addStmtsp(new AstCStmt{nodep->fileline(), stmt});
            }
        }
    }
    if (nodep->extendsp()) {
        string stmt = "out += ";
        if (!comma.empty()) stmt += "\", \"+ ";
        // comma = ", ";  // Nothing further so not needed
        stmt += EmitCBase::prefixNameProtect(nodep->extendsp()->dtypep());
        stmt += "::to_string_middle();\n";
        nodep->user1(true);  // So what we extend dumps this
        funcp->addStmtsp(new AstCStmt{nodep->fileline(), stmt});
    }
    funcp->addStmtsp(new AstCStmt{nodep->fileline(), "return out;\n"});
    nodep->addStmtsp(funcp);
}

//######################################################################
// V3Common class functions

void V3Common::commonAll() {
    UINFO(2, __FUNCTION__ << ": " << endl);
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
    V3Global::dumpCheckGlobalTree("common", 0, dumpTreeLevel() >= 3);
}
