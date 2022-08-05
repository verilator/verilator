// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3EmitCBase.h"

#include "V3Task.h"

//######################################################################
// EmitCParentModule implementation

EmitCParentModule::EmitCParentModule() {
    const auto setAll = [](AstNodeModule* modp) -> void {
        for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (VN_IS(nodep, CFunc) || VN_IS(nodep, Var)) { nodep->user4p(modp); }
        }
    };
    for (AstNode* modp = v3Global.rootp()->modulesp(); modp; modp = modp->nextp()) {
        setAll(VN_AS(modp, NodeModule));
    }
    setAll(v3Global.rootp()->constPoolp()->modp());
}

//######################################################################
// EmitCBaseVisitor implementation

string EmitCBaseVisitor::funcNameProtect(const AstCFunc* nodep, const AstNodeModule* modp) {
    modp = modp ? modp : EmitCParentModule::get(nodep);
    string name;
    if (nodep->isConstructor()) {
        name += prefixNameProtect(modp);
    } else if (nodep->isDestructor()) {
        name += "~";
        name += prefixNameProtect(modp);
    } else {
        if (nodep->isLoose()) {
            name += prefixNameProtect(modp);
            name += "__";
        }
        name += nodep->nameProtect();
    }
    return name;
}

AstCFile* EmitCBaseVisitor::newCFile(const string& filename, bool slow, bool source) {
    AstCFile* const cfilep = new AstCFile(v3Global.rootp()->fileline(), filename);
    cfilep->slow(slow);
    cfilep->source(source);
    v3Global.rootp()->addFilesp(cfilep);
    return cfilep;
}

string EmitCBaseVisitor::cFuncArgs(const AstCFunc* nodep) {
    // Return argument list for given C function
    string args;
    if (nodep->isLoose() && !nodep->isStatic()) {
        if (nodep->isConst().trueKnown()) args += "const ";
        args += prefixNameProtect(EmitCParentModule::get(nodep));
        args += "* vlSelf";
    }
    if (!nodep->argTypes().empty()) {
        if (!args.empty()) args += ", ";
        args += nodep->argTypes();
    }
    // Might be a user function with argument list.
    for (const AstNode* stmtp = nodep->argsp(); stmtp; stmtp = stmtp->nextp()) {
        if (const AstVar* const portp = VN_CAST(stmtp, Var)) {
            if (portp->isIO() && !portp->isFuncReturn()) {
                if (args != "") args += ", ";
                if (nodep->dpiImportPrototype() || nodep->dpiExportDispatcher()) {
                    args += portp->dpiArgType(true, false);
                } else if (nodep->funcPublic()) {
                    args += portp->cPubArgType(true, false);
                } else {
                    args += portp->vlArgType(true, false, true);
                }
            }
        }
    }
    return args;
}

void EmitCBaseVisitor::emitCFuncHeader(const AstCFunc* funcp, const AstNodeModule* modp,
                                       bool withScope) {
    if (funcp->slow()) puts("VL_ATTR_COLD ");
    if (!funcp->isConstructor() && !funcp->isDestructor()) {
        puts(funcp->rtnTypeVoid());
        puts(" ");
    }
    if (withScope) {
        if (funcp->dpiExportDispatcher()) {
            puts(topClassName() + "::");
        } else if (funcp->isProperMethod()) {
            puts(prefixNameProtect(modp) + "::");
        }
    }
    puts(funcNameProtect(funcp, modp));
    puts("(" + cFuncArgs(funcp) + ")");
    if (funcp->isConst().trueKnown() && funcp->isProperMethod()) puts(" const");
}

void EmitCBaseVisitor::emitCFuncDecl(const AstCFunc* funcp, const AstNodeModule* modp,
                                     bool cLinkage) {
    ensureNewLine();
    if (!funcp->ifdef().empty()) puts("#ifdef " + funcp->ifdef() + "\n");
    if (cLinkage) puts("extern \"C\" ");
    if (funcp->isStatic() && funcp->isProperMethod()) puts("static ");
    if (funcp->isVirtual()) {
        UASSERT_OBJ(funcp->isProperMethod(), funcp, "Virtual function is not a proper method");
        puts("virtual ");
    }
    emitCFuncHeader(funcp, modp, /* withScope: */ false);
    puts(";\n");
    if (!funcp->ifdef().empty()) puts("#endif  // " + funcp->ifdef() + "\n");
}

void EmitCBaseVisitor::emitVarDecl(const AstVar* nodep, bool asRef) {
    const AstBasicDType* const basicp = nodep->basicp();
    bool refNeedParens = VN_IS(nodep->dtypeSkipRefp(), UnpackArrayDType);

    const auto emitDeclArrayBrackets = [this](const AstVar* nodep) -> void {
        // This isn't very robust and may need cleanup for other data types
        for (const AstUnpackArrayDType* arrayp = VN_CAST(nodep->dtypeSkipRefp(), UnpackArrayDType);
             arrayp; arrayp = VN_CAST(arrayp->subDTypep()->skipRefp(), UnpackArrayDType)) {
            puts("[" + cvtToStr(arrayp->elementsConst()) + "]");
        }
    };

    if (nodep->isIO() && nodep->isSc()) {
        UASSERT_OBJ(basicp, nodep, "Unimplemented: Outputting this data type");
        if (nodep->attrScClocked() && nodep->isReadOnly()) {
            puts("sc_in_clk ");
        } else {
            if (nodep->isInoutish()) {
                puts("sc_inout<");
            } else if (nodep->isWritable()) {
                puts("sc_out<");
            } else if (nodep->isNonOutput()) {
                puts("sc_in<");
            } else {
                nodep->v3fatalSrc("Unknown type");
            }
            puts(nodep->scType());
            puts("> ");
        }
        if (asRef) {
            if (refNeedParens) puts("(");
            puts("&");
        }
        puts(nodep->nameProtect());
        if (asRef && refNeedParens) { puts(")"); }
        emitDeclArrayBrackets(nodep);
        puts(";\n");
    } else if (nodep->isIO() && basicp && !basicp->isOpaque()) {
        if (nodep->isInoutish()) {
            puts("VL_INOUT");
        } else if (nodep->isWritable()) {
            puts("VL_OUT");
        } else if (nodep->isNonOutput()) {
            puts("VL_IN");
        } else {
            nodep->v3fatalSrc("Unknown type");
        }

        if (nodep->isQuad()) {
            puts("64");
        } else if (nodep->widthMin() <= 8) {
            puts("8");
        } else if (nodep->widthMin() <= 16) {
            puts("16");
        } else if (nodep->isWide()) {
            puts("W");
        }

        puts("(");
        if (asRef) {
            if (refNeedParens) puts("(");
            puts("&");
        }
        puts(nodep->nameProtect());
        if (asRef && refNeedParens) { puts(")"); }
        emitDeclArrayBrackets(nodep);
        // If it's a packed struct/array then nodep->width is the whole
        // thing, msb/lsb is just lowest dimension
        puts("," + cvtToStr(basicp->lo() + nodep->width() - 1) + "," + cvtToStr(basicp->lo()));
        if (nodep->isWide()) puts("," + cvtToStr(nodep->widthWords()));
        puts(");\n");
    } else {
        // strings and other fundamental c types
        if (nodep->isFuncLocal() && nodep->isString()) {
            const string name = nodep->name();
            const string suffix = V3Task::dpiTemporaryVarSuffix();
            // string temporary variable for DPI-C needs to be static because c_str() will be
            // passed to C code and the lifetime of the variable must be long enough. See also
            // Issue 2622.
            const bool beStatic = name.size() >= suffix.size()
                                  && name.substr(name.size() - suffix.size()) == suffix;
            if (beStatic) puts("static VL_THREAD_LOCAL ");
        }
        puts(nodep->vlArgType(true, false, false, "", asRef));
        puts(";\n");
    }
}

void EmitCBaseVisitor::emitModCUse(const AstNodeModule* modp, VUseType useType) {
    string nl;
    for (AstNode* itemp = modp->stmtsp(); itemp; itemp = itemp->nextp()) {
        if (AstCUse* const usep = VN_CAST(itemp, CUse)) {
            if (usep->useType() == useType) {
                if (usep->useType().isInclude()) {
                    puts("#include \"" + prefixNameProtect(usep) + ".h\"\n");
                }
                if (usep->useType().isFwdClass()) {
                    puts("class " + prefixNameProtect(usep) + ";\n");
                }
                nl = "\n";
            }
        }
    }
    puts(nl);
}

void EmitCBaseVisitor::emitTextSection(const AstNodeModule* modp, VNType type) {
    // Short circuit if nothing to do. This can save a lot of time on large designs as this
    // function needs to traverse the entire module linearly.
    if (!v3Global.hasSCTextSections()) return;

    int last_line = -999;
    for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
        if (const AstNodeText* const textp = VN_CAST(nodep, NodeText)) {
            if (nodep->type() == type) {
                if (last_line != nodep->fileline()->lineno()) {
                    if (last_line < 0) {
                        puts("\n//*** Below code from `systemc in Verilog file\n");
                    }
                    putsDecoration(
                        ifNoProtect("// From `systemc at " + nodep->fileline()->ascii() + "\n"));
                    last_line = nodep->fileline()->lineno();
                }
                ofp()->putsNoTracking(textp->text());
                last_line++;
            }
        }
    }
    if (last_line > 0) puts("//*** Above code from `systemc in Verilog file\n\n");
}
