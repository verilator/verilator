// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
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

#include "V3PchAstMT.h"

#include "V3EmitCBase.h"

#include "V3Task.h"

//######################################################################
// EmitCParentModule implementation

EmitCParentModule::EmitCParentModule() {
    const auto setAll = [](AstNodeModule* modp) -> void {
        for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (VN_IS(nodep, CFunc) || VN_IS(nodep, Var)) nodep->user4p(modp);
        }
    };
    for (AstNode* modp = v3Global.rootp()->modulesp(); modp; modp = modp->nextp()) {
        setAll(VN_AS(modp, NodeModule));
    }
    setAll(v3Global.rootp()->constPoolp()->modp());
}

//######################################################################
// EmitCBase implementation

string EmitCBase::prefixNameProtect(const AstNode* nodep) VL_MT_STABLE {
    const string prefix = v3Global.opt.modPrefix() + "_" + VIdProtect::protect(nodep->name());
    // If all-uppercase prefix conflicts with a previous usage of the
    // prefix with different capitalization, rename to avoid conflict.
    // This is to support OSes where filename compares are non-case significant.
    // STATIC:
    static V3Mutex s_mutex;
    const V3LockGuard lock{s_mutex};  // Otherwise map access is unsafe
    static std::map<std::string, std::string> s_memoized;
    static std::map<std::string, std::string> s_ucToPrefix;
    // Memoize results
    const auto mit = s_memoized.find(prefix);
    if (mit != s_memoized.end()) return mit->second;
    //
    // Check capitalization
    const string prefixUpper = VString::upcase(prefix);
    string result;
    {
        const auto it = s_ucToPrefix.find(prefixUpper);
        if (it == s_ucToPrefix.end()) {
            s_ucToPrefix.emplace(prefixUpper, prefix);
            result = prefix;
        } else if (it->second == prefix) {
            result = prefix;  // Same capitialization as last time
        } else {
            VHashSha256 hash{prefix};
            result = prefix + "__Vphsh" + hash.digestSymbol();
        }
    }
    s_memoized.emplace(prefix, result);
    return result;
}

//######################################################################
// EmitCBaseVisitor implementation

string EmitCBaseVisitorConst::funcNameProtect(const AstCFunc* nodep, const AstNodeModule* modp) {
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

AstCFile* EmitCBaseVisitorConst::newCFile(const string& filename, bool slow, bool source) {
    AstCFile* const cfilep = createCFile(filename, slow, source);
    v3Global.rootp()->addFilesp(cfilep);
    return cfilep;
}

AstCFile* EmitCBaseVisitorConst::createCFile(const string& filename, bool slow,
                                             bool source) VL_MT_SAFE {
    AstCFile* const cfilep = new AstCFile{v3Global.rootp()->fileline(), filename};
    cfilep->slow(slow);
    cfilep->source(source);
    if (source) V3Stats::addStatSum(V3Stats::STAT_CPP_FILES, 1);
    return cfilep;
}

string EmitCBaseVisitorConst::cFuncArgs(const AstCFunc* nodep) {
    // Return argument list for given C function
    string args;
    if (nodep->isLoose() && !nodep->isStatic()) {
        if (nodep->isConst().trueKnown()) args += "const ";
        args += prefixNameProtect(EmitCParentModule::get(nodep));
        args += "* vlSelf";
    }
    if (nodep->needProcess()) {
        if (!args.empty()) args += ", ";
        args += "VlProcessRef vlProcess";
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

void EmitCBaseVisitorConst::emitCFuncHeader(const AstCFunc* funcp, const AstNodeModule* modp,
                                            bool withScope) {
    if (funcp->slow()) putns(funcp, "VL_ATTR_COLD ");
    if (!funcp->isConstructor() && !funcp->isDestructor()) {
        putns(funcp, funcp->rtnTypeVoid());
        puts(" ");
    }
    if (withScope) {
        if (funcp->dpiExportDispatcher()) {
            putns(funcp, topClassName() + "::");
        } else if (funcp->isProperMethod()) {
            putns(funcp, prefixNameProtect(modp) + "::");
        }
    }
    putns(funcp, funcNameProtect(funcp, modp));
    puts("(" + cFuncArgs(funcp) + ")");
    if (funcp->isConst().trueKnown() && funcp->isProperMethod()) puts(" const");
}

void EmitCBaseVisitorConst::emitCFuncDecl(const AstCFunc* funcp, const AstNodeModule* modp,
                                          bool cLinkage) {
    ensureNewLine();
    if (!funcp->ifdef().empty()) putns(funcp, "#ifdef " + funcp->ifdef() + "\n");
    if (cLinkage) putns(funcp, "extern \"C\" ");
    if (funcp->isStatic() && funcp->isProperMethod()) putns(funcp, "static ");
    if (funcp->isVirtual()) {
        UASSERT_OBJ(funcp->isProperMethod(), funcp, "Virtual function is not a proper method");
        putns(funcp, "virtual ");
    }
    emitCFuncHeader(funcp, modp, /* withScope: */ false);
    if (funcp->emptyBody() && !funcp->isLoose() && !cLinkage) {
        putns(funcp, " {}\n");
    } else {
        putns(funcp, ";\n");
    }
    if (!funcp->ifdef().empty()) putns(funcp, "#endif  // " + funcp->ifdef() + "\n");
}

void EmitCBaseVisitorConst::emitVarDecl(const AstVar* nodep, bool asRef) {
    const AstBasicDType* const basicp = nodep->basicp();
    bool refNeedParens = VN_IS(nodep->dtypeSkipRefp(), UnpackArrayDType);

    const auto emitDeclArrayBrackets = [this](const AstVar* nodep) -> void {
        // This isn't very robust and may need cleanup for other data types
        for (const AstUnpackArrayDType* arrayp = VN_CAST(nodep->dtypeSkipRefp(), UnpackArrayDType);
             arrayp; arrayp = VN_CAST(arrayp->subDTypep()->skipRefp(), UnpackArrayDType)) {
            putns(arrayp, "[" + cvtToStr(arrayp->elementsConst()) + "]");
        }
    };

    if (nodep->isIO() && nodep->isSc()) {
        UASSERT_OBJ(basicp, nodep, "Unimplemented: Outputting this data type");
        if (nodep->attrScClocked() && nodep->isReadOnly()) {
            putns(nodep, "sc_core::sc_in_clk ");
        } else {
            if (nodep->isInout()) {
                putns(nodep, "sc_core::sc_inout<");
            } else if (nodep->isWritable()) {
                putns(nodep, "sc_core::sc_out<");
            } else if (nodep->isNonOutput()) {
                putns(nodep, "sc_core::sc_in<");
            } else {
                nodep->v3fatalSrc("Unknown type");
            }
            puts(nodep->scType());
            puts("> ");
        }
        if (asRef) {
            if (refNeedParens) putns(nodep, "(");
            putns(nodep, "&");
        }
        putns(nodep, nodep->nameProtect());
        if (asRef && refNeedParens) puts(")");
        emitDeclArrayBrackets(nodep);
        puts(";\n");
    } else if (nodep->isIO() && basicp && !basicp->isOpaque()) {
        if (nodep->isInout()) {
            putns(nodep, "VL_INOUT");
        } else if (nodep->isWritable()) {
            putns(nodep, "VL_OUT");
        } else if (nodep->isNonOutput()) {
            putns(nodep, "VL_IN");
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
        if (asRef && refNeedParens) puts(")");
        emitDeclArrayBrackets(nodep);
        // If it's a packed struct/array then nodep->width is the whole
        // thing, msb/lsb is just lowest dimension
        puts("," + cvtToStr(basicp->lo() + nodep->width() - 1) + "," + cvtToStr(basicp->lo()));
        if (nodep->isWide()) puts("," + cvtToStr(nodep->widthWords()));
        puts(");\n");
    } else {
        // Strings and other fundamental C types
        if (nodep->isFuncLocal() && nodep->isString()) {
            const string name = nodep->name();
            const string suffix = V3Task::dpiTemporaryVarSuffix();
            // String temporary variable for DPI-C needs to be static because c_str() will be
            // passed to C code and the lifetime of the variable must be long enough. See also
            // Issue 2622.
            const bool beStatic = name.size() >= suffix.size()
                                  && name.substr(name.size() - suffix.size()) == suffix;
            if (beStatic) puts("static thread_local ");
        }
        putns(nodep, nodep->vlArgType(true, false, false, "", asRef));
        puts(";\n");
    }
}

void EmitCBaseVisitorConst::emitVarAccessors(const AstVar* nodep) {
    assert(nodep->name().rfind("__Vm_sig_") == 0 && nodep->isIO());
    const string privateName = nodep->name();
    const string publicName = nodep->name().substr(strlen("__Vm_sig_"));

    puts("decltype("s + privateName + ") "s + publicName + "() {return "s + privateName + ";}\n");
    puts("void "s + publicName + "(decltype(" + privateName + ") v) {"s + privateName + "=v;}\n");
}

void EmitCBaseVisitorConst::emitModCUse(const AstNodeModule* modp, VUseType useType) {
    bool nl = false;
    forModCUse(modp, useType, [&](string entry) {
        puts(entry);
        nl = true;
    });
    if (nl) puts("\n");
}

std::pair<string, FileLine*> EmitCBaseVisitorConst::textSection(const AstNodeModule* modp,
                                                                VNType type) {
    if (!v3Global.hasSCTextSections()) return std::make_pair("", nullptr);
    string text;
    FileLine* fl = nullptr;
    int last_line = -999;
    for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
        if (nodep->type() != type) continue;
        if (const AstNodeText* const textp = VN_CAST(nodep, NodeText)) {
            if (text.empty()) {
                fl = textp->fileline();
                text += "\n";
                if (v3Global.opt.decoration())
                    text += "\n//*** Below code from `systemc in Verilog file\n";
            }
            if (last_line + 1 != nodep->fileline()->lineno() && v3Global.opt.decoration())
                text += "// From `systemc at " + nodep->fileline()->ascii() + "\n";
            last_line = textp->fileline()->lineno();
            text += textp->text();
        }
    }
    if (!text.empty()) {
        if (v3Global.opt.decoration()) text += "//*** Above code from `systemc in Verilog file\n";
        text += "\n";
        // Substitute `systemc_class_name
        string::size_type pos;
        while ((pos = text.find("`systemc_class_name")) != string::npos) {
            text.replace(pos, std::strlen("`systemc_class_name"),
                         EmitCBase::prefixNameProtect(modp));
        }
    }
    return std::make_pair(text, fl);
}

void EmitCBaseVisitorConst::emitTextSection(const AstNodeModule* modp, VNType type) {
    // Short circuit if nothing to do. This can save a lot of time on large designs as this
    // function needs to traverse the entire module linearly.
    auto textAndFileline = textSection(modp, type);
    if (!textAndFileline.first.empty()) ofp()->putsNoTracking(textAndFileline.first);
}
