// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
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

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3EmitCBase.h"
#include "V3Error.h"

#include <cinttypes>

//######################################################################
// Emitter that can emit constant initializer expressions

class EmitCConstInit VL_NOT_FINAL : public EmitCBaseVisitorConst {
    // MEMBERS
    uint32_t m_unpackedWord = 0;

    // METHODS
    uint32_t tabModulus(const AstNodeDType* dtypep) {
        const uint32_t elemBytes = dtypep->widthTotalBytes();
        return dtypep->isString() ? 1  // String
               : elemBytes <= 2   ? 8  // CData, SData
               : elemBytes <= 4   ? 4  // IData
               : elemBytes <= 8   ? 2  // QData
                                  : 1;
    }
    // Constants in initializers use our form, not the expression form of EmitCFunc
    void iterateInit(AstNode* nodep) {
        if (AstConst* const constp = VN_CAST(nodep, Const)) {
            EmitCConstInit::visit(constp);
        } else {
            iterateConst(nodep);
        }
    }

protected:
    // METHODS
    // Emit the initializer of a definition, for direct initialization: 'type name{...}'
    void emitDirectInit(AstNode* valuep) {
        if (VN_IS(valuep, ConsArray) || VN_IS(valuep, ConsAssoc) || VN_IS(valuep, ConsWildcard)
            || (VN_IS(valuep, Const) && valuep->isWide())) {
            iterateInit(valuep);  // Already a braced initializer list
        } else {
            puts("{");
            iterateInit(valuep);
            puts("}");
        }
    }

    template <typename T_Item>
    void emitConsKeyedItems(T_Item* itemsp) {
        // Braced list of '{key, value}' pairs
        puts("{");
        for (T_Item* itemp = itemsp; itemp; itemp = AstNode::as<T_Item>(itemp->nextp())) {
            if (itemp != itemsp) puts(",");
            puts("\n{");
            // std::pair's constructor can't deduce a type from a braced list, so give wide keys
            // their type, otherwise converting a non-constant value would be narrowing
            AstNodeExpr* const keyp = itemp->keyp();
            if (VN_IS(keyp, Const) && keyp->isWide()) {
                puts(keyp->dtypep()->cType("", false, false));
            }
            iterateInit(keyp);
            puts(", ");
            iterateInit(itemp->valuep());
            puts("}");
        }
        puts("\n}");
    }

    template <typename T_Item>
    void emitConsUnkeyedItems(T_Item* itemsp) {
        puts("{");
        for (T_Item* itemp = itemsp; itemp; itemp = AstNode::as<T_Item>(itemp->nextp())) {
            if (itemp != itemsp) puts(",");
            puts("\n");
            AstNodeExpr* const valuep = itemp->valuep();
            // The variadic constructor can't deduce a type from a braced list, so give unpacked
            // array values their type
            if (VN_IS(valuep, ConsArray)) puts(valuep->dtypep()->cType("", false, false));
            iterateInit(valuep);
        }
        puts("\n}");
    }

    template <typename T_Cons>
    void emitConsAssoc(T_Cons* nodep) {
        // '{default, {items}}', '{{items}}', or '{}' if empty
        if (!nodep->defaultp() && !nodep->itemsp()) {
            puts("{}");
            return;
        }
        puts("{\n");
        if (AstNodeExpr* const defaultp = nodep->defaultp()) {
            iterateInit(defaultp);
            puts(",\n");
        }
        emitConsKeyedItems(nodep->itemsp());
        puts("\n}");
    }

    // VISITORS
    void visit(AstConsArray* nodep) override {
        VL_RESTORER(m_unpackedWord);
        const AstUnpackArrayDType* const dtypep
            = VN_AS(nodep->dtypep()->skipRefp(), UnpackArrayDType);
        const uint64_t size = dtypep->elementsConst();
        const uint32_t tabMod = tabModulus(dtypep->subDTypep());
        // Note the double {{ initializer. The first { starts the initializer of the
        // VlUnpacked, and the second starts the initializer of m_storage within the
        // VlUnpacked.
        puts("{");
        ofp()->putsNoTracking("{");
        puts("\n");
        for (uint64_t n = 0; n < size; ++n) {
            m_unpackedWord = n;
            if (n) puts((n % tabMod) ? ", " : ",\n");
            AstNode* const itemp = nodep->valuep(n);
            UASSERT_OBJ(itemp, nodep, "Missing array init element");
            iterateInit(itemp);
        }
        puts("\n");
        puts("}");
        ofp()->putsNoTracking("}");
    }

    void visit(AstConsAssoc* nodep) override { emitConsAssoc(nodep); }
    void visit(AstConsWildcard* nodep) override { emitConsAssoc(nodep); }
    void visit(AstConsDynArray* nodep) override {
        if (!nodep->sizep()) {
            emitConsUnkeyedItems(nodep->itemsp());
            return;
        }
        puts("{\n");
        iterateInit(nodep->sizep());
        puts(",\n");
        if (nodep->defaultp()) {
            iterateInit(nodep->defaultp());
            puts(",\n");
        }
        emitConsKeyedItems(nodep->itemsp());
        puts("\n}");
    }
    void visit(AstConsQueue* nodep) override { emitConsUnkeyedItems(nodep->itemsp()); }
    void visit(AstConsStruct* nodep) override { emitConsUnkeyedItems(nodep->itemsp()); }

    void visit(AstNodeConsItem* nodep) override {  // LCOV_EXCL_START
        nodep->v3fatalSrc("Handled by its AstNodeCons");
    }  // LCOV_EXCL_STOP

    void visit(AstConst* nodep) override {
        const V3Number& num = nodep->num();
        UASSERT_OBJ(!num.isFourState(), nodep, "4-state value in constant pool");
        if (!nodep->isWide()) {
            putns(nodep, num.emitC());
            return;
        }
        // Wide values are emitted as a braced initializer list of the words, without the
        // VlWide type. Note the double {{ initializer. The first { starts the initializer of
        // the VlWide, and the second starts the initializer of m_storage within the VlWide.
        const int words = nodep->widthWords();
        putns(nodep, "{");
        ofp()->putsNoTracking("{");
        if (words > 4) puts("\n");
        for (int n = 0; n < words; ++n) {
            if (n) puts((n % 4) ? ", " : ",\n");
            ofp()->printf("0x%08" PRIx32, num.edataWord(n));
        }
        if (words > 4) puts("\n");
        puts("}");
        ofp()->putsNoTracking("}");
    }
    void visit(AstUnbounded* nodep) override {
        // e.g. when emitting a public parameter's "$" value
        // But Unbounded is only special during elaboration, so just use zero
        putns(nodep, "0");
    }

    // Default
    void visit(AstNode* nodep) override {  // LCOV_EXCL_START
        nodep->v3fatalSrc("Unknown node type reached EmitCConstInit: " << nodep->prettyTypeName());
    }  // LCOV_EXCL_STOP
};
