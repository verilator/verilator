// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
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

protected:
    // VISITORS
    void visit(AstInitArray* nodep) override {
        VL_RESTORER(m_unpackedWord);
        if (VN_IS(nodep->dtypep()->skipRefp(), AssocArrayDType)) {
            // Note the double {{ initializer. The first { starts the initializer of the
            // VlAssocArray, and the second starts the initializer of m_storage within the
            // VlAssocArray.
            puts("{");
            ofp()->putsNoTracking("{");
            puts("\n");
            int comma = 0;
            const auto& mapr = nodep->map();
            for (const auto& itr : mapr) {
                if (comma++) putbs(",\n");
                putns(nodep, cvtToStr(itr.first));
                ofp()->printf("%" PRIx64 "ULL", itr.first);
                ofp()->putsNoTracking(":");
                ofp()->putsNoTracking("{");
                iterateConst(nodep->getIndexValuep(itr.first));
                ofp()->putsNoTracking("}");
            }
            puts("\n");
            puts("}");
            ofp()->putsNoTracking("}");
        } else if (const AstUnpackArrayDType* const dtypep
                   = VN_CAST(nodep->dtypep()->skipRefp(), UnpackArrayDType)) {
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
                AstNode* const itemp = nodep->getIndexDefaultedValuep(n);
                UASSERT_OBJ(itemp, nodep, "Missing array init element");
                iterateConst(itemp);
            }
            puts("\n");
            puts("}");
            ofp()->putsNoTracking("}");
        } else {
            nodep->v3fatalSrc("Array initializer has non-array dtype");
        }
    }

    void visit(AstInitItem* nodep) override {  // LCOV_EXCL_START
        nodep->v3fatalSrc("Handled by AstInitArray");
    }  // LCOV_EXCL_STOP

    void visit(AstConst* nodep) override {
        const V3Number& num = nodep->num();
        UASSERT_OBJ(!num.isFourState(), nodep, "4-state value in constant pool");
        putns(nodep, num.emitC());
    }

    // Default
    void visit(AstNode* nodep) override {  // LCOV_EXCL_START
        nodep->v3fatalSrc("Unknown node type reached EmitCConstInit: " << nodep->prettyTypeName());
    }  // LCOV_EXCL_STOP
};
