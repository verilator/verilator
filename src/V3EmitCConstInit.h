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

protected:
    // METHODS
    // Emit the initializer of a definition, for direct initialization: 'type name{...}'
    void emitDirectInit(AstNode* valuep) {
        if (VN_IS(valuep, InitArray) || (VN_IS(valuep, Const) && valuep->isWide())) {
            iterateConst(valuep);  // Already a braced initializer list
        } else {
            puts("{");
            iterateConst(valuep);
            puts("}");
        }
    }

    // VISITORS
    void visit(AstInitArray* nodep) override {
        VL_RESTORER(m_unpackedWord);
        if (VN_IS(nodep->dtypep()->skipRefp(), AssocArrayDType)) {
            // Braced list for the constructors of VlAssocArray: '{default, {items...}}' with a
            // default value, or '{{items...}}' without.
            AstNode* const defaultp = nodep->defaultp();
            const AstInitArray::KeyItemMap& mapr = nodep->map();
            // An empty map without a default must be emitted as '{}'. With 'x{{}}', C++ would
            // take the outer braces as the items list, and the inner '{}' as one value
            // initialized item, giving a map with a single key 0 item instead of an empty map.
            if (!defaultp && mapr.empty()) {
                puts("{}");
                return;
            }
            puts("{\n");
            if (defaultp) {
                puts("/* default: */ ");
                iterateConst(defaultp);
                puts(",\n");
            }
            puts("/* items: */ {");
            bool first = true;
            for (const auto& itr : mapr) {
                if (!first) puts(",");
                first = false;
                puts("\n{");
                ofp()->printf("0x%" PRIx64 "ULL", itr.first);
                puts(", ");
                iterateConst(nodep->getIndexValuep(itr.first));
                puts("}");
            }
            puts("\n}\n}");
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
