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

#include "V3Ast.h"
#include "V3EmitCBase.h"
#include "V3Error.h"

#include <cinttypes>

//######################################################################
// Emitter that can emit constant initializer expressions

class EmitCConstInit VL_NOT_FINAL : public EmitCBaseVisitor {
    // MEMBERS
    bool m_inUnpacked = false;
    uint32_t m_unpackedWord = 0;

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    uint32_t tabModulus(AstNodeDType* dtypep) {
        const uint32_t elemBytes = dtypep->widthTotalBytes();
        return dtypep->isString() ? 1  // String
               : elemBytes <= 2   ? 8  // CData, SData
               : elemBytes <= 4   ? 4  // IData
               : elemBytes <= 8   ? 2  // QData
                                  : 1;
    }

protected:
    // VISITORS
    virtual void visit(AstInitArray* nodep) override {
        VL_RESTORER(m_inUnpacked);
        VL_RESTORER(m_unpackedWord);
        m_inUnpacked = true;
        if (const AstAssocArrayDType* const dtypep
            = VN_CAST(nodep->dtypep()->skipRefp(), AssocArrayDType)) {
            // Note the double {{ initializer. The first { starts the initializer of the
            // VlUnpacked, and the second starts the initializer of m_storage within the
            // VlUnpacked.
            puts("{");
            ofp()->putsNoTracking("{");
            puts("\n");
            int comma = 0;
            const auto& mapr = nodep->map();
            for (const auto& itr : mapr) {
                if (comma++) putbs(",\n");
                puts(cvtToStr(itr.first));
                ofp()->printf("%" PRIx64 "ULL", itr.first);
                ofp()->putsNoTracking(":");
                ofp()->putsNoTracking("{");
                iterate(nodep->getIndexValuep(itr.first));
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
                iterate(nodep->getIndexDefaultedValuep(n));
            }
            puts("\n");
            puts("}");
            ofp()->putsNoTracking("}");
        } else {
            nodep->v3fatalSrc("Array initializer has non-array dtype");
        }
    }

    virtual void visit(AstInitItem* nodep) override {  // LCOV_EXCL_START
        nodep->v3fatal("Handled by AstInitArray");
    }  // LCOV_EXCL_STOP

    virtual void visit(AstConst* nodep) override {
        const V3Number& num = nodep->num();
        UASSERT_OBJ(!num.isFourState(), nodep, "4-state value in constant pool");
        const AstNodeDType* const dtypep = nodep->dtypep();
        if (num.isString()) {
            // Note: putsQuoted does not track indentation, so we use this instead
            puts("\"");
            puts(num.toString());
            puts("\"");
        } else if (dtypep->isWide()) {
            const uint32_t size = dtypep->widthWords();
            // Note the double {{ initializer. The first { starts the initializer of the VlWide,
            // and the second starts the initializer of m_storage within the VlWide.
            puts("{");
            ofp()->putsNoTracking("{");
            if (m_inUnpacked) puts(" // VlWide " + cvtToStr(m_unpackedWord));
            puts("\n");
            for (uint32_t n = 0; n < size; ++n) {
                if (n) puts((n % 4) ? ", " : ",\n");
                ofp()->printf("0x%08" PRIx32, num.edataWord(n));
            }
            puts("\n");
            puts("}");
            ofp()->putsNoTracking("}");
        } else if (dtypep->isDouble()) {
            const double dnum = num.toDouble();
            const char* const fmt
                = !m_inUnpacked && (static_cast<int>(dnum) == dnum && -1000 < dnum && dnum < 1000)
                      ? "%3.1f"  // Force decimal point
                      : "%.17e";  // %e always yields a float literal
            ofp()->printf(fmt, dnum);
        } else if (dtypep->isQuad()) {
            const uint64_t qnum = static_cast<uint64_t>(num.toUQuad());
            const char* const fmt
                = !m_inUnpacked && (qnum < 10) ? ("%" PRIx64 "ULL") : ("0x%016" PRIx64 "ULL");
            ofp()->printf(fmt, qnum);
        } else {
            const uint32_t unum = num.toUInt();
            const char* const fmt = !m_inUnpacked && (unum < 10) ? ("%" PRIu32 "U")
                                    : (dtypep->widthMin() > 16)  ? ("0x%08" PRIx32 "U")
                                    : (dtypep->widthMin() > 8)   ? ("0x%04" PRIx32 "U")
                                                                 : ("0x%02" PRIx32 "U");
            ofp()->printf(fmt, unum);
        }
    }

    // Default
    virtual void visit(AstNode* nodep) override {  // LCOV_EXCL_START
        nodep->v3fatalSrc("Unknown node type reached EmitCConstInit: " << nodep->prettyTypeName());
    }  // LCOV_EXCL_STOP
};
