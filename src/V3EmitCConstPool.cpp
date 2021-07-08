// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2021 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3EmitC.h"
#include "V3EmitCBase.h"
#include "V3File.h"
#include "V3Global.h"
#include "V3String.h"
#include "V3Stats.h"

#include <algorithm>
#include <cinttypes>

//######################################################################
// Const pool emitter

class EmitCConstPool final : EmitCBaseVisitor {
    // MEMBERS
    bool m_inUnpacked = false;
    uint32_t m_unpackedWord = 0;
    uint32_t m_outFileCount = 0;
    int m_outFileSize = 0;
    VDouble0 m_tablesEmitted;
    VDouble0 m_constsEmitted;

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    V3OutCFile* newOutCFile() const {
        const string fileName = v3Global.opt.makeDir() + "/" + topClassName() + "__ConstPool_"
                                + cvtToStr(m_outFileCount) + ".cpp";
        newCFile(fileName, /* slow: */ true, /* source: */ true);
        V3OutCFile* const ofp = new V3OutCFile(fileName);
        ofp->putsHeader();
        ofp->puts("// DESCRIPTION: Verilator output: Constant pool\n");
        ofp->puts("//\n");
        ofp->puts("\n");
        ofp->puts("#include \"verilated_heavy.h\"\n");
        return ofp;
    }

    void maybeSplitCFile() {
        if (v3Global.opt.outputSplit() && m_outFileSize < v3Global.opt.outputSplit()) return;
        // Splitting file, so using parallel build.
        v3Global.useParallelBuild(true);
        // Close current file
        VL_DO_DANGLING(delete m_ofp, m_ofp);
        // Open next file
        m_outFileSize = 0;
        ++m_outFileCount;
        m_ofp = newOutCFile();
    }

    void emitVars(const AstConstPool* poolp) {
        std::vector<const AstVar*> varps;
        for (AstNode* nodep = poolp->modp()->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstVar* const varp = VN_CAST_CONST(nodep, Var)) { varps.push_back(varp); }
        }

        if (varps.empty()) return;  // Constant pool is empty, so we are done

        stable_sort(varps.begin(), varps.end(), [](const AstVar* ap, const AstVar* bp) {  //
            return ap->name() < bp->name();
        });

        m_ofp = newOutCFile();

        for (const AstVar* varp : varps) {
            maybeSplitCFile();
            const string nameProtect = topClassName() + "__ConstPool__" + varp->nameProtect();
            puts("\n");
            puts("extern const ");
            puts(varp->dtypep()->cType(nameProtect, false, false));
            puts(" = ");
            iterate(varp->valuep());
            puts(";\n");
            // Keep track of stats
            if (VN_IS(varp->dtypep(), UnpackArrayDType)) {
                ++m_tablesEmitted;
            } else {
                ++m_constsEmitted;
            }
        }

        VL_DO_DANGLING(delete m_ofp, m_ofp);
    }

    // VISITORS
    virtual void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

    virtual void visit(AstInitArray* nodep) override {
        const AstUnpackArrayDType* const dtypep
            = VN_CAST(nodep->dtypep()->skipRefp(), UnpackArrayDType);
        UASSERT_OBJ(dtypep, nodep, "Array initializer has non-array dtype");
        const uint32_t size = dtypep->elementsConst();
        const uint32_t elemBytes = dtypep->subDTypep()->widthTotalBytes();
        const uint32_t tabMod = dtypep->subDTypep()->isString() ? 1  // String
                                : elemBytes <= 2                ? 8  // CData, SData
                                : elemBytes <= 4                ? 4  // IData
                                : elemBytes <= 8                ? 2  // QData
                                                                : 1;
        VL_RESTORER(m_inUnpacked);
        VL_RESTORER(m_unpackedWord);
        m_inUnpacked = true;
        // Note the double {{ initializer. The first { starts the initializer of the VlUnpacked,
        // and the second starts the initializer of m_storage within the VlUnpacked.
        puts("{");
        ofp()->putsNoTracking("{");
        puts("\n");
        for (uint32_t n = 0; n < size; ++n) {
            m_unpackedWord = n;
            if (n) puts(n % tabMod ? ", " : ",\n");
            iterate(nodep->getIndexDefaultedValuep(n));
        }
        puts("\n");
        puts("}");
        ofp()->putsNoTracking("}");
    }

    virtual void visit(AstInitItem* nodep) override {  // LCOV_EXCL_START
        nodep->v3fatal("Handled by AstInitArray");
    }  // LCOV_EXCL_END

    virtual void visit(AstConst* nodep) override {
        const V3Number& num = nodep->num();
        UASSERT_OBJ(!num.isFourState(), nodep, "4-state value in constant pool");
        AstNodeDType* const dtypep = nodep->dtypep();
        m_outFileSize += 1;
        if (num.isString()) {
            // Note: putsQuoted does not track indentation, so we use this instead
            puts("\"");
            puts(num.toString());
            puts("\"");
            m_outFileSize += 9;
        } else if (dtypep->isWide()) {
            const uint32_t size = dtypep->widthWords();
            m_outFileSize += size - 1;
            // Note the double {{ initializer. The first { starts the initializer of the VlWide,
            // and the second starts the initializer of m_storage within the VlWide.
            puts("{");
            ofp()->putsNoTracking("{");
            if (m_inUnpacked) puts(" // VlWide " + cvtToStr(m_unpackedWord));
            puts("\n");
            for (uint32_t n = 0; n < size; ++n) {
                if (n) puts(n % 4 ? ", " : ",\n");
                ofp()->printf("0x%08" PRIx32, num.edataWord(n));
            }
            puts("\n");
            puts("}");
            ofp()->putsNoTracking("}");
        } else if (dtypep->isQuad()) {
            ofp()->printf("0x%016" PRIx64, static_cast<uint64_t>(num.toUQuad()));
        } else if (dtypep->widthMin() > 16) {
            ofp()->printf("0x%08" PRIx32, num.toUInt());
        } else if (dtypep->widthMin() > 8) {
            ofp()->printf("0x%04" PRIx32, num.toUInt());
        } else {
            ofp()->printf("0x%02" PRIx32, num.toUInt());
        }
    }

public:
    explicit EmitCConstPool(AstConstPool* poolp) {
        emitVars(poolp);
        V3Stats::addStatSum("ConstPool, Tables emitted", m_tablesEmitted);
        V3Stats::addStatSum("ConstPool, Constants emitted", m_constsEmitted);
    }
};

//######################################################################
// EmitC static functions

void V3EmitC::emitcConstPool() {
    UINFO(2, __FUNCTION__ << ": " << endl);
    EmitCConstPool(v3Global.rootp()->constPoolp());
}
