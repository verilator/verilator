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

#include "V3PchAstMT.h"

#include "V3EmitC.h"
#include "V3EmitCConstInit.h"
#include "V3File.h"
#include "V3Stats.h"
#include "V3UniqueNames.h"

#include <algorithm>
#include <cinttypes>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Const pool emitter

class EmitCConstPool final : public EmitCConstInit {
    // TYPES
    using OutCFilePair = std::pair<V3OutCFile*, AstCFile*>;

    // MEMBERS
    VDouble0 m_tablesEmitted;
    VDouble0 m_constsEmitted;
    V3UniqueNames m_uniqueNames;  // Generates unique file names
    const std::string m_fileBaseName = EmitCUtil::topClassName() + "__ConstPool";

    // METHODS
    void emitVars(const AstConstPool* poolp) {
        UASSERT(!ofp(), "Output file should not be open");

        std::vector<const AstVar*> varps;
        for (AstNode* nodep = poolp->modp()->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstVar* const varp = VN_CAST(nodep, Var)) varps.push_back(varp);
        }

        if (varps.empty()) return;  // Constant pool is empty, so we are done

        stable_sort(varps.begin(), varps.end(), [](const AstVar* ap, const AstVar* bp) {  //
            return ap->name() < bp->name();
        });

        for (const AstVar* varp : varps) {
            if (splitNeeded()) {
                // Splitting file, so using parallel build.
                v3Global.useParallelBuild(true);
                // Close old file
                closeOutputFile();
            }

            if (!ofp()) {
                openNewOutputSourceFile(m_uniqueNames.get(m_fileBaseName), true, false,
                                        "Constant pool");
                puts("\n");
                puts("#include \"verilated.h\"\n");
            }

            const std::string nameProtect
                = EmitCUtil::topClassName() + "__ConstPool__" + varp->nameProtect();
            puts("\n");
            putns(varp, "extern const ");
            putns(varp, varp->dtypep()->cType(nameProtect, false, false));
            putns(varp, " = ");
            UASSERT_OBJ(varp, varp->valuep(), "Var without value");
            iterateConst(varp->valuep());
            putns(varp, ";\n");
            // Keep track of stats
            if (VN_IS(varp->dtypep(), UnpackArrayDType)) {
                ++m_tablesEmitted;
            } else {
                ++m_constsEmitted;
            }
        }

        if (ofp()) closeOutputFile();
    }

    // VISITORS
    void visit(AstConst* nodep) override {
        if (nodep->num().isString()) {
            splitSizeInc(AstNode::INSTR_COUNT_STR);
        } else if (nodep->isWide()) {
            splitSizeInc(nodep->widthWords());
        } else {
            splitSizeInc(1);
        }
        EmitCConstInit::visit(nodep);
    }

public:
    explicit EmitCConstPool(const AstConstPool* poolp) {
        emitVars(poolp);
        V3Stats::addStatSum("ConstPool, Tables emitted", m_tablesEmitted);
        V3Stats::addStatSum("ConstPool, Constants emitted", m_constsEmitted);
    }
};

//######################################################################
// EmitC static functions

void V3EmitC::emitcConstPool() {
    UINFO(2, __FUNCTION__ << ":");
    EmitCConstPool(v3Global.rootp()->constPoolp());
}
