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
    std::array<VDouble0, VNType::NUM_TYPES()> m_emitted;  // Entries emitted, by value type
    V3UniqueNames m_uniqueNames;  // Generates unique file names
    // Base name of the constant pool files
    const std::string m_fileBaseName = EmitCUtil::topClassName() + "__ConstPool";

    // METHODS
    void emitVars(const AstPackage* poolp) {
        UASSERT(!ofp(), "Output file should not be open");

        std::vector<const AstVar*> varps;
        for (AstNode* const nodep : poolp->stmtspList()) {
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

            puts("\n");
            putns(varp, "extern ");
            // Literal types should be constinit (no code generation needed)
            if (varp->dtypep()->isLiteralType()) putns(varp, "VL_CONSTINIT_CXX20 ");
            putns(varp, "const ");
            emitVarDefn(varp);
            // Account for file splitting
            varp->valuep()->foreach([this](const AstConst* constp) {
                if (constp->num().isString()) {
                    splitSizeInc(AstNode::INSTR_COUNT_STR);
                } else if (constp->isWide()) {
                    splitSizeInc(constp->widthWords());
                } else {
                    splitSizeInc(1);
                }
            });
            putns(varp, ";\n");
            // Keep track of stats
            ++m_emitted[varp->valuep()->type()];
        }

        if (ofp()) closeOutputFile();
    }

    // VISITORS
    void visit(AstNode* nodep) override {  // LCOV_EXCL_START
        nodep->v3fatalSrc("Unknown node type reached EmitCConstPool: " << nodep->prettyTypeName());
    }  // LCOV_EXCL_STOP

public:
    explicit EmitCConstPool(const AstPackage* poolp) {
        emitVars(poolp);
        const auto addStat = [this](VNType type) {
            V3Stats::addStat("ConstPool, "s + type.ascii() + " emitted", m_emitted[type]);
        };
        addStat(VNType::Const);
        for (int t = VNType::firstNodeCons; t <= VNType::lastNodeCons; ++t) {
            addStat(static_cast<VNType::en>(t));
        }
    }
};

//######################################################################
// EmitC static functions

void V3EmitC::emitcConstPool() {
    UINFO(2, __FUNCTION__ << ":");
    EmitCConstPool(v3Global.rootp()->constPoolPkgp());
}
