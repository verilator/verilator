// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
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

#include <algorithm>
#include <cinttypes>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Const pool emitter

class EmitCConstPool final : public EmitCConstInit {
    // TYPES
    using OutCFilePair = std::pair<V3OutCFile*, AstCFile*>;

    // MEMBERS
    uint32_t m_outFileCount = 0;
    int m_outFileSize = 0;
    VDouble0 m_tablesEmitted;
    VDouble0 m_constsEmitted;

    // METHODS

    OutCFilePair newOutCFile() const {
        const string fileName = v3Global.opt.makeDir() + "/" + topClassName() + "__ConstPool_"
                                + cvtToStr(m_outFileCount) + ".cpp";
        AstCFile* const cfilep = newCFile(fileName, /* slow: */ true, /* source: */ true);
        V3OutCFile* const ofp = new V3OutCFile{fileName};
        ofp->putsHeader();
        ofp->puts("// DESCRIPTION: Verilator output: Constant pool\n");
        ofp->puts("//\n");
        ofp->puts("\n");
        ofp->puts("#include \"verilated.h\"\n");
        return {ofp, cfilep};
    }

    void maybeSplitCFile() {
        if (v3Global.opt.outputSplit() && m_outFileSize < v3Global.opt.outputSplit()) return;
        // Splitting file, so using parallel build.
        v3Global.useParallelBuild(true);
        // Close current file
        closeOutputFile();
        // Open next file
        m_outFileSize = 0;
        ++m_outFileCount;
        const OutCFilePair outFileAndNodePair = newOutCFile();
        setOutputFile(outFileAndNodePair.first, outFileAndNodePair.second);
    }

    void emitVars(const AstConstPool* poolp) {
        std::vector<const AstVar*> varps;
        for (AstNode* nodep = poolp->modp()->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (const AstVar* const varp = VN_CAST(nodep, Var)) varps.push_back(varp);
        }

        if (varps.empty()) return;  // Constant pool is empty, so we are done

        stable_sort(varps.begin(), varps.end(), [](const AstVar* ap, const AstVar* bp) {  //
            return ap->name() < bp->name();
        });

        const OutCFilePair outFileAndNodePair = newOutCFile();
        setOutputFile(outFileAndNodePair.first, outFileAndNodePair.second);

        for (const AstVar* varp : varps) {
            maybeSplitCFile();
            const string nameProtect = topClassName() + "__ConstPool__" + varp->nameProtect();
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

        closeOutputFile();
    }

    // VISITORS
    void visit(AstConst* nodep) override {
        m_outFileSize += nodep->num().isString() ? 10 : nodep->isWide() ? nodep->widthWords() : 1;
        EmitCConstInit::visit(nodep);
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
