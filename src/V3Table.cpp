// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Make lookup tables
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
// TABLE TRANSFORMATIONS:
//      Look at all large always and assignments.
//      Count # of input bits and # of output bits, and # of statements
//      If high # of statements relative to inpbits*outbits,
//      replace with lookup table
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Table.h"

#include "V3Ast.h"
#include "V3Global.h"
#include "V3Simulate.h"
#include "V3Stats.h"

#include <cmath>
#include <vector>

//######################################################################
// Table class functions

// CONFIG
// 1MB is max table size (better be lots of instructs to be worth it!)
static constexpr int TABLE_MAX_BYTES = 1 * 1024 * 1024;
// 64MB is close to max memory of some systems (256MB or so), so don't get out of control
static constexpr int TABLE_TOTAL_BYTES = 64 * 1024 * 1024;
// Worth no more than 8 bytes of data to replace an instruction
static constexpr int TABLE_SPACE_TIME_MULT = 8;
// If < 32 instructions, not worth the effort
static constexpr int TABLE_MIN_NODE_COUNT = 32;
// Assume an instruction is 4 bytes
static constexpr int TABLE_BYTES_PER_INST = 4;

//######################################################################

class TableVisitor;

class TableSimulateVisitor final : public SimulateVisitor {
    // MEMBERS
    TableVisitor* const m_cbthis;  ///< Class for callback

public:
    ///< Call other-this function on all new var references
    virtual void varRefCb(AstVarRef* nodep) override;

    // CONSTRUCTORS
    explicit TableSimulateVisitor(TableVisitor* cbthis)
        : m_cbthis{cbthis} {}
    virtual ~TableSimulateVisitor() override = default;
};

//######################################################################
// Class for holding lookup table state during construction

class TableBuilder final {
    FileLine* const m_fl;  // FileLine used during construction
    AstInitArray* m_initp = nullptr;  // The lookup table initializer values
    AstVarScope* m_varScopep = nullptr;  // The scoped variable holding the table

public:
    explicit TableBuilder(FileLine* fl)
        : m_fl{fl} {}

    ~TableBuilder() {
        if (m_initp) m_initp->deleteTree();
    }

    void setTableSize(AstNodeDType* elemDType, unsigned size) {
        UASSERT_OBJ(!m_initp, m_fl, "Table size already set");
        UASSERT_OBJ(size > 0, m_fl, "Size zero");
        // TODO: Assert elemDType is a packed type
        // Create data type
        const int width = elemDType->width();
        AstNodeDType* const subDTypep
            = elemDType->isString()
                  ? elemDType
                  : v3Global.rootp()->findBitDType(width, width, VSigning::UNSIGNED);
        AstUnpackArrayDType* const tableDTypep = new AstUnpackArrayDType{
            m_fl, subDTypep, new AstRange{m_fl, static_cast<int>(size), 0}};
        v3Global.rootp()->typeTablep()->addTypesp(tableDTypep);
        // Create table initializer (with default value 0)
        AstConst* const defaultp = elemDType->isString()
                                       ? new AstConst{m_fl, AstConst::String(), ""}
                                       : new AstConst{m_fl, AstConst::WidthedValue(), width, 0};
        m_initp = new AstInitArray{m_fl, tableDTypep, defaultp};
    }

    void addValue(unsigned index, const V3Number& value) {
        UASSERT_OBJ(!m_varScopep, m_fl, "Table variable already created");
        // Default value is zero/empty string so don't add it
        if (value.isString() ? value.toString().empty() : value.isEqZero()) return;
        m_initp->addIndexValuep(index, new AstConst{m_fl, value});
    }

    AstVarScope* varScopep() {
        if (!m_varScopep) { m_varScopep = v3Global.rootp()->constPoolp()->findTable(m_initp); }
        return m_varScopep;
    }
};

//######################################################################
// Class for holding output variable state during table conversion of logic

class TableOutputVar final {
    AstVarScope* const m_varScopep;  // The output variable
    const unsigned m_ord;  // Output ordinal number in this block
    bool m_mayBeUnassigned = false;  // If true, then this variable may be unassigned through
                                     // some path through the block being table converted
    TableBuilder m_tableBuilder;

public:
    TableOutputVar(AstVarScope* varScopep, unsigned ord)
        : m_varScopep{varScopep}
        , m_ord{ord}
        , m_tableBuilder{varScopep->fileline()} {}

    AstVarScope* varScopep() const { return m_varScopep; }
    string name() const { return varScopep()->varp()->name(); }
    unsigned ord() const { return m_ord; }
    void setMayBeUnassigned() { m_mayBeUnassigned = true; }
    bool mayBeUnassigned() const { return m_mayBeUnassigned; }
    void setTableSize(unsigned size) { m_tableBuilder.setTableSize(varScopep()->dtypep(), size); }
    void addValue(unsigned index, const V3Number& value) { m_tableBuilder.addValue(index, value); }
    AstVarScope* tabeVarScopep() { return m_tableBuilder.varScopep(); }
};

//######################################################################
// Table class functions

class TableVisitor final : public VNVisitor {
private:
    // NODE STATE
    // Cleared on each always/assignw

    // STATE
    double m_totalBytes = 0;  // Total bytes in tables created
    VDouble0 m_statTablesCre;  // Statistic tracking

    //  State cleared on each module
    AstNodeModule* m_modp = nullptr;  // Current MODULE
    int m_modTables = 0;  // Number of tables created in this module

    //  State cleared on each scope
    AstScope* m_scopep = nullptr;  // Current SCOPE

    //  State cleared on each always/assignw
    bool m_assignDly = false;  // Consists of delayed assignments instead of normal assignments
    unsigned m_inWidthBits = 0;  // Input table width - in bits
    unsigned m_outWidthBytes = 0;  // Output table width - in bytes
    std::vector<AstVarScope*> m_inVarps;  // Input variable list
    std::vector<TableOutputVar> m_outVarps;  // Output variable list

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

public:
    void simulateVarRefCb(AstVarRef* nodep) {
        // Called by TableSimulateVisitor on each unique varref encountered
        UINFO(9, "   SimVARREF " << nodep << endl);
        AstVarScope* const vscp = nodep->varScopep();
        if (nodep->access().isWriteOrRW()) {
            // We'll make the table with a separate natural alignment for each output var, so
            // always have 8, 16 or 32 bit widths, so use widthTotalBytes
            m_outWidthBytes += nodep->varp()->dtypeSkipRefp()->widthTotalBytes();
            m_outVarps.emplace_back(vscp, m_outVarps.size());
        }
        if (nodep->access().isReadOrRW()) {
            m_inWidthBits += nodep->varp()->width();
            m_inVarps.push_back(vscp);
        }
    }

private:
    bool treeTest(AstAlways* nodep) {
        // Process alw/assign tree
        m_inWidthBits = 0;
        m_outWidthBytes = 0;
        m_inVarps.clear();
        m_outVarps.clear();

        // Collect stats
        TableSimulateVisitor chkvis{this};
        chkvis.mainTableCheck(nodep);
        m_assignDly = chkvis.isAssignDly();
        // Also sets m_inWidthBits
        // Also sets m_outWidthBytes
        // Also sets m_inVarps
        // Also sets m_outVarps

        // Calc data storage in bytes
        const size_t chgWidth = m_outVarps.size();
        const double space = std::pow<double>(2.0, m_inWidthBits) * (m_outWidthBytes + chgWidth);
        // Instruction count bytes (ok, it's space also not time :)
        const double time  // max(_, 1), so we won't divide by zero
            = std::max<double>(chkvis.instrCount() * TABLE_BYTES_PER_INST + chkvis.dataCount(), 1);
        if (chkvis.instrCount() < TABLE_MIN_NODE_COUNT) {
            chkvis.clearOptimizable(nodep, "Table has too few nodes involved");
        }
        if (space > TABLE_MAX_BYTES) {
            chkvis.clearOptimizable(nodep, "Table takes too much space");
        }
        if (space > time * TABLE_SPACE_TIME_MULT) {
            chkvis.clearOptimizable(nodep, "Table has bad tradeoff");
        }
        if (m_totalBytes > TABLE_TOTAL_BYTES) {
            chkvis.clearOptimizable(nodep, "Table out of memory");
        }
        if (!m_outWidthBytes || !m_inWidthBits) {
            chkvis.clearOptimizable(nodep, "Table has no outputs");
        }
        if (chkvis.isOutputter()) {
            chkvis.clearOptimizable(nodep, "Table creates display output");
        }
        UINFO(4, "  Test: Opt=" << (chkvis.optimizable() ? "OK" : "NO") << ", Instrs="
                                << chkvis.instrCount() << " Data=" << chkvis.dataCount()
                                << " in width (bits)=" << m_inWidthBits << " out width (bytes)="
                                << m_outWidthBytes << " Spacetime=" << (space / time) << "("
                                << space << "/" << time << ")"
                                << ": " << nodep << endl);
        if (chkvis.optimizable()) {
            UINFO(3, " Table Optimize spacetime=" << (space / time) << " " << nodep << endl);
            m_totalBytes += space;
        }
        return chkvis.optimizable();
    }

    void replaceWithTable(AstAlways* nodep) {
        // We've determined this table of nodes is optimizable, do it.
        ++m_modTables;
        ++m_statTablesCre;

        FileLine* const fl = nodep->fileline();

        // We will need a table index variable, create it here.
        AstVar* const indexVarp
            = new AstVar{fl, VVarType::BLOCKTEMP, "__Vtableidx" + cvtToStr(m_modTables),
                         VFlagBitPacked{}, static_cast<int>(m_inWidthBits)};
        m_modp->addStmtp(indexVarp);
        AstVarScope* const indexVscp = new AstVarScope{indexVarp->fileline(), m_scopep, indexVarp};
        m_scopep->addVarp(indexVscp);

        // The 'output assigned' table builder
        TableBuilder outputAssignedTableBuilder{fl};
        outputAssignedTableBuilder.setTableSize(
            nodep->findBitDType(m_outVarps.size(), m_outVarps.size(), VSigning::UNSIGNED),
            VL_MASK_I(m_inWidthBits));

        // Set sizes of output tables
        for (TableOutputVar& tov : m_outVarps) { tov.setTableSize(VL_MASK_I(m_inWidthBits)); }

        // Populate the tables
        createTables(nodep, outputAssignedTableBuilder);

        AstNode* const stmtsp = createLookupInput(fl, indexVscp);
        createOutputAssigns(nodep, stmtsp, indexVscp, outputAssignedTableBuilder.varScopep());

        // Link it in.
        // Keep sensitivity list, but delete all else
        nodep->bodysp()->unlinkFrBackWithNext()->deleteTree();
        nodep->addStmtp(stmtsp);
        if (debug() >= 6) nodep->dumpTree(cout, "  table_new: ");
    }

    void createTables(AstAlways* nodep, TableBuilder& outputAssignedTableBuilder) {
        // Create table
        // There may be a simulation path by which the output doesn't change value.
        // We could bail on these cases, or we can have a "change it" boolean.
        // We've chosen the latter route, since recirc is common in large FSMs.
        TableSimulateVisitor simvis{this};
        for (uint32_t i = 0; i <= VL_MASK_I(m_inWidthBits); ++i) {
            const uint32_t inValue = i;
            // Make a new simulation structure so we can set new input values
            UINFO(8, " Simulating " << std::hex << inValue << endl);

            // Above simulateVisitor clears user 3, so
            // all outputs default to nullptr to mean 'recirculating'.
            simvis.clear();

            // Set all inputs to the constant
            uint32_t shift = 0;
            for (AstVarScope* invscp : m_inVarps) {
                // LSB is first variable, so extract it that way
                const AstConst cnst(invscp->fileline(), AstConst::WidthedValue(), invscp->width(),
                                    VL_MASK_I(invscp->width()) & (inValue >> shift));
                simvis.newValue(invscp, &cnst);
                shift += invscp->width();
                // We are using 32 bit arithmetic, because there's no way the input table can be
                // 2^32 bytes!
                UASSERT_OBJ(shift <= 32, nodep, "shift overflow");
                UINFO(8, "   Input " << invscp->name() << " = " << cnst.name() << endl);
            }

            // Simulate
            simvis.mainTableEmulate(nodep);
            UASSERT_OBJ(simvis.optimizable(), simvis.whyNotNodep(),
                        "Optimizable cleared, even though earlier test run said not: "
                            << simvis.whyNotMessage());

            // Build output value tables and the assigned flags table
            V3Number outputAssignedMask{nodep, static_cast<int>(m_outVarps.size()), 0};
            for (TableOutputVar& tov : m_outVarps) {
                if (V3Number* const outnump = simvis.fetchOutNumberNull(tov.varScopep())) {
                    UINFO(8, "   Output " << tov.name() << " = " << *outnump << endl);
                    outputAssignedMask.setBit(tov.ord(), 1);  // Mark output as assigned
                    tov.addValue(inValue, *outnump);
                } else {
                    UINFO(8, "   Output " << tov.name() << " not set for this input\n");
                    tov.setMayBeUnassigned();
                }
            }

            // Set changed table
            outputAssignedTableBuilder.addValue(inValue, outputAssignedMask);
        }  // each value
    }

    AstNode* createLookupInput(FileLine* fl, AstVarScope* indexVscp) {
        // Concat inputs into a single temp variable (inside always)
        // First var in inVars becomes the LSB of the concat
        AstNode* concatp = nullptr;
        for (AstVarScope* invscp : m_inVarps) {
            AstVarRef* const refp = new AstVarRef{fl, invscp, VAccess::READ};
            if (concatp) {
                concatp = new AstConcat{fl, refp, concatp};
            } else {
                concatp = refp;
            }
        }

        return new AstAssign{fl, new AstVarRef{fl, indexVscp, VAccess::WRITE}, concatp};
    }

    AstArraySel* select(FileLine* fl, AstVarScope* fromp, AstVarScope* indexp) {
        AstVarRef* const fromRefp = new AstVarRef{fl, fromp, VAccess::READ};
        AstVarRef* const indexRefp = new AstVarRef{fl, indexp, VAccess::READ};
        return new AstArraySel{fl, fromRefp, indexRefp};
    }

    void createOutputAssigns(AstNode* nodep, AstNode* stmtsp, AstVarScope* indexVscp,
                             AstVarScope* outputAssignedTableVscp) {
        FileLine* const fl = nodep->fileline();
        for (TableOutputVar& tov : m_outVarps) {
            AstNode* const alhsp = new AstVarRef{fl, tov.varScopep(), VAccess::WRITE};
            AstNode* const arhsp = select(fl, tov.tabeVarScopep(), indexVscp);
            AstNode* outsetp = m_assignDly
                                   ? static_cast<AstNode*>(new AstAssignDly{fl, alhsp, arhsp})
                                   : static_cast<AstNode*>(new AstAssign{fl, alhsp, arhsp});

            // If this output is unassigned on some code paths, wrap the assignment in an If
            if (tov.mayBeUnassigned()) {
                V3Number outputChgMask{nodep, static_cast<int>(m_outVarps.size()), 0};
                outputChgMask.setBit(tov.ord(), 1);
                AstNode* const condp
                    = new AstAnd{fl, select(fl, outputAssignedTableVscp, indexVscp),
                                 new AstConst{fl, outputChgMask}};
                outsetp = new AstIf{fl, condp, outsetp};
            }

            stmtsp->addNext(outsetp);
        }
    }

    // VISITORS
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }
    virtual void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        VL_RESTORER(m_modTables);
        {
            m_modp = nodep;
            m_modTables = 0;
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstScope* nodep) override {
        UINFO(4, " SCOPE " << nodep << endl);
        m_scopep = nodep;
        iterateChildren(nodep);
        m_scopep = nullptr;
    }
    virtual void visit(AstAlways* nodep) override {
        UINFO(4, "  ALWAYS  " << nodep << endl);
        if (treeTest(nodep)) {
            // Well, then, I'll be a memory hog.
            replaceWithTable(nodep);
        }
    }
    virtual void visit(AstNodeAssign* nodep) override {
        // It's nearly impossible to have a large enough assign to make this worthwhile
        // For now we won't bother.
        // Accelerated: no iterate
    }

public:
    // CONSTRUCTORS
    explicit TableVisitor(AstNetlist* nodep) { iterate(nodep); }
    virtual ~TableVisitor() override {  //
        V3Stats::addStat("Optimizations, Tables created", m_statTablesCre);
    }
};

//######################################################################

void TableSimulateVisitor::varRefCb(AstVarRef* nodep) {
    // Called by checking on each new varref encountered
    // We cross-call into a TableVisitor function.
    m_cbthis->simulateVarRefCb(nodep);
}

//######################################################################
// Table class functions

void V3Table::tableAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { TableVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("table", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
