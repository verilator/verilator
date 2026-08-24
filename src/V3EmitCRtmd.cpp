// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for the run time model descriptors
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
//
// Emits the descriptor tables of the model:
//
// - Data type table (VlRtmdDataTypeRow), one row per type descriptor, each holding the
//   descriptor itself. The members of a struct or union, and the items of an enum, are the rows
//   following it.
// - Global table (VlRtmdGlobalSymRow), the global variables of Signal rows flagged IS_GLOBAL,
//   which are constant pool entries. Index 0 is not used, and is nullptr.
// - Signal type table (VlRtmdSignalTypeRow), one row per signal type descriptor.
// - Activity set table (VlRtmdActSetRow). The first rows are the row range of each set, by set
//   index, so a signal's set index is its row. The rest are the flag numbers of all sets, each
//   set's following the previous. An empty set means the signal never changes.
// - Hierarchy table (VlRtmdHierRow), one row per descriptor entry, ending with the Pop of the
//   root level. Values are located by offset from the symbol table, or, for constant pool
//   entries, via the global table.
//
//*************************************************************************

#include "V3PchAstMT.h"

#include "V3EmitC.h"
#include "V3EmitCBase.h"
#include "V3File.h"
#include "V3Stats.h"

#include <algorithm>
#include <string>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Base of the emitters of a run time model descriptor table

class EmitCRtmdTableBase VL_NOT_FINAL : public EmitCBaseVisitorConst {
    // STATE
    const std::string m_rowType;  // Type of the rows of the table
    const std::string m_symbol;  // Name of the table
    const char* const m_descriptionp;  // Description of the table, for the file headers
    const uint64_t m_chunkRows;  // Rows per chunk
    const bool m_split = m_chunkRows < (uint64_t{1} << 32);  // Chunks in their own files
    uint32_t m_nRows = 0;  // Number of rows so far
    uint32_t m_nChunks = 0;  // Number of chunks so far
    bool m_needComma = false;  // Row has an argument already. Cleared by beginRow, set by putArg

    // METHODS

    // Name of chunk 'index' of the table
    std::string chunkName(uint32_t index) const {
        return m_symbol + "__chunk__" + std::to_string(index);
    }

    // Open the file of the next chunk, and begin its array
    void openChunk() {
        const std::string fileName
            = m_split ? m_symbol + "__" + std::to_string(m_nChunks) : m_symbol;
        const std::string name = chunkName(m_nChunks++);
        openNewOutputSourceFile(fileName, true, true, m_descriptionp);
        putPrologue();
        puts("\nVL_CONSTINIT_CXX20 extern const " + m_rowType + " " + name + "[] = {\n");
    }
    // End the array of the current chunk, and close its file, if its own
    void closeChunk() {
        puts("};\n");
        putEpilogue();
        if (m_split) closeOutputFile();
    }

protected:
    // VISITORS
    void visit(AstNode* nodep) override { nodep->v3fatalSrc("Unexpected node"); }

    // METHODS

    // Return as a C string literal
    static std::string stringLiteral(const std::string& str) {
        return '"' + V3OutFormatter::quoteNameControls(str) + '"';
    }
    // Return the name of the node as a C string literal
    static std::string nameLiteral(const AstNode* nodep) {
        return stringLiteral(VIdProtect::protectWordsIf(nodep->name(), nodep->protect()));
    }

    // Number of rows so far, which is the index of the next row
    uint32_t nRows() const { return m_nRows; }
    // Rows per chunk
    uint64_t chunkRows() const { return m_chunkRows; }

    // Put the start of a file of the table, before its array, and the end, after it
    virtual void putPrologue() = 0;
    virtual void putEpilogue() = 0;

    // Begin and end the table. There is always at least one chunk, even if empty. The table of
    // the chunks is in the file named after the table.
    void beginTable() { openChunk(); }
    void endTable() {
        closeChunk();
        // The table is split into multiple files, so use parallel build
        if (m_nChunks > 1) v3Global.useParallelBuild(true);
        if (m_split) {
            openNewOutputSourceFile(m_symbol, true, true, m_descriptionp);
            puts("\n#include \"verilated_rtmd.h\"\n\n");
            for (uint32_t i = 0; i < m_nChunks; ++i) {
                puts("extern const " + m_rowType + " " + chunkName(i) + "[];\n");
            }
        }
        puts("\nVL_CONSTINIT_CXX20 extern const " + m_rowType + "* const " + m_symbol
             + "[] = {\n");
        for (uint32_t i = 0; i < m_nChunks; ++i) { puts("    " + chunkName(i) + ",\n"); }
        puts("};\n");
        closeOutputFile();
    }

    // A row of the table. 'kind' is the type nested in the row type to construct the row from,
    // from the arguments.
    void beginRow(const std::string& kind) {
        // Continue in the next chunk if the current one is full
        if (m_nRows && m_nRows % m_chunkRows == 0) {
            closeChunk();
            openChunk();
        }
        if (v3Global.opt.decoration()) puts("/*" + std::to_string(m_nRows) + "*/ ");
        ++m_nRows;
        puts(m_rowType + "::" + kind + "{");
        m_needComma = false;
    }
    void putArg(const std::string& arg) {
        if (m_needComma) puts(", ");
        puts(arg);
        m_needComma = true;
    }
    void endRow(const std::string& comment = "") {
        puts("}");
        const bool hasComment
            = !comment.empty() && v3Global.opt.decoration() && !v3Global.opt.protectIds();
        puts(hasComment ? ", // " + comment + "\n" : ",\n");
    }

    // CONSTRUCTORS
    EmitCRtmdTableBase(const std::string& rowType, const std::string& symbol,
                       const char* descriptionp, uint32_t chunkSizeLog2)
        : m_rowType{rowType}
        , m_symbol{symbol}
        , m_descriptionp{descriptionp}
        , m_chunkRows{uint64_t{1} << chunkSizeLog2} {}
};

//######################################################################
// Rtmd activity set table emitter

class EmitCRtmdActSets final : public EmitCRtmdTableBase {
    // METHODS
    void putPrologue() override { puts("\n#include \"verilated_rtmd.h\"\n"); }
    void putEpilogue() override {}

    // CONSTRUCTORS
    explicit EmitCRtmdActSets(AstNetlist* netlistp)
        : EmitCRtmdTableBase{"VlRtmdActSetRow", EmitCUtil::rtmdActSetTableName(),
                             "RTMD activity flag sets", 32} {
        const std::vector<std::vector<uint32_t>>& sets = netlistp->actSets();
        beginTable();
        // The row range of each set, the flags starting after these rows
        size_t begin = sets.size();
        for (const std::vector<uint32_t>& set : sets) {
            const size_t end = begin + set.size();
            const std::string comment = [&]() -> std::string {
                if (set.empty()) return "empty";
                std::string str = "flags";
                for (const uint32_t flag : set) str += " " + std::to_string(flag);
                return str;
            }();
            beginRow("Range");
            putArg(std::to_string(begin));
            putArg(std::to_string(end));
            endRow(comment);
            begin = end;
        }
        // The flags of each set
        for (size_t id = 0; id < sets.size(); ++id) {
            for (const uint32_t flag : sets[id]) {
                beginRow("Flag");
                putArg(std::to_string(flag) + "U");
                endRow("In set " + std::to_string(id));
            }
        }
        endTable();
        V3Stats::addStat("Emit, Rtmd activity set table rows", nRows());
    }

public:
    static void apply(AstNetlist* netlistp) { EmitCRtmdActSets{netlistp}; }
};

//######################################################################
// Rtmd data type table emitter

class EmitCRtmdDataTypes final : public EmitCRtmdTableBase {
    // METHODS
    void putPrologue() override {
        puts("\n#include \"" + EmitCUtil::pchClassName() + ".h\"\n");
        puts("\n#include \"verilated_rtmd.h\"\n");
        putOffsetofPragmaPush();
    }
    void putEpilogue() override { putOffsetofPragmaPop(); }

    // VISITORS - Each type puts its row, then the rows of its members or items
    using EmitCRtmdTableBase::visit;
    void visit(AstRtmdDTAtom* nodep) override {
        beginRow("Atom");
        putArg("VlRtmdDataTypeRow::Atom::Kind::"s + nodep->keyword().rtmdAtomKind());
        putArg(nodep->isSigned() ? "true" : "false");
        putArg(std::to_string(nodep->bits()));
        endRow(nodep->keyword().ascii() + (nodep->isSigned() ? " signed"s : ""s));
    }

    void visit(AstRtmdDTEnum* nodep) override {
        const std::string baseIdx = std::to_string(nodep->rtmddtp()->user2());
        beginRow("Enum");
        putArg(nameLiteral(nodep));
        putArg(baseIdx);
        putArg(std::to_string(nodep->itemspList().size()));
        endRow("enum " + nodep->name() + " of #" + baseIdx);
        for (const AstRtmdEnumItem* const ip : nodep->itemspList()) {
            beginRow("EnumItem");
            putArg(nameLiteral(ip));
            putArg(stringLiteral(ip->value()));
            endRow("item " + ip->name());
        }
    }

    void visit(AstRtmdDTPackedArray* nodep) override {
        const std::string lStr = std::to_string(nodep->left());
        const std::string rStr = std::to_string(nodep->right());
        const std::string elemIdx = std::to_string(nodep->elemRtmddtp()->user2());
        beginRow("PackedArray");
        putArg(lStr);
        putArg(rStr);
        putArg(elemIdx);
        putArg(nodep->isSigned() ? "true" : "false");
        endRow((nodep->isSigned() ? "signed "s : ""s) + "[" + lStr + ":" + rStr + "] of #"
               + elemIdx);
    }

    void visit(AstRtmdDTPackedStruct* nodep) override {
        beginRow("PackedStruct");
        putArg(std::to_string(nodep->memberspList().size()));
        putArg(nodep->isSigned() ? "true" : "false");
        endRow("struct packed"s + (nodep->isSigned() ? " signed" : ""));
        for (const AstRtmdMember* const mp : nodep->memberspList()) {
            const std::string memberIdx = std::to_string(mp->rtmddtp()->user2());
            beginRow("Member");
            putArg(nameLiteral(mp));
            putArg(memberIdx);
            putArg(std::to_string(mp->lsb()));
            endRow("member " + mp->name() + " of #" + memberIdx);
        }
    }

    void visit(AstRtmdDTPackedUnion* nodep) override {
        beginRow("PackedUnion");
        putArg(std::to_string(nodep->memberspList().size()));
        putArg(nodep->isSigned() ? "true" : "false");
        endRow("union packed"s + (nodep->isSigned() ? " signed" : ""));
        // The members, with the bit offset of their LSB
        for (const AstRtmdMember* const mp : nodep->memberspList()) {
            const std::string memberIdx = std::to_string(mp->rtmddtp()->user2());
            beginRow("Member");
            putArg(nameLiteral(mp));
            putArg(memberIdx);
            putArg(std::to_string(mp->lsb()));
            endRow("member " + mp->name() + " of #" + memberIdx);
        }
    }

    void visit(AstRtmdDTUnpackedArray* nodep) override {
        const std::string lStr = std::to_string(nodep->left());
        const std::string rStr = std::to_string(nodep->right());
        const std::string elemIdx = std::to_string(nodep->elemRtmddtp()->user2());
        const std::string elemType = nodep->dtypep()->subDTypep()->cType("", false, false);
        beginRow("UnpackedArray");
        putArg(lStr);
        putArg(rStr);
        putArg(elemIdx);
        putArg("sizeof(" + elemType + ")");
        endRow("[" + lStr + ":" + rStr + "] of #" + elemIdx);
    }

    void visit(AstRtmdDTUnpackedStruct* nodep) override {
        beginRow("UnpackedStruct");
        putArg(std::to_string(nodep->memberspList().size()));
        endRow("struct");
        const std::string structType = EmitCUtil::prefixNameProtect(nodep->dtypep());
        const AstMemberDType* dtMemberp = VN_AS(nodep->dtypep(), StructDType)->membersp();
        for (const AstRtmdMember* const mp : nodep->memberspList()) {
            UASSERT_OBJ(dtMemberp, mp, "Member without a data type");
            const std::string memberIdx = std::to_string(mp->rtmddtp()->user2());
            beginRow("Member");
            putArg(nameLiteral(mp));
            putArg(memberIdx);
            putArg("offsetof(" + structType + ", " + dtMemberp->nameProtect() + ")");
            endRow("member " + mp->name() + " of #" + memberIdx);
            dtMemberp = VN_AS(dtMemberp->nextp(), MemberDType);
        }
    }

    // CONSTRUCTORS
    explicit EmitCRtmdDataTypes(AstNetlist* netlistp)
        : EmitCRtmdTableBase{"VlRtmdDataTypeRow", EmitCUtil::rtmdDataTypeTableName(),
                             "RTMD data type table", v3Global.opt.outputSplitRtmd()} {
        beginTable();
        for (AstNodeRtmdDataType* const typep : netlistp->typeTablep()->rtmdDataTypespList()) {
            // Record the row index of this type
            typep->user2(nRows());
            // Emit it
            iterateConst(typep);
        }
        beginRow("End");
        endRow("end of table");
        endTable();
        V3Stats::addStat("Emit, Rtmd data type table rows", nRows());
    }

public:
    static void apply(AstNetlist* netlistp) { EmitCRtmdDataTypes{netlistp}; }
};

//######################################################################
// Rtmd global symbol table emitter

class EmitCRtmdGlobalSyms final : public EmitCRtmdTableBase {
    // STATE
    std::vector<const AstVar*> m_varps;  // The globals, the one of row 'i' at index 'i - 1'

    // METHODS
    void putPrologue() override {
        puts("\n#include \"" + EmitCUtil::pchClassName() + ".h\"\n");
        puts("\n#include \"verilated_rtmd.h\"\n");
        // Declarations of the globals of the rows of this chunk - these will need relocations
        const size_t begin = nRows() ? nRows() - 1 : 0;
        const size_t end = std::min<size_t>(nRows() + chunkRows() - 1, m_varps.size());
        for (size_t i = begin; i < end; ++i) {
            if (i == begin) puts("\n");
            const AstVar* const varp = m_varps[i];
            const std::string name = EmitCUtil::constPoolName(varp);
            putns(varp, "extern const " + varp->dtypep()->cType(name, false, false) + ";\n");
        }
    }
    void putEpilogue() override {}

    // CONSTRUCTORS
    explicit EmitCRtmdGlobalSyms(AstNetlist* netlistp)
        : EmitCRtmdTableBase{"VlRtmdGlobalSymRow", EmitCUtil::rtmdGlobalTableName(),
                             "RTMD global symbol table", v3Global.opt.outputSplitRtmd()} {
        // Gather the globals, recording the index of each
        netlistp->topScopep()->rtmdp()->foreach([&](AstRtmdSignal* sigp) {
            if (!sigp->refp()) return;
            AstVar* const varp = sigp->varp();
            if (!varp->constPoolEntry() || varp->user2()) return;
            m_varps.push_back(varp);
            varp->user2(m_varps.size());
        });

        // Table
        beginTable();
        beginRow("Const");
        putArg("nullptr");
        endRow("not used");
        for (const AstVar* const varp : m_varps) {
            beginRow("Const");
            putArg("&" + EmitCUtil::constPoolName(varp));
            endRow(varp->name());
        }
        endTable();
        V3Stats::addStat("Emit, Rtmd global symbol table rows", nRows());
    }

public:
    static void apply(AstNetlist* netlistp) { EmitCRtmdGlobalSyms{netlistp}; }
};

//######################################################################
// Rtmd signal type table emitter

class EmitCRtmdSignalTypes final : public EmitCRtmdTableBase {
    // METHODS
    void putPrologue() override { puts("\n#include \"verilated_rtmd.h\"\n"); }
    void putEpilogue() override {}

    // CONSTRUCTORS
    explicit EmitCRtmdSignalTypes(AstNetlist* netlistp)
        : EmitCRtmdTableBase{"VlRtmdSignalTypeRow", EmitCUtil::rtmdSignalTypeTableName(),
                             "RTMD signal type table", v3Global.opt.outputSplitRtmd()} {
        beginTable();
        for (AstRtmdSignalType* const sigTypep : netlistp->typeTablep()->rtmdSignalTypespList()) {
            sigTypep->user2(nRows());
            beginRow("Signal");
            putArg("VlRtmdSignalTypeRow::Signal::Kind::"s + sigTypep->kind().ascii());
            putArg("VlRtmdSignalTypeRow::Signal::Direction::"s + sigTypep->direction().ascii());
            putArg(std::to_string(sigTypep->rtmddtp()->user2()));
            endRow();
        }
        endTable();
        V3Stats::addStat("Emit, Rtmd signal type table rows", nRows());
    }

public:
    static void apply(AstNetlist* netlistp) { EmitCRtmdSignalTypes{netlistp}; }
};

//######################################################################
// Rtmd hierarchy table emitter

class EmitCRtmdHier final : public EmitCRtmdTableBase {
    // NODE STATE
    //  AstRtmdHier::user1()  // int; 0: unknown, else EVALUATED, HAS_SIGNALS, HAS_TRACED
    const VNUser1InUse m_user1InUse;
    static constexpr int EVALUATED = 1;  // The other flags are known
    static constexpr int HAS_SIGNALS = 2;  // Some signals are under it
    static constexpr int HAS_TRACED = 4;  // Some traced signals are under it

    // METHODS

    void putPrologue() override {
        puts("\n#include \"" + EmitCUtil::pchClassName() + ".h\"\n");
        puts("#include \"verilated_rtmd.h\"\n");
        putOffsetofPragmaPush();
        const std::string symCls = EmitCUtil::symClassName();
        puts("\n#define VL_RTMD_OFFSETOF(scopeType, scope, member) \\\n");
        puts("    (offsetof(" + symCls + ", scope) + offsetof(scopeType, member))\n");
    }
    void putEpilogue() override {
        puts("\n#undef VL_RTMD_OFFSETOF\n");
        putOffsetofPragmaPop();
    }

    // Computes the offset of a signal's storage from the model symbol table
    static std::string valueOffset(const AstRtmdSignal* sigp) {
        const AstScope* const scopep = sigp->refScopep();
        return "VL_RTMD_OFFSETOF(" + EmitCUtil::prefixNameProtect(scopep->modp()) + ", "
               + instName(scopep) + ", " + varName(sigp->varp()) + ")";
    }

    // What is present under levelp: some signals, and some traced signals, see m_user1InUse
    static int signalsUnder(AstRtmdHier* levelp) {
        if (levelp->user1()) return levelp->user1();
        int flags = EVALUATED;
        for (AstNodeRtmdItem* const itemp : levelp->itemspList()) {
            if (AstRtmdHier* const subp = VN_CAST(itemp, RtmdHier)) {
                flags |= signalsUnder(subp);
            } else if (AstRtmdIfaceRef* const ifaceRefp = VN_CAST(itemp, RtmdIfaceRef)) {
                flags |= signalsUnder(ifaceRefp->ifaceRtmdp());
            } else if (VN_IS(itemp, RtmdPartition)) {
                flags |= HAS_SIGNALS | HAS_TRACED;  // Assume partitions are not empty
            } else if (const AstRtmdSignal* const sigp = VN_CAST(itemp, RtmdSignal)) {
                flags |= HAS_SIGNALS | (sigp->traced() ? HAS_TRACED : 0);
            }
        }
        levelp->user1(flags);
        return flags;
    }

    // Number the Push row of each level, from 'row', returns the row after the level
    static uint32_t numberRows(AstRtmdHier* levelp, uint32_t row) {
        levelp->user2(row++);  // Push
        for (AstNodeRtmdItem* const itemp : levelp->itemspList()) {
            if (AstRtmdHier* const subp = VN_CAST(itemp, RtmdHier)) {
                row = numberRows(subp, row);
            } else {
                ++row;
            }
        }
        return ++row;  // Pop
    }

    // The flags argument of a row, from the names of the flags that are set
    static std::string flagsArg(const std::string& cls, std::initializer_list<const char*> names) {
        std::string arg;
        for (const char* const namep : names) {
            if (!namep) continue;
            if (!arg.empty()) arg += " | ";
            arg += cls + "::" + namep;
        }
        return arg.empty() ? "0" : arg;
    }

    // VISITORS - Each item puts its rows
    using EmitCRtmdTableBase::visit;
    void visit(AstRtmdHier* nodep) override {
        // The rows of a hierarchy level, bracketed by a Push and a Pop
        const uint32_t pushRow = nRows();
        UASSERT_OBJ(nodep->user2() == pushRow, nodep, "Push row numbered wrong");
        beginRow("Push");
        putArg(nameLiteral(nodep));
        putArg("VlRtmdHierRow::Push::Kind::"s + nodep->kind().ascii());
        const int flags = signalsUnder(nodep);
        putArg(flagsArg("VlRtmdHierRow::HierFlags",
                        {flags & HAS_SIGNALS ? "HAS_SIGNALS" : nullptr,
                         flags & HAS_TRACED ? "HAS_TRACED_SIGNALS" : nullptr}));
        endRow("push");
        iterateAndNextConstNull(nodep->itemsp());
        beginRow("Pop");
        endRow("pop #" + std::to_string(pushRow));
    }

    void visit(AstRtmdIfaceRef* nodep) override {
        beginRow("IfaceRef");
        putArg(nameLiteral(nodep));
        putArg(std::to_string(nodep->ifaceRtmdp()->user2()));
        endRow();
    }

    void visit(AstRtmdInstance* nodep) override {
        beginRow("Instance");
        putArg(nameLiteral(nodep));
        endRow();
    }

    void visit(AstRtmdSignal* nodep) override {
        // A global is located via the global table, others by offset from the symbol table. A
        // signal whose value is not accessible has no location.
        const AstVar* const varp = nodep->refp() ? nodep->varp() : nullptr;
        const bool isGlobal = varp && varp->constPoolEntry();
        const std::string location = !varp      ? "VlRtmd::NOADDR"s
                                     : isGlobal ? std::to_string(varp->user2())
                                                : valueOffset(nodep);
        beginRow("Signal");
        putArg(nameLiteral(nodep));
        putArg(std::to_string(nodep->typeDescp()->user2()));
        // No activity set without tracing, or without a value
        putArg(nodep->hasActSet() ? std::to_string(nodep->actSetIdx()) : "VlRtmd::NOIDX"s);
        putArg(location);
        putArg(flagsArg("VlRtmdHierRow::SignalFlags", {isGlobal ? "IS_GLOBAL" : nullptr,
                                                       nodep->traced() ? "IS_TRACED" : nullptr}));
        endRow();
    }

    void visit(AstRtmdPartition* nodep) override {
        beginRow("Partition");
        putArg(nameLiteral(nodep));
        endRow();
    }

    // CONSTRUCTORS
    explicit EmitCRtmdHier(AstNetlist* netlistp)
        : EmitCRtmdTableBase{"VlRtmdHierRow", EmitCUtil::rtmdHierTableName(),
                             "RTMD hierarchy table", v3Global.opt.outputSplitRtmd()} {
        AstRtmdHier* const rootp = netlistp->topScopep()->rtmdp();
        UASSERT_OBJ(rootp->kind() == VRtmdHierKind::ROOT, rootp, "Top scope is not the root");
        const uint32_t nRowsExpected = numberRows(rootp, 0);
        beginTable();
        iterateConst(rootp);
        endTable();
        UASSERT_OBJ(nRows() == nRowsExpected, rootp, "Hierarchy rows numbered wrong");
        V3Stats::addStat("Emit, Rtmd hierarchy table rows", nRows());
    }

public:
    static void apply(AstNetlist* netlistp) { EmitCRtmdHier{netlistp}; }
};

//######################################################################
// Rtmd emit

void V3EmitC::emitcRtmd() {
    if (!v3Global.opt.rtmd()) return;

    UINFO(2, __FUNCTION__ << ":");
    // NODE STATE
    // AstNodeRtmdDataType::user2()   // uint32_t; Index of its row in the data type table
    // AstRtmdSignalType::user2()     // uint32_t; Index of its row in the signal type table
    // AstVar::user2()                // uint32_t; Index of its row in the global table, 0 if none
    // AstRtmdHier::user2()           // uint32_t; Index of its Push row in the hierarchy table
    const VNUser2InUse user2InUse;

    // Activity sets are only meaningful with the activity flags
    if (v3Global.rootp()->activityp()) EmitCRtmdActSets::apply(v3Global.rootp());
    EmitCRtmdDataTypes::apply(v3Global.rootp());
    EmitCRtmdGlobalSyms::apply(v3Global.rootp());
    EmitCRtmdSignalTypes::apply(v3Global.rootp());
    EmitCRtmdHier::apply(v3Global.rootp());
}
