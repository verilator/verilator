// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#include <verilated_rtmd.h>

#include <cstdio>
#include <memory>
#include <string>

#include VM_PREFIX_INCLUDE

// Prints the hierarchy enumerated by the walker, one line per level and signal
class HierPrinter final : public VlRtmdHierListener {
    const bool m_split;  // Walk the components of arrays, structs and unions
    int m_indent = 0;  // Current indentation level

    void line(const std::string& text) const {
        std::printf("%*s%s\n", 2 * m_indent, "", text.c_str());
    }
    bool open(const std::string& text, bool hasSignals) {
        line(text + (hasSignals ? "" : " (no signals)"));
        ++m_indent;
        return true;
    }
    void close(const std::string& text) {
        --m_indent;
        line(text);
    }

    static std::string kindName(VlRtmdSignalType::Kind kind) {
        switch (kind) {
        case VlRtmdSignalType::Kind::VAR: return "var"s;
        case VlRtmdSignalType::Kind::WIRE: return "wire"s;
        case VlRtmdSignalType::Kind::WREAL: return "wreal"s;
        case VlRtmdSignalType::Kind::TRI: return "tri"s;
        case VlRtmdSignalType::Kind::TRI0: return "tri0"s;
        case VlRtmdSignalType::Kind::TRI1: return "tri1"s;
        case VlRtmdSignalType::Kind::TRIAND: return "triand"s;
        case VlRtmdSignalType::Kind::TRIOR: return "trior"s;
        case VlRtmdSignalType::Kind::SUPPLY0: return "supply0"s;
        case VlRtmdSignalType::Kind::SUPPLY1: return "supply1"s;
        case VlRtmdSignalType::Kind::GPARAM: return "parameter"s;
        case VlRtmdSignalType::Kind::LPARAM: return "localparam"s;
        case VlRtmdSignalType::Kind::SPECPARAM: return "specparam"s;
        case VlRtmdSignalType::Kind::GENVAR: return "genvar"s;
        }
        return "?"s;
    }
    static std::string directionName(VlRtmdSignalType::Direction direction) {
        switch (direction) {
        case VlRtmdSignalType::Direction::NONE: return ""s;
        case VlRtmdSignalType::Direction::INPUT: return "input "s;
        case VlRtmdSignalType::Direction::OUTPUT: return "output "s;
        case VlRtmdSignalType::Direction::INOUT: return "inout "s;
        case VlRtmdSignalType::Direction::REF: return "ref "s;
        case VlRtmdSignalType::Direction::CONSTREF: return "const ref "s;
        }
        return "?"s;
    }
    static std::string instanceName(InstanceKind kind) {
        switch (kind) {
        case InstanceKind::MODULE: return "module"s;
        case InstanceKind::INTERFACE: return "interface"s;
        case InstanceKind::PACKAGE: return "package"s;
        }
        return "?"s;
    }
    static std::string scopeEnd(ScopeKind kind) {
        switch (kind) {
        case ScopeKind::ROOTIO: return "endrootio"s;
        case ScopeKind::FUNCTION: return "endfunction"s;
        case ScopeKind::TASK: return "endtask"s;
        case ScopeKind::GENERATE: return "endgenerate"s;
        case ScopeKind::BEGIN: return "end"s;
        case ScopeKind::FORK: return "join"s;
        }
        return "?"s;
    }
    static std::string scopeName(ScopeKind kind) {
        switch (kind) {
        case ScopeKind::ROOTIO: return "rootio"s;
        case ScopeKind::FUNCTION: return "function"s;
        case ScopeKind::TASK: return "task"s;
        case ScopeKind::GENERATE: return "generate"s;
        case ScopeKind::BEGIN: return "begin"s;
        case ScopeKind::FORK: return "fork"s;
        }
        return "?"s;
    }

protected:
    bool enterRoot(const VerilatedModel& model) override {
        return open(model.hierName() + " : $root"s, true);
    }
    void exitRoot(const VerilatedModel& model) override {
        close("end$root : "s + model.hierName());
    }
    bool enterInstance(InstanceKind kind, const char* namep, const char* modNamep,
                       HierFlags flags) override {
        return open(namep + " : "s + instanceName(kind) + " " + modNamep, flags.hasSignals());
    }
    void exitInstance(InstanceKind kind, const char* namep, const char*, HierFlags) override {
        close("end" + instanceName(kind) + " : " + namep);
    }
    bool enterIfaceRef(const char* namep, const char* modNamep, HierFlags flags) override {
        return open(namep + " : interface reference "s + modNamep, flags.hasSignals());
    }
    void exitIfaceRef(const char* namep, const char*, HierFlags) override {
        close("endinterface reference : "s + namep);
    }
    bool enterScope(ScopeKind kind, const char* namep, HierFlags flags) override {
        return open(namep + " : "s + scopeName(kind), flags.hasSignals());
    }
    void exitScope(ScopeKind kind, const char* namep, HierFlags) override {
        close(scopeEnd(kind) + " : " + namep);
    }
    // Print a value, and walk the parts of unpacked arrays and structs
    bool value(const std::string& name, const VlRtmdDataType& dtype, const void* datap) {
        line(name + " : " + dtype.toString() + (datap ? "" : " (no address)"));
        if (!m_split) return false;
        // Packed arrays of single bits, e.g. 'logic [7:0]', are not split, as too many
        if (dtype.isPackedArray()) return dtype.elemType().width() > 1;
        return dtype.isUnpackedArray() || dtype.isUnpackedStruct() || dtype.isPackedStruct()
               || dtype.isPackedUnion();
    }
    bool onSignal(const char* namep, const VlRtmdSignalType& sigType, const VlRtmdDataType& dtype,
                  const VlRtmdActSet&, const void* datap, SignalFlags) override {
        return value(directionName(sigType.direction()) + kindName(sigType.kind()) + " " + namep,
                     dtype, datap);
    }
    void enterUnpackedArray(const char*, const VlRtmdDataType& dtype) override {
        open("enter unpacked array ["s + std::to_string(dtype.left()) + ":"
                 + std::to_string(dtype.right()) + "]",
             true);
    }
    void exitUnpackedArray(const char*, const VlRtmdDataType&) override {
        close("exit unpacked array");
    }
    void enterUnpackedStruct(const char*, const VlRtmdDataType& dtype) override {
        open("enter unpacked struct, "s + std::to_string(dtype.memberCount()) + " members", true);
    }
    void exitUnpackedStruct(const char*, const VlRtmdDataType&) override {
        close("exit unpacked struct");
    }
    void enterPackedArray(const char*, const VlRtmdDataType& dtype) override {
        open("enter packed array ["s + std::to_string(dtype.left()) + ":"
                 + std::to_string(dtype.right()) + "]",
             true);
    }
    void exitPackedArray(const char*, const VlRtmdDataType&) override {
        close("exit packed array");
    }
    void enterPackedStruct(const char*, const VlRtmdDataType& dtype) override {
        open("enter packed struct, "s + std::to_string(dtype.memberCount()) + " members", true);
    }
    void exitPackedStruct(const char*, const VlRtmdDataType&) override {
        close("exit packed struct");
    }
    void enterPackedUnion(const char*, const VlRtmdDataType& dtype) override {
        open("enter packed union, "s + std::to_string(dtype.memberCount()) + " members", true);
    }
    void exitPackedUnion(const char*, const VlRtmdDataType&) override {
        close("exit packed union");
    }
    bool onComponent(const char* namep, const VlRtmdSignalType&, const VlRtmdDataType& dtype,
                     const VlRtmdActSet&, const void* datap, uint32_t lsb) override {
        // A component of a packed value is located by its bit offset
        return value(namep + (lsb != NOLSB ? " @" + std::to_string(lsb) : ""s), dtype, datap);
    }

public:
    explicit HierPrinter(bool split)
        : m_split{split} {}
};

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);
    // The name of the model is given by +topname=<name>
    const std::string topnameArg = contextp->commandArgsPlusMatch("topname=");
    if (topnameArg.empty()) {
        std::printf("%%Error: +topname=<name> is required\n");
        return 1;
    }
    const std::string topname = topnameArg.substr(9);
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), topname.c_str()}};

    // The partitions are created on the first evaluation
    topp->eval();

    // With +split, the components of unpacked arrays and structs are walked too
    const bool split = *contextp->commandArgsPlusMatch("split");
    HierPrinter{split}.walkContext(*contextp);

    std::printf("*-* All Finished *-*\n");
    return 0;
}
