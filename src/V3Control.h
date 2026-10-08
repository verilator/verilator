// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Verilator Control Files (.vlt) handling
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2010-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3CONFIG_H_
#define VERILATOR_V3CONFIG_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Error.h"
#include "V3FileLine.h"
#include "V3Mutex.h"

//######################################################################

// A reference out of a hierarchical block, promoted to an input port on it.
// Found in the plan run, written to the generated .vlt, and read back by the
// child run that creates the port and the top run that connects it.
class VHierXmrPort final {
    string m_refModule;  // Module the reference appears in
    string m_port;  // Generated port name
    string m_path;  // Dotted path of the signal it reads
    int m_width;  // Width, established before V3Width from the declared type
    bool m_signed;  // Whether the referenced signal is signed

public:
    VHierXmrPort(const string& refModule, const string& port, const string& path, int width,
                 bool isSigned)
        : m_refModule{refModule}
        , m_port{port}
        , m_path{path}
        , m_width{width}
        , m_signed{isSigned} {}
    const string& refModule() const { return m_refModule; }
    const string& port() const { return m_port; }
    const string& path() const { return m_path; }
    int width() const { return m_width; }
    bool isSigned() const { return m_signed; }
};

class V3Control final {
public:
    struct FsmRegisterWrapper final {
        string moduleName;
        string d;
        string q;
        string clock;
        string reset;
        string resetValue;
    };

    enum class VarSpecKind : uint8_t {
        PARAM,  // Select only matching parameters
        PORT,  // Select only matching ports
        VAR  // Select any matching AstVar (including params and ports)
    };

    static void addCaseFull(const string& file, int lineno);
    static void addCaseParallel(const string& file, int lineno);
    static void addCoverageBlockOff(const string& file, int lineno);
    static void addCoverageBlockOff(const string& module, const string& blockname);
    static void addHierWorkers(FileLine* fl, const string& model, int workers);
    static void addHierXmrPort(FileLine* fl, const string& block, const string& refModule,
                               const string& port, int width, bool isSigned, const string& path);
    static void addFsmRegisterWrapper(FileLine* fl, const string& module, const string& d,
                                      const string& q, const string& clock, const string& reset,
                                      const string& resetValue);
    static void addIgnore(V3ErrorCode code, bool on, const string& filename, int min, int max);
    static void addIgnoreMatch(V3ErrorCode code, const string& filename, const string& contents,
                               const string& match);
    static void addInline(FileLine* fl, const string& module, const string& ftask, bool on);
    static void addModulePragma(const string& module, VPragmaType pragma);
    static void addProfileData(FileLine* fl, const string& hierDpi, uint64_t cost);
    static void addProfileData(FileLine* fl, const string& model, const string& key,
                               uint64_t cost);
    static void addScopeTraceOn(bool on, const string& scope, int levels);
    static void addVarAttr(FileLine* fl, const string& module, const string& ftask,
                           VarSpecKind kind, const string& pattern, VAttrType type,
                           AstSenTree* nodep);

    static void applyCase(AstCase* nodep);
    static void applyCoverageBlock(AstNodeModule* modulep, AstBegin* nodep);
    static void applyCoverageBlock(AstNodeModule* modulep, AstGenBlock* nodep);
    static void applyFTask(AstNodeModule* modulep, AstNodeFTask* ftaskp);
    static void applyIgnores(FileLine* filelinep);
    static void applyModule(AstNodeModule* modulep);
    static void applyVarAttr(const AstNodeModule* modulep, const AstNodeFTask* ftaskp,
                             AstVar* varp);

    static int getHierWorkers(const string& model);
    // nullptr if the module has none; a reference return trips gcc's
    // -Wdangling-reference at every call site
    static const std::vector<VHierXmrPort>* getHierXmrPorts(const string& module);
    // Whether that module has a promoted port of this name
    static bool hasHierXmrPort(const string& module, const string& port);
    static FileLine* getHierWorkersFileLine(const string& model);
    static const FsmRegisterWrapper* getFsmRegisterWrapper(const string& module);
    static uint64_t getProfileData(const string& hierDpi);
    static uint64_t getProfileData(const string& model, const string& key);
    static FileLine* getProfileDataFileLine();
    static bool getScopeTraceOn(const string& scope);

    static void contentsPushText(const string& text);

    static bool containsMTaskProfileData();
    static uint64_t getCurrentHierBlockCost();

    static bool waive(const FileLine* filelinep, V3ErrorCode code, const string& message);

    static void selfTest();
};

#endif  // Guard
