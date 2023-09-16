// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Inlining of modules
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3TASK_H_
#define VERILATOR_V3TASK_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Error.h"

#include <utility>
#include <vector>

//============================================================================

using V3TaskConnect = std::pair<AstVar*, AstArg*>;  // [port, pin-connects-to]
using V3TaskConnects = std::vector<V3TaskConnect>;  // [ [port, pin-connects-to] ... ]

class V3TaskConnectState final {
    VNDeleter m_deleter;  // Allow delayed deletion of nodes
    bool m_didWrap = false;  // Made a wrapper
    using WrapMap = std::map<std::pair<AstNodeFTask*, std::string>, AstNodeFTask*>;
    WrapMap m_wrapMap;  // Map of {old function, arguments} -> new function
public:
    V3TaskConnectState() {}
    ~V3TaskConnectState() = default;
    void pushDeletep(AstNode* nodep) { m_deleter.pushDeletep(nodep); }
    bool didWrap() const { return m_didWrap; }
    void setDidWrap() { m_didWrap = true; }
    WrapMap& wrapMap() { return m_wrapMap; }
};

//============================================================================

class V3Task final {
    static const char* const s_dpiTemporaryVarSuffix;

public:
    static void taskAll(AstNetlist* nodep);
    /// Return vector of [port, pin-connects-to]  (SLOW)
    static V3TaskConnects taskConnects(AstNodeFTaskRef* nodep, AstNode* taskStmtsp,
                                       V3TaskConnectState* statep = nullptr);
    static void taskConnectWrap(AstNodeFTaskRef* nodep, const V3TaskConnects& tconnects,
                                V3TaskConnectState* statep,
                                const std::set<const AstVar*>& argWrap);
    static AstNodeFTask* taskConnectWrapNew(AstNodeFTask* taskp, const string& newname,
                                            const V3TaskConnects& tconnects,
                                            const std::set<const AstVar*>& argWrap);
    static string assignInternalToDpi(AstVar* portp, bool isPtr, const string& frSuffix,
                                      const string& toSuffix, const string& frPrefix = "");
    static string assignDpiToInternal(const string& lhsName, AstVar* rhsp);
    static const char* dpiTemporaryVarSuffix() VL_MT_SAFE { return s_dpiTemporaryVarSuffix; }
};

#endif  // Guard
