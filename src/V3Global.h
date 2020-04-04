// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Common headers
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef _V3GLOBAL_H_
#define _V3GLOBAL_H_ 1

#include "config_build.h"
#ifndef HAVE_CONFIG_BUILD
# error "Something failed during ./configure as config_build.h is incomplete. Perhaps you used autoreconf, don't."
#endif

#include "verilatedos.h"

#include "V3Error.h"
#include "V3FileLine.h"
#include "V3Options.h"

#include <string>

class AstNetlist;

//======================================================================
// Statics


//######################################################################

class VWidthMinUsage {
public:
    enum en {
        LINT_WIDTH,
        MATCHES_WIDTH,
        VERILOG_WIDTH
    };
    enum en m_e;
    inline VWidthMinUsage() : m_e(LINT_WIDTH) {}
    // cppcheck-suppress noExplicitConstructor
    inline VWidthMinUsage(en _e) : m_e(_e) {}
    explicit inline VWidthMinUsage(int _e) : m_e(static_cast<en>(_e)) {}
    operator en() const { return m_e; }
};
inline bool operator==(const VWidthMinUsage& lhs, const VWidthMinUsage& rhs) {
    return lhs.m_e == rhs.m_e;
}
inline bool operator==(const VWidthMinUsage& lhs, VWidthMinUsage::en rhs) {
    return lhs.m_e == rhs;
}
inline bool operator==(VWidthMinUsage::en lhs, const VWidthMinUsage& rhs) {
    return lhs == rhs.m_e;
}

//######################################################################
// V3Global - The top level class for the entire program

class V3Global {
    // Globals
    AstNetlist* m_rootp;  // Root of entire netlist
    VWidthMinUsage m_widthMinUsage;  // What AstNode::widthMin() is used for

    int m_debugFileNumber;  // Number to append to debug files created
    bool m_assertDTypesResolved;  // Tree should have dtypep()'s
    bool m_constRemoveXs;  // Const needs to strip any Xs
    bool m_needTraceDumper;  // Need __Vm_dumperp in symbols
    bool m_needHInlines;  // Need __Inlines file
    bool m_needHeavy;  // Need verilated_heavy.h include
    bool m_dpi;  // Need __Dpi include files

public:
    // Options
    V3Options opt;  // All options; let user see them directly

  public:
    // CONSTRUCTORS
    V3Global() {
        m_debugFileNumber = 0;
        m_widthMinUsage = VWidthMinUsage::LINT_WIDTH;
        m_assertDTypesResolved = false;
        m_constRemoveXs = false;
        m_needTraceDumper = false;
        m_needHInlines = false;
        m_needHeavy = false;
        m_dpi = false;
        m_rootp = NULL;  // created by makeInitNetlist() so static constructors run first
    }
    AstNetlist* makeNetlist();
    void boot() { UASSERT(!m_rootp,"call once"); m_rootp = makeNetlist(); }
    void clear();
    // ACCESSORS (general)
    AstNetlist* rootp() const { return m_rootp; }
    VWidthMinUsage widthMinUsage() const { return m_widthMinUsage; }
    bool assertDTypesResolved() const { return m_assertDTypesResolved; }

    // METHODS
    void readFiles();
    void checkTree();
    static void dumpCheckGlobalTree(const string& stagename, int newNumber=0, bool doDump=true);
    void assertDTypesResolved(bool flag) { m_assertDTypesResolved = flag; }
    void widthMinUsage(const VWidthMinUsage& flag) { m_widthMinUsage = flag; }
    bool constRemoveXs() const { return m_constRemoveXs; }
    void constRemoveXs(bool flag) { m_constRemoveXs = flag; }
    string debugFilename(const string& nameComment, int newNumber=0) {
        ++m_debugFileNumber;
        if (newNumber) m_debugFileNumber = newNumber;
        char digits[100]; sprintf(digits, "%03d", m_debugFileNumber);
        return opt.makeDir()+"/"+opt.prefix()+"_"+digits+"_"+nameComment;
    }
    bool needTraceDumper() const { return m_needTraceDumper; }
    void needTraceDumper(bool flag) { m_needTraceDumper = flag; }
    bool needHInlines() const { return m_needHInlines; }
    void needHInlines(bool flag) { m_needHInlines = flag; }
    bool needHeavy() const { return m_needHeavy; }
    void needHeavy(bool flag) { m_needHeavy = flag; }
    bool dpi() const { return m_dpi; }
    void dpi(bool flag) { m_dpi = flag; }
};

extern V3Global v3Global;

//######################################################################

#endif  // guard
