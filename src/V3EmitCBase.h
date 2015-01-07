// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2015 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#ifndef _V3EMITCBASE_H_
#define _V3EMITCBASE_H_ 1

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <cmath>

#include "V3Global.h"
#include "V3File.h"
#include "V3Ast.h"

//######################################################################
// Base Visitor class -- holds output file pointer

class EmitCBaseVisitor : public AstNVisitor {
public:
    // STATE
    V3OutCFile*	m_ofp;
    // METHODS
    V3OutCFile*	ofp() const { return m_ofp; }
    void puts(const string& str) { ofp()->puts(str); }
    void putbs(const string& str) { ofp()->putbs(str); }
    void putsQuoted(const string& str) { ofp()->putsQuoted(str); }
    bool optSystemC() { return v3Global.opt.systemC(); }
    bool optSystemPerl() { return v3Global.opt.systemPerl(); }
    static string symClassName() { return v3Global.opt.prefix()+"__Syms"; }
    static string symClassVar()  { return symClassName()+"* __restrict vlSymsp"; }
    static string symTopAssign() { return v3Global.opt.prefix()+"* __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;"; }
    static string modClassName(AstNodeModule* modp) {	// Return name of current module being processed
	if (modp->isTop()) {
	    return v3Global.opt.prefix();
	} else {
	    return v3Global.opt.modPrefix() + "_" + modp->name();
	}
    }
    static string topClassName() {		// Return name of top wrapper module
	return v3Global.opt.prefix();
    }
    AstCFile* newCFile(const string& filename, bool slow, bool source) {
	AstCFile* cfilep = new AstCFile(v3Global.rootp()->fileline(), filename);
	cfilep->slow(slow);
	cfilep->source(source);
	v3Global.rootp()->addFilesp(cfilep);
	return cfilep;
    }
    string cFuncArgs(AstCFunc* nodep) {
	// Return argument list for given C function
	string args = nodep->argTypes();
	// Might be a user function with argument list.
	for (AstNode* stmtp = nodep->argsp(); stmtp; stmtp=stmtp->nextp()) {
	    if (AstVar* portp = stmtp->castVar()) {
		if (portp->isIO() && !portp->isFuncReturn()) {
		    if (args != "") args+= ", ";
		    if (nodep->dpiImport() || nodep->dpiExportWrapper())
			args += portp->dpiArgType(true,false);
		    else if (nodep->funcPublic())
			args += portp->cPubArgType(true,false);
		    else args += portp->vlArgType(true,false,true);
		}
	    }
	}
	return args;
    }

    // CONSTRUCTORS
    EmitCBaseVisitor() {
	m_ofp = NULL;
    }
    virtual ~EmitCBaseVisitor() {}
};

//######################################################################
// Count operations under the given node, as a visitor of each AstNode

class EmitCBaseCounterVisitor : public AstNVisitor {
private:
    // STATE
    int			m_count;	// Number of statements
    // VISITORS
    virtual void visit(AstNode* nodep, AstNUser*) {
	m_count++;
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    EmitCBaseCounterVisitor(AstNode* nodep) {
	m_count = 0;
	nodep->accept(*this);
    }
    virtual ~EmitCBaseCounterVisitor() {}
    int count() const { return m_count; }
};

#endif // guard
