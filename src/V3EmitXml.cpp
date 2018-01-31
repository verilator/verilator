// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit Verilog from tree
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2004-2018 by Wilson Snyder.  This program is free software; you can
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

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <cmath>
#include <map>
#include <vector>
#include <algorithm>

#include "V3Global.h"
#include "V3String.h"
#include "V3EmitXml.h"
#include "V3EmitCBase.h"

//######################################################################
// Emit statements and math operators

class EmitXmlFileVisitor : public AstNVisitor {
    // NODE STATE
    //Entire netlist:
    // AstNode::user1           -> uint64_t, number to connect crossrefs

    // MEMBERS
    V3OutFile*	m_ofp;
    uint64_t	m_id;

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    // Outfile methods
    V3OutFile*	ofp() const { return m_ofp; }
    virtual void puts(const string& str) { ofp()->puts(str); }
    virtual void putbs(const string& str) { ofp()->putbs(str); }
    virtual void putfs(AstNode*, const string& str) { putbs(str); }
    virtual void putqs(AstNode*, const string& str) { putbs(str); }
    virtual void putsNoTracking(const string& str) { ofp()->putsNoTracking(str); }
    virtual void putsQuoted(const string& str) {
	// Quote \ and " for use inside C programs
	// Don't use to quote a filename for #include - #include doesn't \ escape.
	// Duplicate in V3File - here so we can print to string
	putsNoTracking("\"");
	putsNoTracking(V3Number::quoteNameControls(str));
	putsNoTracking("\"");
    }

    // XML methods
    void outputId(AstNode* nodep) {
	if (!nodep->user1()) { nodep->user1(++m_id); }
	puts("\""+cvtToStr(nodep->user1())+"\"");
    }
    void outputTag(AstNode* nodep, string tag) {
	if (tag=="") tag = VString::downcase(nodep->typeName());
	puts("<"+tag+" "+nodep->fileline()->xml());
	if (nodep->castNodeDType()) { puts(" id="); outputId(nodep); }
	if (nodep->name()!="") { puts(" name="); putsQuoted(nodep->prettyName()); }
	if (nodep->tag()!="") { puts(" tag="); putsQuoted(nodep->tag()); }
	if (AstNodeDType* dtp = nodep->castNodeDType()) {
	    if (dtp->subDTypep()) { puts(" sub_dtype_id="); outputId(dtp->subDTypep()->skipRefp()); }
	} else {
	    if (nodep->dtypep()) { puts(" dtype_id="); outputId(nodep->dtypep()->skipRefp()); }
	}
    }
    void outputChildrenEnd(AstNode* nodep, string tag) {
	if (tag=="") tag = VString::downcase(nodep->typeName());
	if (nodep->op1p() || nodep->op2p() || nodep->op3p() || nodep->op4p()) {
	    puts(">\n");
	    nodep->iterateChildren(*this);
	    puts("</"+tag+">\n");
	} else {
	    puts("/>\n");
	}
    }

    // VISITORS
    virtual void visit(AstAssignW* nodep) {
        outputTag(nodep, "contassign"); // IEEE: vpiContAssign
        outputChildrenEnd(nodep, "contassign");
    }
    virtual void visit(AstCell* nodep) {
        outputTag(nodep, "instance");   // IEEE: vpiInstance
        puts(" defName="); putsQuoted(nodep->modName());  // IEEE vpiDefName
        outputChildrenEnd(nodep, "instance");
    }
    virtual void visit(AstNetlist* nodep) {
	puts("<netlist>\n");
	nodep->iterateChildren(*this);
	puts("</netlist>\n");
    }
    virtual void visit(AstNodeModule* nodep) {
	outputTag(nodep, "");
	if (nodep->level()==1 || nodep->level()==2) // ==2 because we don't add wrapper when in XML mode
	    puts(" topModule=\"1\"");  // IEEE vpiTopModule
	outputChildrenEnd(nodep, "");
    }
    virtual void visit(AstPin* nodep) {
	// What we call a pin in verilator is a port in the IEEE spec.
	outputTag(nodep, "port");	// IEEE: vpiPort
	if (nodep->modVarp()->isInOnly())
	    puts(" direction=\"in\"");
	else if (nodep->modVarp()->isOutOnly())
	    puts(" direction=\"out\"");
	else puts(" direction=\"inout\"");
	puts(" portIndex=\""+cvtToStr(nodep->pinNum())+"\""); // IEEE: vpiPortIndex
	// Children includes vpiHighConn and vpiLowConn; we don't support port bits (yet?)
	outputChildrenEnd(nodep, "port");
    }
    virtual void visit(AstSenItem* nodep) {
        outputTag(nodep, "");
        puts(" edgeType=\""+cvtToStr(nodep->edgeType().ascii())+"\"");  // IEEE vpiTopModule
        outputChildrenEnd(nodep, "");
    }

    // Data types
    virtual void visit(AstBasicDType* nodep) {
	outputTag(nodep, "basicdtype ");
	if (nodep->isRanged()) {
	    puts(" left=\""+cvtToStr(nodep->left())+"\"");
	    puts(" right=\""+cvtToStr(nodep->right())+"\"");
	}
	puts("/>\n");
    }

    // Default
    virtual void visit(AstNode* nodep) {
	outputTag(nodep, "");
	outputChildrenEnd(nodep, "");
    }
public:
    EmitXmlFileVisitor(AstNode* nodep, V3OutFile* ofp) {
	m_ofp = ofp;
	m_id = 0;
	nodep->accept(*this);
    }
    virtual ~EmitXmlFileVisitor() {}
};

//######################################################################
// EmitXml class functions

void V3EmitXml::emitxml() {
    UINFO(2,__FUNCTION__<<": "<<endl);
    // All-in-one file
    V3OutXmlFile of (v3Global.opt.makeDir()+"/"+v3Global.opt.prefix()+".xml");
    of.putsHeader();
    of.puts("<!-- DESCR" "IPTION: Verilator output: XML representation of netlist -->\n");
    of.puts("<verilator_xml>\n");
    {
	std::stringstream sstr;
	FileLine::fileNameNumMapDumpXml(sstr);
	of.puts(sstr.str());
    }
    EmitXmlFileVisitor visitor (v3Global.rootp(), &of);
    of.puts("</verilator_xml>\n");
}
