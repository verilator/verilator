// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit Verilog from tree
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2004-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3String.h"
#include "V3EmitXml.h"
#include "V3EmitCBase.h"

#include <algorithm>
#include <cmath>
#include <cstdarg>
#include <map>
#include <vector>

//######################################################################
// Emit statements and math operators

class EmitXmlFileVisitor : public AstNVisitor {
    // NODE STATE
    //Entire netlist:
    // AstNode::user1           -> uint64_t, number to connect crossrefs

    // MEMBERS
    V3OutFile*  m_ofp;
    uint64_t    m_id;

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // Outfile methods
    V3OutFile*  ofp() const { return m_ofp; }
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
        putsNoTracking(V3OutFormatter::quoteNameControls(str, V3OutFormatter::LA_XML));
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
        puts(" "+nodep->fileline()->xmlDetailedLocation());
        if (VN_IS(nodep, NodeDType)) { puts(" id="); outputId(nodep); }
        if (nodep->name()!="") { puts(" name="); putsQuoted(nodep->prettyName()); }
        if (nodep->tag()!="") { puts(" tag="); putsQuoted(nodep->tag()); }
        if (AstNodeDType* dtp = VN_CAST(nodep, NodeDType)) {
            if (dtp->subDTypep()) {
                puts(" sub_dtype_id="); outputId(dtp->subDTypep()->skipRefp());
            }
        } else {
            if (nodep->dtypep()) { puts(" dtype_id="); outputId(nodep->dtypep()->skipRefp()); }
        }
    }
    void outputChildrenEnd(AstNode* nodep, string tag) {
        if (tag=="") tag = VString::downcase(nodep->typeName());
        if (nodep->op1p() || nodep->op2p() || nodep->op3p() || nodep->op4p()) {
            puts(">\n");
            iterateChildren(nodep);
            puts("</"+tag+">\n");
        } else {
            puts("/>\n");
        }
    }

    // VISITORS
    virtual void visit(AstAssignW* nodep) VL_OVERRIDE {
        outputTag(nodep, "contassign");  // IEEE: vpiContAssign
        outputChildrenEnd(nodep, "contassign");
    }
    virtual void visit(AstCell* nodep) VL_OVERRIDE {
        outputTag(nodep, "instance");  // IEEE: vpiInstance
        puts(" defName="); putsQuoted(nodep->modName());  // IEEE vpiDefName
        puts(" origName="); putsQuoted(nodep->origName());
        outputChildrenEnd(nodep, "instance");
    }
    virtual void visit(AstNetlist* nodep) VL_OVERRIDE {
        puts("<netlist>\n");
        iterateChildren(nodep);
        puts("</netlist>\n");
    }
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        outputTag(nodep, "");
        puts(" origName="); putsQuoted(nodep->origName());
        if (nodep->level()==1 || nodep->level()==2)  // ==2 because we don't add wrapper when in XML mode
            puts(" topModule=\"1\"");  // IEEE vpiTopModule
        if (nodep->modPublic()) puts(" public=\"true\"");
        outputChildrenEnd(nodep, "");
    }
    virtual void visit(AstVar* nodep) VL_OVERRIDE {
        AstVarType typ = nodep->varType();
        string kw = nodep->verilogKwd();
        string vt = nodep->dtypep()->name();
        outputTag(nodep, "");
        if (nodep->isIO()) {
            puts(" dir="); putsQuoted(kw);
            puts(" vartype="); putsQuoted(!vt.empty()
                                          ? vt : typ == AstVarType::PORT ? "port" : "unknown");
        } else {
            puts(" vartype="); putsQuoted(!vt.empty() ? vt : kw);
        }
        puts(" origName="); putsQuoted(nodep->origName());
        // Attributes
        if (nodep->attrClocker() == VVarAttrClocker::CLOCKER_YES)
            puts(" clocker=\"true\"");
        else if (nodep->attrClocker() == VVarAttrClocker::CLOCKER_NO)
            puts(" clocker=\"false\"");
        if (nodep->attrClockEn()) puts(" clock_enable=\"true\"");
        if (nodep->attrIsolateAssign()) puts(" isolate_assignments=\"true\"");
        if (nodep->isSigPublic()) puts(" public=\"true\"");
        if (nodep->isSigUserRdPublic()) puts(" public_flat_rd=\"true\"");
        if (nodep->isSigUserRWPublic()) puts(" public_flat_rw=\"true\"");
        if (nodep->isGParam()) puts(" param=\"true\"");
        else if (nodep->isParam()) puts(" localparam=\"true\"");
        if (nodep->attrScBv()) puts(" sc_bv=\"true\"");
        if (nodep->attrScClocked()) puts(" sc_clock=\"true\"");
        if (nodep->attrSFormat()) puts(" sformat=\"true\"");
        outputChildrenEnd(nodep, "");
    }
    virtual void visit(AstPin* nodep) VL_OVERRIDE {
        // What we call a pin in verilator is a port in the IEEE spec.
        outputTag(nodep, "port");  // IEEE: vpiPort
        if (nodep->modVarp()->isIO()) {
            puts(" direction=\""+nodep->modVarp()->direction().xmlKwd()+"\"");
        }
        puts(" portIndex=\""+cvtToStr(nodep->pinNum())+"\"");  // IEEE: vpiPortIndex
        // Children includes vpiHighConn and vpiLowConn; we don't support port bits (yet?)
        outputChildrenEnd(nodep, "port");
    }
    virtual void visit(AstSenItem* nodep) VL_OVERRIDE {
        outputTag(nodep, "");
        puts(" edgeType=\""+cvtToStr(nodep->edgeType().ascii())+"\"");  // IEEE vpiTopModule
        outputChildrenEnd(nodep, "");
    }
    virtual void visit(AstModportVarRef* nodep) VL_OVERRIDE {
        // Dump direction for Modport references
        string kw = nodep->direction().xmlKwd();
        outputTag(nodep, "");
        puts(" direction="); putsQuoted(kw);
        outputChildrenEnd(nodep, "");
    }
    virtual void visit(AstVarXRef* nodep) VL_OVERRIDE {
        outputTag(nodep, "");
        puts(" dotted="); putsQuoted(nodep->dotted());
        outputChildrenEnd(nodep, "");
    }

    // Data types
    virtual void visit(AstBasicDType* nodep) VL_OVERRIDE {
        outputTag(nodep, "basicdtype");
        if (nodep->isRanged()) {
            puts(" left=\""+cvtToStr(nodep->left())+"\"");
            puts(" right=\""+cvtToStr(nodep->right())+"\"");
        }
        puts("/>\n");
    }
    virtual void visit(AstIfaceRefDType* nodep) VL_OVERRIDE {
        string mpn;
        outputTag(nodep, "");
        if (nodep->isModport()) mpn = nodep->modportName();
        puts(" modportname="); putsQuoted(mpn);
        outputChildrenEnd(nodep, "");
    }
    virtual void visit(AstDisplay* nodep) VL_OVERRIDE {
        outputTag(nodep, "");
        puts(" displaytype="); putsQuoted(nodep->verilogKwd());
        outputChildrenEnd(nodep, "");
    }
    virtual void visit(AstElabDisplay* nodep) VL_OVERRIDE {
        outputTag(nodep, "");
        puts(" displaytype="); putsQuoted(nodep->verilogKwd());
        outputChildrenEnd(nodep, "");
    }
    virtual void visit(AstExtend* nodep) VL_OVERRIDE {
        outputTag(nodep, "");
        puts(" width="); putsQuoted(cvtToStr(nodep->width()));
        puts(" widthminv="); putsQuoted(cvtToStr(nodep->lhsp()->widthMinV()));
        outputChildrenEnd(nodep, "");
    }
    virtual void visit(AstExtendS* nodep) VL_OVERRIDE {
        outputTag(nodep, "");
        puts(" width="); putsQuoted(cvtToStr(nodep->width()));
        puts(" widthminv="); putsQuoted(cvtToStr(nodep->lhsp()->widthMinV()));
        outputChildrenEnd(nodep, "");
    }

    // Default
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        outputTag(nodep, "");
        outputChildrenEnd(nodep, "");
    }
public:
    EmitXmlFileVisitor(AstNode* nodep, V3OutFile* ofp) {
        m_ofp = ofp;
        m_id = 0;
        iterate(nodep);
    }
    virtual ~EmitXmlFileVisitor() {}
};

//######################################################################
// List of module files xml visitor

class ModuleFilesXmlVisitor : public AstNVisitor {
private:
    // MEMBERS
    std::ostream& m_os;
    std::set<std::string> m_modulesCovered;
    std::deque<FileLine*> m_nodeModules;

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITORS
    virtual void visit(AstNetlist* nodep) VL_OVERRIDE {
        // Children are iterated backwards to ensure correct compilation order
        iterateChildrenBackwards(nodep);
    }
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        // Only list modules and interfaces
        // Assumes modules and interfaces list is already sorted level wise
        if (!nodep->dead()
            && (VN_IS(nodep, Module) || VN_IS(nodep, Iface))
            && m_modulesCovered.insert(nodep->fileline()->filename()).second) {
            m_nodeModules.push_front(nodep->fileline());
        }
    }
    //-----
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        // All modules are present at root so no need to iterate on children
    }

public:
    // CONSTRUCTORS
    ModuleFilesXmlVisitor(AstNetlist* nodep, std::ostream& os)
        : m_os(os), m_modulesCovered(), m_nodeModules() {
        // Operate on whole netlist
        nodep->accept(*this);
        // Xml output
        m_os<<"<module_files>\n";
        for (std::deque<FileLine*>::iterator it = m_nodeModules.begin();
                it != m_nodeModules.end(); ++it) {
            m_os<<"<file id=\""<<(*it)->filenameLetters()
                <<"\" filename=\""<<(*it)->filename()
                <<"\" language=\""<<(*it)->language().ascii()<<"\"/>\n";
        }
        m_os<<"</module_files>\n";
    }
    virtual ~ModuleFilesXmlVisitor() {}
};

//######################################################################
// Hierarchy of Cells visitor

class HierCellsXmlVisitor : public AstNVisitor {
private:
    // MEMBERS
    std::ostream& m_os;
    std::string m_hier;
    bool m_hasChildren;

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITORS
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        if (nodep->level() >= 0
            && nodep->level() <=2 ) {  // ==2 because we don't add wrapper when in XML mode
            m_os<<"<cells>\n";
            m_os<<"<cell "<<nodep->fileline()->xml()
                <<" "<<nodep->fileline()->xmlDetailedLocation()
                <<" name=\""<<nodep->name()<<"\""
                <<" submodname=\""<<nodep->name()<<"\""
                <<" hier=\""<<nodep->name()<<"\"";
            m_hier = nodep->name() + ".";
            m_hasChildren = false;
            iterateChildren(nodep);
            if (m_hasChildren) {
                m_os<<"</cell>\n";
            } else {
                m_os<<"/>\n";
            }
            m_os<<"</cells>\n";
        }
    }
    virtual void visit(AstCell* nodep) VL_OVERRIDE {
        if (nodep->modp()->dead()) {
            return;
        }
        if (!m_hasChildren) m_os<<">\n";
        m_os<<"<cell "<<nodep->fileline()->xml()
            <<" "<<nodep->fileline()->xmlDetailedLocation()
            <<" name=\""<<nodep->name()<<"\""
            <<" submodname=\""<<nodep->modName()<<"\""
            <<" hier=\""<<m_hier+nodep->name()<<"\"";
        std::string hier = m_hier;
        m_hier += nodep->name() + ".";
        m_hasChildren = false;
        iterateChildren(nodep->modp());
        if (m_hasChildren) {
            m_os<<"</cell>\n";
        } else {
            m_os<<"/>\n";
        }
        m_hier = hier;
        m_hasChildren = true;
    }
    //-----
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    HierCellsXmlVisitor(AstNetlist* nodep, std::ostream& os)
        : m_os(os), m_hier(""), m_hasChildren(false) {
        // Operate on whole netlist
        nodep->accept(*this);
    }
    virtual ~HierCellsXmlVisitor() {}
};

//######################################################################
// EmitXml class functions

void V3EmitXml::emitxml() {
    UINFO(2,__FUNCTION__<<": "<<endl);
    // All-in-one file
    string filename = (v3Global.opt.xmlOutput().empty()
                       ? v3Global.opt.makeDir()+"/"+v3Global.opt.prefix()+".xml"
                       : v3Global.opt.xmlOutput());
    V3OutXmlFile of(filename);
    of.putsHeader();
    of.puts("<!-- DESCR" "IPTION: Verilator output: XML representation of netlist -->\n");
    of.puts("<verilator_xml>\n");
    {
        std::stringstream sstr;
        FileLine::fileNameNumMapDumpXml(sstr);
        of.puts(sstr.str());
    }
    {
        std::stringstream sstr;
        ModuleFilesXmlVisitor moduleFilesVisitor (v3Global.rootp(), sstr);
        HierCellsXmlVisitor cellsVisitor (v3Global.rootp(), sstr);
        of.puts(sstr.str());
    }
    EmitXmlFileVisitor visitor (v3Global.rootp(), &of);
    of.puts("</verilator_xml>\n");
}
