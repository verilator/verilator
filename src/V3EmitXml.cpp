// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit Verilog from tree
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2004-2025 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3EmitXml.h"

#include "V3EmitCBase.h"

#include <map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

// ######################################################################
//  Emit statements and expressions

class EmitXmlFileVisitor final : public VNVisitorConst {
    // NODE STATE
    // Entire netlist:
    // AstNode::user1           -> uint64_t, number to connect crossrefs
    const VNUser1InUse m_user1InUse;

    // MEMBERS
    V3OutFile* const m_ofp;
    uint64_t m_id = 0;

    // METHODS

    // Outfile methods
    V3OutFile* ofp() const { return m_ofp; }
    virtual void puts(const string& str) { ofp()->puts(str); }
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
        if (!nodep->user1()) nodep->user1(++m_id);
        puts("\"" + cvtToStr(nodep->user1()) + "\"");
    }
    void outputTag(AstNode* nodep, const string& tagin) {
        string tag = tagin;
        if (tag == "") tag = VString::downcase(nodep->typeName());
        puts("<" + tag);
        puts(" " + nodep->fileline()->xmlDetailedLocation());
        if (VN_IS(nodep, NodeDType)) {
            puts(" id=");
            outputId(nodep);
        }
        if (nodep->name() != "") {
            puts(" name=");
            putsQuoted(nodep->prettyName());
        }
        if (nodep->tag() != "") {
            puts(" tag=");
            putsQuoted(nodep->tag());
        }
        if (const AstNodeDType* const dtp = VN_CAST(nodep, NodeDType)) {
            if (dtp->subDTypep()) {
                puts(" sub_dtype_id=");
                outputId(dtp->subDTypep()->skipRefp());
            }
        } else {
            if (nodep->dtypep()) {
                puts(" dtype_id=");
                outputId(nodep->dtypep()->skipRefp());
            }
        }
    }
    void outputChildrenEnd(AstNode* nodep, const string& tagin) {
        string tag = tagin;
        if (tag == "") tag = VString::downcase(nodep->typeName());
        if (nodep->op1p() || nodep->op2p() || nodep->op3p() || nodep->op4p()) {
            puts(">\n");
            iterateChildrenConst(nodep);
            puts("</" + tag + ">\n");
        } else {
            puts("/>\n");
        }
    }

    // VISITORS
    void visit(AstAssignW* nodep) override {
        outputTag(nodep, "contassign");  // IEEE: vpiContAssign
        outputChildrenEnd(nodep, "contassign");
    }
    void visit(AstCell* nodep) override {
        outputTag(nodep, "instance");  // IEEE: vpiInstance
        puts(" defName=");
        putsQuoted(nodep->modName());  // IEEE vpiDefName
        puts(" origName=");
        putsQuoted(nodep->origName());
        outputChildrenEnd(nodep, "instance");
    }
    void visit(AstNodeIf* nodep) override {
        outputTag(nodep, "if");
        puts(">\n");
        iterateAndNextConstNull(nodep->condp());
        puts("<begin>\n");
        iterateAndNextConstNull(nodep->thensp());
        puts("</begin>\n");
        if (nodep->elsesp()) {
            puts("<begin>\n");
            iterateAndNextConstNull(nodep->elsesp());
            puts("</begin>\n");
        }
        puts("</if>\n");
    }
    void visit(AstWhile* nodep) override {
        outputTag(nodep, "while");
        puts(">\n");
        if (nodep->condp()) {
            puts("<begin>\n");
            iterateAndNextConstNull(nodep->condp());
            puts("</begin>\n");
        }
        if (nodep->stmtsp()) {
            puts("<begin>\n");
            iterateAndNextConstNull(nodep->stmtsp());
            puts("</begin>\n");
        }
        if (nodep->incsp()) {
            puts("<begin>\n");
            iterateAndNextConstNull(nodep->incsp());
            puts("</begin>\n");
        }
        puts("</while>\n");
    }
    void visit(AstNetlist* nodep) override {
        puts("<netlist>\n");
        iterateChildrenConst(nodep);
        puts("</netlist>\n");
    }
    void visit(AstConstPool* nodep) override {
        if (!v3Global.opt.xmlOnly()) {
            puts("<constpool>\n");
            iterateChildrenConst(nodep);
            puts("</constpool>\n");
        }
    }
    void visit(AstInitArray* nodep) override {
        puts("<initarray>\n");
        const auto& mapr = nodep->map();
        for (const auto& itr : mapr) {
            puts("<inititem index=\"");
            puts(cvtToStr(itr.first));
            puts("\">\n");
            iterateChildrenConst(itr.second);
            puts("</inititem>\n");
        }
        puts("</initarray>\n");
    }
    void visit(AstNodeModule* nodep) override {
        outputTag(nodep, "");
        puts(" origName=");
        putsQuoted(nodep->origName());
        if (nodep->level() == 1
            || nodep->level() == 2)  // ==2 because we don't add wrapper when in XML mode
            puts(" topModule=\"1\"");  // IEEE vpiTopModule
        if (nodep->modPublic()) puts(" public=\"true\"");
        outputChildrenEnd(nodep, "");
    }
    void visit(AstVar* nodep) override {
        const VVarType typ = nodep->varType();
        const string kw = nodep->verilogKwd();
        const string vt = nodep->dtypep() ? nodep->dtypep()->name() : "";
        outputTag(nodep, "");
        if (nodep->isIO()) {
            puts(" dir=");
            putsQuoted(kw);
            if (nodep->pinNum() != 0) puts(" pinIndex=\"" + cvtToStr(nodep->pinNum()) + "\"");
            puts(" vartype=");
            putsQuoted(!vt.empty() ? vt : typ == VVarType::PORT ? "port" : "unknown");
        } else {
            puts(" vartype=");
            putsQuoted(!vt.empty() ? vt : kw);
        }
        puts(" origName=");
        putsQuoted(nodep->origName());
        // Attributes
        if (nodep->attrClocker() == VVarAttrClocker::CLOCKER_YES) {
            puts(" clocker=\"true\"");
        } else if (nodep->attrClocker() == VVarAttrClocker::CLOCKER_NO) {
            puts(" clocker=\"false\"");
        }
        if (nodep->attrIsolateAssign()) puts(" isolate_assignments=\"true\"");
        if (nodep->isLatched()) puts(" latched=\"true\"");
        if (nodep->isSigPublic()) puts(" public=\"true\"");
        if (nodep->isSigUserRdPublic()) puts(" public_flat_rd=\"true\"");
        if (nodep->isSigUserRWPublic()) puts(" public_flat_rw=\"true\"");
        if (nodep->isGParam()) {
            puts(" param=\"true\"");
        } else if (nodep->isParam()) {
            puts(" localparam=\"true\"");
        }
        if (nodep->attrScBv()) puts(" sc_bv=\"true\"");
        if (nodep->attrSFormat()) puts(" sformat=\"true\"");
        outputChildrenEnd(nodep, "");
    }
    void visit(AstPin* nodep) override {
        // What we call a pin in verilator is a port in the IEEE spec.
        outputTag(nodep, "port");  // IEEE: vpiPort
        if (nodep->modVarp() && nodep->modVarp()->isIO()) {
            puts(" direction=\"" + nodep->modVarp()->direction().xmlKwd() + "\"");
        }
        puts(" portIndex=\"" + cvtToStr(nodep->pinNum()) + "\"");  // IEEE: vpiPortIndex
        // Children includes vpiHighConn and vpiLowConn; we don't support port bits (yet?)
        outputChildrenEnd(nodep, "port");
    }
    void visit(AstSenItem* nodep) override {
        outputTag(nodep, "");
        puts(" edgeType=\"" + cvtToStr(nodep->edgeType().ascii()) + "\"");  // IEEE vpiTopModule
        outputChildrenEnd(nodep, "");
    }
    void visit(AstModportVarRef* nodep) override {
        // Dump direction for Modport references
        const string kw = nodep->direction().xmlKwd();
        outputTag(nodep, "");
        puts(" direction=");
        putsQuoted(kw);
        outputChildrenEnd(nodep, "");
    }
    void visit(AstVarXRef* nodep) override {
        outputTag(nodep, "");
        puts(" dotted=");
        putsQuoted(nodep->dotted());
        outputChildrenEnd(nodep, "");
    }
    void visit(AstNodeCCall* nodep) override {
        outputTag(nodep, "");
        puts(" func=");
        putsQuoted(nodep->funcp() ? nodep->funcp()->name() : nodep->name());
        outputChildrenEnd(nodep, "");
    }
    void visit(AstSel* nodep) override {
        outputTag(nodep, "");
        puts(" widthConst=\"" + cvtToStr(nodep->widthConst()) + "\"");
        outputChildrenEnd(nodep, "");
    }

    // Data types
    void visit(AstBasicDType* nodep) override {
        outputTag(nodep, "basicdtype");
        if (nodep->isRanged()) {
            puts(" left=\"" + cvtToStr(nodep->left()) + "\"");
            puts(" right=\"" + cvtToStr(nodep->right()) + "\"");
        }
        if (nodep->isSigned()) puts(" signed=\"true\"");
        puts("/>\n");
    }
    void visit(AstIfaceRefDType* nodep) override {
        string mpn;
        outputTag(nodep, "");
        if (nodep->isModport()) mpn = nodep->modportName();
        puts(" modportname=");
        putsQuoted(mpn);
        outputChildrenEnd(nodep, "");
    }
    void visit(AstDisplay* nodep) override {
        outputTag(nodep, "");
        puts(" displaytype=");
        putsQuoted(nodep->verilogKwd());
        outputChildrenEnd(nodep, "");
    }
    void visit(AstElabDisplay* nodep) override {
        outputTag(nodep, "");
        puts(" displaytype=");
        putsQuoted(nodep->verilogKwd());
        outputChildrenEnd(nodep, "");
    }
    void visit(AstExtend* nodep) override {
        outputTag(nodep, "");
        puts(" width=");
        putsQuoted(cvtToStr(nodep->width()));
        puts(" widthminv=");
        putsQuoted(cvtToStr(nodep->lhsp()->widthMinV()));
        outputChildrenEnd(nodep, "");
    }
    void visit(AstExtendS* nodep) override {
        outputTag(nodep, "");
        puts(" width=");
        putsQuoted(cvtToStr(nodep->width()));
        puts(" widthminv=");
        putsQuoted(cvtToStr(nodep->lhsp()->widthMinV()));
        outputChildrenEnd(nodep, "");
    }

    // Default
    void visit(AstNode* nodep) override {
        outputTag(nodep, "");
        outputChildrenEnd(nodep, "");
    }

public:
    EmitXmlFileVisitor(AstNode* nodep, V3OutFile* ofp)
        : m_ofp{ofp} {
        iterateConst(nodep);
    }
    ~EmitXmlFileVisitor() override = default;
};

//######################################################################
// List of module files xml visitor

class ModuleFilesXmlVisitor final : public VNVisitorConst {
    // MEMBERS
    std::ostream& m_os;
    std::set<std::string> m_modulesCovered;
    std::deque<FileLine*> m_nodeModules;

    // METHODS

    // VISITORS
    void visit(AstNetlist* nodep) override {
        // Children are iterated backwards to ensure correct compilation order
        iterateChildrenBackwardsConst(nodep);
    }
    void visit(AstNodeModule* nodep) override {
        // Only list modules and interfaces
        // Assumes modules and interfaces list is already sorted level wise
        if (!nodep->dead() && (VN_IS(nodep, Module) || VN_IS(nodep, Iface))
            && m_modulesCovered.insert(nodep->fileline()->filename()).second) {
            m_nodeModules.push_front(nodep->fileline());
        }
    }
    //-----
    void visit(AstNode*) override {
        // All modules are present at root so no need to iterate on children
    }

public:
    // CONSTRUCTORS
    ModuleFilesXmlVisitor(AstNetlist* nodep, std::ostream& os)
        : m_os(os) {  // Need () or GCC 4.8 false warning
        // Operate on whole netlist
        iterateConst(nodep);
        // Xml output
        m_os << "<module_files>\n";
        for (const FileLine* ifp : m_nodeModules) {
            m_os << "<file id=\"" << ifp->filenameLetters() << "\" filename=\""
                 << ifp->filenameEsc() << "\" language=\"" << ifp->language().ascii() << "\"/>\n";
        }
        m_os << "</module_files>\n";
    }
    ~ModuleFilesXmlVisitor() override = default;
};

//######################################################################
// Hierarchy of Cells visitor

class HierCellsXmlVisitor final : public VNVisitorConst {
    // MEMBERS
    std::ostream& m_os;
    std::string m_hier;
    bool m_hasChildren = false;

    // METHODS

    // VISITORS
    void visit(AstConstPool*) override {}

    void visit(AstNodeModule* nodep) override {
        if (nodep->level() >= 0
            && nodep->level() <= 2) {  // ==2 because we don't add wrapper when in XML mode
            m_os << "<cells>\n";
            m_os << "<cell " << nodep->fileline()->xmlDetailedLocation()  //
                 << " name=\"" << nodep->prettyName() << "\""
                 << " submodname=\"" << nodep->prettyName() << "\""
                 << " hier=\"" << nodep->prettyName() << "\"";
            m_hier = nodep->prettyName() + ".";
            m_hasChildren = false;
            iterateChildrenConst(nodep);
            if (m_hasChildren) {
                m_os << "</cell>\n";
            } else {
                m_os << "/>\n";
            }
            m_os << "</cells>\n";
        }
    }
    void visit(AstCell* nodep) override {
        if (nodep->modp() && nodep->modp()->dead()) return;
        if (!m_hasChildren) m_os << ">\n";
        m_os << "<cell " << nodep->fileline()->xmlDetailedLocation() << " name=\"" << nodep->name()
             << "\""
             << " submodname=\"" << nodep->modName() << "\""
             << " hier=\"" << m_hier + nodep->name() << "\"";
        const std::string hier = m_hier;
        m_hier += nodep->name() + ".";
        m_hasChildren = false;
        iterateChildrenConst(nodep->modp());
        if (m_hasChildren) {
            m_os << "</cell>\n";
        } else {
            m_os << "/>\n";
        }
        m_hier = hier;
        m_hasChildren = true;
    }
    void visit(AstBegin* nodep) override {
        VL_RESTORER(m_hier);
        if (nodep->name() != "") m_hier += nodep->name() + ".";
        iterateChildrenConst(nodep);
    }
    //-----
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    // CONSTRUCTORS
    HierCellsXmlVisitor(AstNetlist* nodep, std::ostream& os)
        : m_os(os) {  // Need () or GCC 4.8 false warning
        iterateConst(nodep);
    }
    ~HierCellsXmlVisitor() override = default;
};

//######################################################################
// EmitXml class functions

void V3EmitXml::emitxml() {
    UINFO(2, __FUNCTION__ << ":");
    // All-in-one file
    const string filename = (v3Global.opt.xmlOutput().empty()
                                 ? v3Global.opt.makeDir() + "/" + v3Global.opt.prefix() + ".xml"
                                 : v3Global.opt.xmlOutput());
    V3OutXmlFile of{filename};
    of.putsHeader();
    of.puts("<!-- DESCR"
            "IPTION: Verilator output: XML representation of netlist -->\n");
    of.puts("<verilator_xml>\n");
    {
        std::stringstream sstr;
        FileLine::fileNameNumMapDumpXml(sstr);
        of.puts(sstr.str());
    }
    {
        std::stringstream sstr;
        const ModuleFilesXmlVisitor moduleFilesVisitor{v3Global.rootp(), sstr};
        const HierCellsXmlVisitor cellsVisitor{v3Global.rootp(), sstr};
        of.puts(sstr.str());
    }
    const EmitXmlFileVisitor visitor{v3Global.rootp(), &of};
    of.puts("</verilator_xml>\n");
}
