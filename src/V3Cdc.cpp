// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Clock Domain Crossing Lint
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
// V3Cdc's Transformations:
//
// Create V3Graph-ish graph
// Find all negedge reset flops
// Trace back to previous flop
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Cdc.h"
#include "V3Ast.h"
#include "V3Graph.h"
#include "V3Const.h"
#include "V3EmitV.h"
#include "V3File.h"

#include <algorithm>
#include <cstdarg>
#include <deque>
#include <iomanip>
#include <list>
#include <memory>
#include <vector>

#define CDC_WEIGHT_ASYNC        0x1000  // Weight for edges that feed async logic

//######################################################################

class CdcBaseVisitor : public AstNVisitor {
public:
    VL_DEBUG_FUNC;  // Declare debug()
};

//######################################################################
// Graph support classes

class CdcEitherVertex : public V3GraphVertex {
    AstScope*   m_scopep;
    AstNode*    m_nodep;
    AstSenTree* m_srcDomainp;
    AstSenTree* m_dstDomainp;
    bool        m_srcDomainSet:1;
    bool        m_dstDomainSet:1;
    bool        m_asyncPath:1;
public:
    CdcEitherVertex(V3Graph* graphp, AstScope* scopep, AstNode* nodep)
        : V3GraphVertex(graphp), m_scopep(scopep), m_nodep(nodep)
        , m_srcDomainp(NULL), m_dstDomainp(NULL)
        , m_srcDomainSet(false), m_dstDomainSet(false)
        , m_asyncPath(false) {}
    virtual ~CdcEitherVertex() {}
    // ACCESSORS
    virtual FileLine* fileline() const { return nodep()->fileline(); }
    AstScope* scopep() const { return m_scopep; }
    AstNode* nodep() const { return m_nodep; }
    AstSenTree* srcDomainp() const { return m_srcDomainp; }
    void srcDomainp(AstSenTree* nodep) { m_srcDomainp = nodep; }
    bool srcDomainSet() const { return m_srcDomainSet; }
    void srcDomainSet(bool flag) { m_srcDomainSet = flag; }
    AstSenTree* dstDomainp() const { return m_dstDomainp; }
    void dstDomainp(AstSenTree* nodep) { m_dstDomainp = nodep; }
    bool dstDomainSet() const { return m_dstDomainSet; }
    void dstDomainSet(bool flag) { m_dstDomainSet = flag; }
    bool asyncPath() const { return m_asyncPath; }
    void asyncPath(bool flag) { m_asyncPath = flag; }
};

class CdcVarVertex : public CdcEitherVertex {
    AstVarScope* m_varScp;
    int         m_cntAsyncRst;
    bool        m_fromFlop;
public:
    CdcVarVertex(V3Graph* graphp, AstScope* scopep, AstVarScope* varScp)
        : CdcEitherVertex(graphp, scopep, varScp)
        , m_varScp(varScp), m_cntAsyncRst(0), m_fromFlop(false) {}
    virtual ~CdcVarVertex() {}
    // ACCESSORS
    AstVarScope* varScp() const { return m_varScp; }
    virtual string name() const { return (cvtToHex(m_varScp)+" "+varScp()->name()); }
    virtual string dotColor() const {
        return fromFlop() ? "green" : cntAsyncRst() ? "red" : "blue"; }
    int cntAsyncRst() const { return m_cntAsyncRst; }
    void cntAsyncRst(int flag) { m_cntAsyncRst = flag; }
    bool fromFlop() const { return m_fromFlop; }
    void fromFlop(bool flag) { m_fromFlop = flag; }
};

class CdcLogicVertex : public CdcEitherVertex {
    bool        m_hazard:1;
    bool        m_isFlop:1;
public:
    CdcLogicVertex(V3Graph* graphp, AstScope* scopep, AstNode* nodep, AstSenTree* sensenodep)
        : CdcEitherVertex(graphp, scopep, nodep)
        , m_hazard(false), m_isFlop(false)
        { srcDomainp(sensenodep); dstDomainp(sensenodep); }
    virtual ~CdcLogicVertex() {}
    // ACCESSORS
    virtual string name() const { return (cvtToHex(nodep())+"@"+scopep()->prettyName()); }
    virtual string dotColor() const { return hazard() ? "black" : "yellow"; }
    bool hazard() const { return m_hazard; }
    void setHazard(AstNode* nodep) { m_hazard = true; nodep->user3(true); }
    void clearHazard() { m_hazard = false; }
    bool isFlop() const { return m_isFlop; }
    void isFlop(bool flag) { m_isFlop = flag; }
};

//######################################################################

class CdcDumpVisitor : public CdcBaseVisitor {
private:
    // NODE STATE
    //Entire netlist:
    // {statement}Node::user3   -> bool, indicating not hazard
    std::ofstream* m_ofp;  // Output file
    string              m_prefix;

    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        *m_ofp<<m_prefix;
        if (nodep->user3()) *m_ofp<<" %%";
        else *m_ofp<<"  ";
        *m_ofp<<nodep->prettyTypeName()<<" "<<endl;
        string lastPrefix = m_prefix;
        m_prefix = lastPrefix + "1:";
        iterateAndNextNull(nodep->op1p());
        m_prefix = lastPrefix + "2:";
        iterateAndNextNull(nodep->op2p());
        m_prefix = lastPrefix + "3:";
        iterateAndNextNull(nodep->op3p());
        m_prefix = lastPrefix + "4:";
        iterateAndNextNull(nodep->op4p());
        m_prefix = lastPrefix;
    }

public:
    // CONSTRUCTORS
    CdcDumpVisitor(AstNode* nodep, std::ofstream* ofp, const string& prefix) {
        m_ofp = ofp;
        m_prefix = prefix;
        iterate(nodep);
    }
    virtual ~CdcDumpVisitor() {}
};

//######################################################################

class CdcWidthVisitor : public CdcBaseVisitor {
private:
    int         m_maxLineno;
    size_t      m_maxFilenameLen;

    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        // Keeping line+filename lengths separate is much faster than calling ascii().length()
        if (nodep->fileline()->lineno() >= m_maxLineno) {
            m_maxLineno = nodep->fileline()->lineno()+1;
        }
        if (nodep->fileline()->filename().length() >= m_maxFilenameLen) {
            m_maxFilenameLen = nodep->fileline()->filename().length()+1;
        }
    }
public:
    // CONSTRUCTORS
    explicit CdcWidthVisitor(AstNode* nodep) {
        m_maxLineno = 0;
        m_maxFilenameLen = 0;
        iterate(nodep);
    }
    virtual ~CdcWidthVisitor() {}
    // ACCESSORS
    int maxWidth() {
        size_t width = 1;
        width += m_maxFilenameLen;
        width += 1;  // The :
        width += cvtToStr(m_maxLineno).length();
        width += 1;  // Final :
        return static_cast<int>(width);
    }
};

//######################################################################
// Cdc class functions

class CdcVisitor : public CdcBaseVisitor {
private:
    // NODE STATE
    //Entire netlist:
    // AstVarScope::user1p      -> CdcVarVertex* for usage var, 0=not set yet
    // AstVarScope::user2       -> bool  Used in sensitivity list
    // {statement}Node::user1p  -> CdcLogicVertex* for this statement
    // AstNode::user3           -> bool  True indicates to print %% (via V3EmitV)
    AstUser1InUse       m_inuser1;
    AstUser2InUse       m_inuser2;
    AstUser3InUse       m_inuser3;

    // STATE
    V3Graph             m_graph;        // Scoreboard of var usages/dependencies
    CdcLogicVertex*     m_logicVertexp; // Current statement being tracked, NULL=ignored
    AstScope*           m_scopep;       // Current scope being processed
    AstNodeModule*      m_modp;         // Current module
    AstSenTree*         m_domainp;      // Current sentree
    bool                m_inDly;        // In delayed assign
    int                 m_inSenItem;    // Number of senitems
    string              m_ofFilename;   // Output filename
    std::ofstream*      m_ofp;          // Output file
    uint32_t            m_userGeneration;  // Generation count to avoid slow userClearVertices
    int                 m_filelineWidth;   // Characters in longest fileline

    // METHODS
    void iterateNewStmt(AstNode* nodep) {
        if (m_scopep) {
            UINFO(4,"   STMT "<<nodep<<endl);
            m_logicVertexp = new CdcLogicVertex(&m_graph, m_scopep, nodep, m_domainp);
            if (m_domainp && m_domainp->hasClocked()) {  // To/from a flop
                m_logicVertexp->isFlop(true);
                m_logicVertexp->srcDomainp(m_domainp);
                m_logicVertexp->srcDomainSet(true);
                m_logicVertexp->dstDomainp(m_domainp);
                m_logicVertexp->dstDomainSet(true);
            }
            iterateChildren(nodep);
            m_logicVertexp = NULL;

            if (0 && debug()>=9) {
                UINFO(9, "Trace Logic:\n");
                nodep->dumpTree(cout, "-log1: ");
            }
        }
    }

    CdcVarVertex* makeVarVertex(AstVarScope* varscp) {
        CdcVarVertex* vertexp = reinterpret_cast<CdcVarVertex*>(varscp->user1p());
        if (!vertexp) {
            UINFO(6,"New vertex "<<varscp<<endl);
            vertexp = new CdcVarVertex(&m_graph, m_scopep, varscp);
            varscp->user1p(vertexp);
            if (varscp->varp()->isUsedClock()) {}
            if (varscp->varp()->isPrimaryIO()) {
                // Create IO vertex - note it's relative to the pointed to var, not where we are now
                // This allows reporting to easily print the input statement
                CdcLogicVertex* ioVertexp = new CdcLogicVertex(&m_graph, varscp->scopep(),
                                                               varscp->varp(), NULL);
                if (varscp->varp()->isWritable()) {
                    new V3GraphEdge(&m_graph, vertexp, ioVertexp, 1);
                } else {
                    new V3GraphEdge(&m_graph, ioVertexp, vertexp, 1);
                }
            }
        }
        if (m_inSenItem) {
            varscp->user2(true);  // It's like a clock...
            // TODO: In the future we could mark it here and do normal clock tree glitch checks also
        } else if (varscp->user2()) {  // It was detected in a sensitivity list earlier
            // And now it's used as logic.  So must be a reset.
            vertexp->cntAsyncRst(vertexp->cntAsyncRst()+1);
        }
        return vertexp;
    }

    void warnAndFile(AstNode* nodep, V3ErrorCode code, const string& msg) {
        static bool told_file = false;
        nodep->v3warnCode(code, msg);
        if (!told_file) {
            told_file = 1;
            std::cerr<<V3Error::msgPrefix()<<"     See details in "<<m_ofFilename<<endl;
        }
        *m_ofp<<"%Warning-"<<code.ascii()<<": "<<nodep->fileline()<<" "<<msg<<endl;
    }

    void setNodeHazard(AstNode* nodep) {
        // Need to not clear if warnings are off (rather than when report it)
        // as bypassing this warning may turn up another path that isn't warning off'ed.
        // We can't modifyWarnOff here, as one instantiation might not be
        // an issue until we find a hitting flop.
        // Furthermore, a module like a "Or" module would only get flagged
        // once, even though the signals feeding it are radically different.
        if (!m_domainp || m_domainp->hasCombo()) {  // Source flop logic in a posedge block is OK for reset (not async though)
            if (m_logicVertexp && !nodep->fileline()->warnIsOff(V3ErrorCode::CDCRSTLOGIC)) {
                UINFO(8,"Set hazard "<<nodep<<endl);
                m_logicVertexp->setHazard(nodep);
            }
        }
    }

    string spaces(int level) { string out; while (level--) out += " "; return out; }  // LCOV_EXCL_LINE

    string pad(unsigned column, const string& in) {
        string out = in;
        while (out.length()<column) out += ' ';
        return out;
    }

    void analyze() {
        UINFO(3,__FUNCTION__<<": "<<endl);
        //if (debug()>6) m_graph.dump();
        if (debug()>6) m_graph.dumpDotFilePrefixed("cdc_pre");
        //
        m_graph.removeRedundantEdges(&V3GraphEdge::followAlwaysTrue);  // This will MAX across edge weights
        //
        m_graph.dumpDotFilePrefixed("cdc_simp");
        //
        analyzeReset();
    }

    int filelineWidth() {
        if (!m_filelineWidth) {
            CdcWidthVisitor visitor (v3Global.rootp());
            m_filelineWidth = visitor.maxWidth();
        }
        return m_filelineWidth;
    }

    //----------------------------------------
    // RESET REPORT

    void analyzeReset() {
        // Find all async reset wires, and trace backwards
        // userClearVertices is very slow, so we use a generation count instead
        m_graph.userClearVertices();  // user1: uint32_t - was analyzed generation
        for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp=itp->verticesNextp()) {
            if (CdcVarVertex* vvertexp = dynamic_cast<CdcVarVertex*>(itp)) {
                if (vvertexp->cntAsyncRst()) {
                    m_userGeneration++;  // Effectively a userClearVertices()
                    UINFO(8, "   Trace One async: "<<vvertexp<<endl);
                    // Twice, as we need to detect, then propagate
                    CdcEitherVertex* markp = traceAsyncRecurse(vvertexp, false);
                    if (markp) {  // Mark is non-NULL if something bad on this path
                        UINFO(9, "   Trace One bad! "<<vvertexp<<endl);
                        m_userGeneration++;  // Effectively a userClearVertices()
                        traceAsyncRecurse(vvertexp, true);
                        m_userGeneration++;  // Effectively a userClearVertices()
                        dumpAsync(vvertexp, markp);
                    }
                }
            }
        }
    }

    CdcEitherVertex* traceAsyncRecurse(CdcEitherVertex* vertexp, bool mark) {
        // First pass: Return vertex of any hazardous stuff attached, or NULL if OK
        // If first pass returns true, second pass calls asyncPath() on appropriate nodes
        if (vertexp->user()>=m_userGeneration) return NULL;  // Processed - prevent loop
        vertexp->user(m_userGeneration);

        CdcEitherVertex* mark_outp = NULL;
        UINFO(9,"      Trace: "<<vertexp<<endl);

        // Clear out in prep for marking next path
        if (!mark) vertexp->asyncPath(false);

        if (CdcLogicVertex* vvertexp = dynamic_cast<CdcLogicVertex*>(vertexp)) {
            // Any logic considered bad, at the moment, anyhow
            if (vvertexp->hazard() && !mark_outp) mark_outp = vvertexp;
            // And keep tracing back so the user can understand what's up
        }
        else if (CdcVarVertex* vvertexp = dynamic_cast<CdcVarVertex*>(vertexp)) {
            if (mark) vvertexp->asyncPath(true);
            // If primary I/O, it's ok here back
            if (vvertexp->varScp()->varp()->isPrimaryInish()) {
                // Show the source "input" statement if it exists
                for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep; edgep = edgep->inNextp()) {
                    CdcEitherVertex* eFromVertexp = static_cast<CdcEitherVertex*>(edgep->fromp());
                    eFromVertexp->asyncPath(true);
                }
                return NULL;
            }
            // Also ok if from flop, but partially trace the flop so more obvious to users
            if (vvertexp->fromFlop()) {
                for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep; edgep = edgep->inNextp()) {
                    CdcEitherVertex* eFromVertexp = static_cast<CdcEitherVertex*>(edgep->fromp());
                    eFromVertexp->asyncPath(true);
                }
                return NULL;
            }
        }

        for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep; edgep = edgep->inNextp()) {
            CdcEitherVertex* eFromVertexp = static_cast<CdcEitherVertex*>(edgep->fromp());
            CdcEitherVertex* submarkp = traceAsyncRecurse(eFromVertexp, mark);
            if (submarkp && !mark_outp) mark_outp = submarkp;
        }

        if (mark) vertexp->asyncPath(true);
        return mark_outp;
    }

    void dumpAsync(CdcVarVertex* vertexp, CdcEitherVertex* markp) {
        AstNode* nodep = vertexp->varScp();
        *m_ofp<<"\n";
        *m_ofp<<"\n";
        CdcEitherVertex* targetp = vertexp;  // One example destination flop (of possibly many)
        for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep = edgep->outNextp()) {
            CdcEitherVertex* eToVertexp = static_cast<CdcEitherVertex*>(edgep->top());
            if (!eToVertexp) targetp = eToVertexp;
            if (CdcLogicVertex* vvertexp = dynamic_cast<CdcLogicVertex*>(eToVertexp)) {
                if (vvertexp->isFlop()  // IE the target flop that is upsetting us
                    && edgep->weight() >= CDC_WEIGHT_ASYNC) {  // And this signal feeds an async reset line
                    targetp = eToVertexp;
                    //UINFO(9," targetasync  "<<targetp->name()<<" "<<" from "<<vertexp->name()<<endl);
                    break;
                }
            }  // else it might be random logic that's not relevant
        }
        //UINFO(9," finalflop  "<<targetp->name()<<" "<<targetp->nodep()->fileline()<<endl);
        warnAndFile(markp->nodep(), V3ErrorCode::CDCRSTLOGIC,
                    "Logic in path that feeds async reset, via signal: "+nodep->prettyNameQ());
        dumpAsyncRecurse(targetp, "", "   ", 0);
    }
    bool dumpAsyncRecurse(CdcEitherVertex* vertexp, const string& prefix,
                          const string& sep, int level) {
        // level=0 is special, indicates to dump destination flop
        // Return true if printed anything
        // If mark, also mark the output even if nothing hazardous below
        if (vertexp->user()>=m_userGeneration) return false;  // Processed - prevent loop
        vertexp->user(m_userGeneration);
        if (!vertexp->asyncPath() && level!=0) return false;  // Not part of path

        // Other logic in the path
        string cont = prefix+sep;
        string nextsep = "   ";
        for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep; edgep = edgep->inNextp()) {
            CdcEitherVertex* eFromVertexp = static_cast<CdcEitherVertex*>(edgep->fromp());
            if (dumpAsyncRecurse(eFromVertexp, cont, nextsep, level+1)) {
                nextsep = " | ";
            }
        }

        // Dump single variable/logic block
        // See also OrderGraph::loopsVertexCb(V3GraphVertex* vertexp)
        AstNode* nodep = vertexp->nodep();
        string front = pad(filelineWidth(), nodep->fileline()->ascii()+":")+" "+prefix+" +- ";
        if (VN_IS(nodep, VarScope)) {
            *m_ofp<<front<<"Variable: "<<nodep->prettyName()<<endl;
        }
        else {
            V3EmitV::verilogPrefixedTree(nodep, *m_ofp, prefix+" +- ", filelineWidth(),
                                         vertexp->srcDomainp(), true);
            if (debug()) {
                CdcDumpVisitor visitor (nodep, m_ofp, front+"DBG: ");
            }
        }

        nextsep = " | ";
        if (level) *m_ofp<<V3OutFile::indentSpaces(filelineWidth())<<" "<<prefix<<nextsep<<"\n";

        if (CdcLogicVertex* vvertexp = dynamic_cast<CdcLogicVertex*>(vertexp)) {
            // Now that we've printed a path with this hazard, don't bother to print any more
            // Otherwise, we'd get a path for almost every destination flop
            vvertexp->clearHazard();
        }
        return true;
    }

    //----------------------------------------
    // EDGE REPORTS

    void edgeReport() {
        // Make report of all signal names and what clock edges they have
        //
        // Due to flattening, many interesting direct-connect signals are
        // lost, so we can't make a report showing I/Os for a low level
        // module.  Disabling flattening though makes us consider each
        // signal in it's own unique clock domain.

        UINFO(3,__FUNCTION__<<": "<<endl);

        // Trace all sources and sinks
        for (int traceDests=0; traceDests<2; ++traceDests) {
            UINFO(9, " Trace Direction "<<(traceDests?"dst":"src")<<endl);
            m_graph.userClearVertices();  // user1: bool - was analyzed
            for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp=itp->verticesNextp()) {
                if (CdcVarVertex* vvertexp = dynamic_cast<CdcVarVertex*>(itp)) {
                    UINFO(9, "   Trace One edge: "<<vvertexp<<endl);
                    edgeDomainRecurse(vvertexp, traceDests, 0);
                }
            }
        }

        string filename = v3Global.opt.makeDir()+"/"+v3Global.opt.prefix()+"__cdc_edges.txt";
        const vl_unique_ptr<std::ofstream> ofp (V3File::new_ofstream(filename));
        if (ofp->fail()) v3fatal("Can't write "<<filename);
        *ofp<<"Edge Report for "<<v3Global.opt.prefix()<<endl;

        std::deque<string> report;  // Sort output by name
        for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp=itp->verticesNextp()) {
            if (CdcVarVertex* vvertexp = dynamic_cast<CdcVarVertex*>(itp)) {
                AstVar* varp = vvertexp->varScp()->varp();
                if (1) {  // varp->isPrimaryIO()
                    string what = "wire";
                    if (varp->isPrimaryIO()) what = varp->direction().prettyName();

                    std::ostringstream os;
                    os.setf(std::ios::left);
                    // Module name - doesn't work due to flattening having lost the original
                    // so we assume the modulename matches the filebasename
                    string fname = vvertexp->varScp()->fileline()->filebasename() + ":";
                    os<<"  "<<std::setw(20)<<fname;
                    os<<"  "<<std::setw(8)<<what;
                    os<<"  "<<std::setw(40)<<vvertexp->varScp()->prettyName();
                    os<<"  SRC=";
                    if (vvertexp->srcDomainp()) V3EmitV::verilogForTree(vvertexp->srcDomainp(), os);
                    os<<"  DST=";
                    if (vvertexp->dstDomainp()) V3EmitV::verilogForTree(vvertexp->dstDomainp(), os);
                    os<<std::setw(0);
                    os<<endl;
                    report.push_back(os.str());
                }
            }
        }
        stable_sort(report.begin(), report.end());
        for (std::deque<string>::iterator it = report.begin(); it!=report.end(); ++it) {
            *ofp << *it;
        }
    }

    void edgeDomainRecurse(CdcEitherVertex* vertexp, bool traceDests, int level) {
        // Scan back to inputs/outputs, flops, and compute clock domain information
        UINFO(8,spaces(level)<<"     Tracein  "<<vertexp<<endl);
        if (vertexp->user()>=m_userGeneration) return;  // Mid-Processed - prevent loop
        vertexp->user(m_userGeneration);

        // Variables from flops already are domained
        if (traceDests ? vertexp->dstDomainSet() : vertexp->srcDomainSet()) return;  // Fully computed

        typedef std::set<AstSenTree*> SenSet;
        SenSet senouts;  // List of all sensitivities for new signal
        if (CdcLogicVertex* vvertexp = dynamic_cast<CdcLogicVertex*>(vertexp)) {
            if (vvertexp) {}  // Unused
        }
        else if (CdcVarVertex* vvertexp = dynamic_cast<CdcVarVertex*>(vertexp)) {
            // If primary I/O, give it domain of the input
            AstVar* varp = vvertexp->varScp()->varp();
            if (varp->isPrimaryIO() && varp->isNonOutput() && !traceDests) {
                senouts.insert(
                    new AstSenTree(varp->fileline(),
                                   new AstSenItem(varp->fileline(), AstSenItem::Combo())));
            }
        }

        // Now combine domains of sources/dests
        if (traceDests) {
            for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep = edgep->outNextp()) {
                CdcEitherVertex* eToVertexp = static_cast<CdcEitherVertex*>(edgep->top());
                edgeDomainRecurse(eToVertexp, traceDests, level+1);
                if (eToVertexp->dstDomainp()) senouts.insert(eToVertexp->dstDomainp());
            }
        } else {
            for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep; edgep = edgep->inNextp()) {
                CdcEitherVertex* eFromVertexp = static_cast<CdcEitherVertex*>(edgep->fromp());
                edgeDomainRecurse(eFromVertexp, traceDests, level+1);
                if (eFromVertexp->srcDomainp()) senouts.insert(eFromVertexp->srcDomainp());
            }
        }

        // Convert list of senses into one sense node
        AstSenTree* senoutp = NULL;
        bool        senedited = false;
        for (SenSet::iterator it=senouts.begin(); it!=senouts.end(); ++it) {
            if (!senoutp) senoutp = *it;
            else {
                if (!senedited) {
                    senedited = true;
                    senoutp = senoutp->cloneTree(true);
                }
                senoutp->addSensesp((*it)->sensesp()->cloneTree(true));
            }
        }
        // If multiple domains need to do complicated optimizations
        if (senedited) {
            senoutp = VN_CAST(V3Const::constifyExpensiveEdit(senoutp), SenTree);
        }
        if (traceDests) {
            vertexp->dstDomainSet(true);  // Note it's set - domainp may be null, so can't use that
            vertexp->dstDomainp(senoutp);
            if (debug()>=9) {
                UINFO(9,spaces(level)+"     Tracedst "<<vertexp);
                if (senoutp) { V3EmitV::verilogForTree(senoutp, cout); cout<<endl; }
            }
        } else {
            vertexp->srcDomainSet(true);  // Note it's set - domainp may be null, so can't use that
            vertexp->srcDomainp(senoutp);
            if (debug()>=9) {
                UINFO(9,spaces(level)+"     Tracesrc "<<vertexp);
                if (senoutp) { V3EmitV::verilogForTree(senoutp, cout); cout<<endl; }
            }
        }
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        AstNodeModule* origModp = m_modp;
        {
            m_modp = nodep;
            iterateChildren(nodep);
        }
        m_modp = origModp;
    }
    virtual void visit(AstScope* nodep) VL_OVERRIDE {
        UINFO(4," SCOPE "<<nodep<<endl);
        m_scopep = nodep;
        m_logicVertexp = NULL;
        iterateChildren(nodep);
        m_scopep = NULL;
    }
    virtual void visit(AstActive* nodep) VL_OVERRIDE {
        // Create required blocks and add to module
        UINFO(4,"  BLOCK  "<<nodep<<endl);
        AstNode::user2ClearTree();
        m_domainp = nodep->sensesp();
        if (!m_domainp || m_domainp->hasCombo() || m_domainp->hasClocked()) {  // IE not hasSettle/hasInitial
            iterateNewStmt(nodep);
        }
        m_domainp = NULL;
        AstNode::user2ClearTree();
    }
    virtual void visit(AstNodeVarRef* nodep) VL_OVERRIDE {
        if (m_scopep) {
            UASSERT_OBJ(m_logicVertexp, nodep, "Var ref not under a logic block");
            AstVarScope* varscp = nodep->varScopep();
            UASSERT_OBJ(varscp, nodep, "Var didn't get varscoped in V3Scope.cpp");
            CdcVarVertex* varvertexp = makeVarVertex(varscp);
            UINFO(5," VARREF to "<<varscp<<endl);
            // We use weight of one for normal edges,
            // Weight of CDC_WEIGHT_ASYNC to indicate feeds async (for reporting)
            // When simplify we'll take the MAX weight
            if (nodep->lvalue()) {
                new V3GraphEdge(&m_graph, m_logicVertexp, varvertexp, 1);
                if (m_inDly) {
                    varvertexp->fromFlop(true);
                    varvertexp->srcDomainp(m_domainp);
                    varvertexp->srcDomainSet(true);
                }
            } else {
                if (varvertexp->cntAsyncRst()) {
                    //UINFO(9," edgeasync "<<varvertexp->name()<<" to "<<m_logicVertexp<<endl);
                    new V3GraphEdge(&m_graph, varvertexp, m_logicVertexp, CDC_WEIGHT_ASYNC);
                } else {
                    //UINFO(9," edgena    "<<varvertexp->name()<<" to "<<m_logicVertexp<<endl);
                    new V3GraphEdge(&m_graph, varvertexp, m_logicVertexp, 1);
                }
            }
        }
    }
    virtual void visit(AstAssignDly* nodep) VL_OVERRIDE {
        m_inDly = true;
        iterateChildren(nodep);
        m_inDly = false;
    }
    virtual void visit(AstSenItem* nodep) VL_OVERRIDE {
        // Note we look at only AstSenItems, not AstSenGate's
        // The gating term of a AstSenGate is normal logic
        m_inSenItem = true;
        iterateChildren(nodep);
        m_inSenItem = false;
    }
    virtual void visit(AstAlways* nodep) VL_OVERRIDE {
        iterateNewStmt(nodep);
    }
    virtual void visit(AstAlwaysPublic* nodep) VL_OVERRIDE {
        // CDC doesn't care about public variables
    }
    virtual void visit(AstCFunc* nodep) VL_OVERRIDE {
        iterateNewStmt(nodep);
    }
    virtual void visit(AstSenGate* nodep) VL_OVERRIDE {
        // First handle the clock part will be handled in a minute by visit AstSenItem
        // The logic gating term is dealt with as logic
        iterateNewStmt(nodep);
    }
    virtual void visit(AstAssignAlias* nodep) VL_OVERRIDE {
        iterateNewStmt(nodep);
    }
    virtual void visit(AstAssignW* nodep) VL_OVERRIDE {
        iterateNewStmt(nodep);
    }

    // Math that shouldn't cause us to clear hazard
    virtual void visit(AstConst* nodep) VL_OVERRIDE { }
    virtual void visit(AstReplicate* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }
    virtual void visit(AstConcat* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }
    virtual void visit(AstNot* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }
    virtual void visit(AstSel* nodep) VL_OVERRIDE {
        if (!VN_IS(nodep->lsbp(), Const)) setNodeHazard(nodep);
        iterateChildren(nodep);
    }
    virtual void visit(AstNodeSel* nodep) VL_OVERRIDE {
        if (!VN_IS(nodep->bitp(), Const)) setNodeHazard(nodep);
        iterateChildren(nodep);
    }

    // Ignores
    virtual void visit(AstInitial* nodep) VL_OVERRIDE { }
    virtual void visit(AstTraceInc* nodep) VL_OVERRIDE { }
    virtual void visit(AstCoverToggle* nodep) VL_OVERRIDE { }
    virtual void visit(AstNodeDType* nodep) VL_OVERRIDE { }

    //--------------------
    // Default
    virtual void visit(AstNodeMath* nodep) VL_OVERRIDE {
        setNodeHazard(nodep);
        iterateChildren(nodep);
    }
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit CdcVisitor(AstNode* nodep) {
        m_logicVertexp = NULL;
        m_scopep = NULL;
        m_modp = NULL;
        m_domainp = NULL;
        m_inDly = false;
        m_inSenItem = 0;
        m_userGeneration = 0;
        m_filelineWidth = 0;

        // Make report of all signal names and what clock edges they have
        string filename = v3Global.opt.makeDir()+"/"+v3Global.opt.prefix()+"__cdc.txt";
        m_ofp = V3File::new_ofstream(filename);
        if (m_ofp->fail()) v3fatal("Can't write "<<filename);
        m_ofFilename = filename;
        *m_ofp<<"CDC Report for "<<v3Global.opt.prefix()<<endl;
        *m_ofp<<"Each dump below traces logic from inputs/source flops to destination flop(s).\n";
        *m_ofp<<"First source logic is listed, then a variable that logic generates,\n";
        *m_ofp<<"repeating recursively forwards to the destination flop(s).\n";
        *m_ofp<<"%% Indicates the operator considered potentially hazardous.\n";

        iterate(nodep);
        analyze();
        if (debug()>=1) edgeReport();  // Not useful to users at the moment
        if (0) {
            *m_ofp<<"\nDBG-test-dumper\n";
            V3EmitV::verilogPrefixedTree(nodep, *m_ofp, "DBG ", 40, NULL, true);
            *m_ofp<<endl;
        }
    }
    virtual ~CdcVisitor() {
        if (m_ofp) VL_DO_CLEAR(delete m_ofp, m_ofp = NULL);
    }
};

//######################################################################
// Cdc class functions

void V3Cdc::cdcAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    CdcVisitor visitor (nodep);
}
