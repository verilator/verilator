//*************************************************************************
// DESCRIPTION: Verilator: Resolve module/signal name references
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2009 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************
// LINK TRANSFORMATIONS:
//	Top-down traversal
//	    Cells:
//		Read module if needed
//		Link to module that instantiates it
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <map>
#include <algorithm>
#include <vector>

#include "V3Global.h"
#include "V3LinkCells.h"
#include "V3SymTable.h"
#include "V3Read.h"
#include "V3Ast.h"
#include "V3Graph.h"

//######################################################################
// Graph subclasses

class LinkCellsGraph : public V3Graph {
public:
    LinkCellsGraph() {}
    virtual ~LinkCellsGraph() {}
    virtual void loopsMessageCb(V3GraphVertex* vertexp);
};


class LinkCellsVertex : public V3GraphVertex {
    AstModule* m_modp;
public:
    LinkCellsVertex(V3Graph* graphp, AstModule* modp)
	: V3GraphVertex(graphp), m_modp(modp) {}
    virtual ~LinkCellsVertex() {}
    AstModule* modp() const { return m_modp; }
    virtual string name() const { return modp()->name(); }
};

class LibraryVertex : public V3GraphVertex {
public:
    LibraryVertex(V3Graph* graphp)
	: V3GraphVertex(graphp) {}
    virtual ~LibraryVertex() {}
    virtual string name() const { return "*LIBRARY*"; }
};

void LinkCellsGraph::loopsMessageCb(V3GraphVertex* vertexp) {
    if (LinkCellsVertex* vvertexp = dynamic_cast<LinkCellsVertex*>(vertexp)) {
	vvertexp->modp()->v3error("Recursive module (module instantiates itself): "
				  <<vvertexp->modp()->name());
	V3Error::abortIfErrors();
    } else {  // Everything should match above, but...
	v3fatalSrc("Recursive instantiations");
    }
}

//######################################################################
// Link state, as a visitor of each AstNode

class LinkCellsVisitor : public AstNVisitor {
private:
    // NODE STATE
    //  Entire netlist:
    //   AstModule::user1p()	// V3GraphVertex*    Vertex describing this module
    AstUser1InUse	m_inuser1;

    // STATE
    // Below state needs to be preserved between each module call.
    AstModule*	m_modp;		// Current module
    V3SymTable  m_mods;		// Symbol table of all module names
    LinkCellsGraph	m_graph;	// Linked graph of all cell interconnects
    LibraryVertex*	m_libVertexp;	// Vertex at root of all libraries
    V3GraphVertex*	m_topVertexp;	// Vertex of top module

    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    // METHODS
    V3GraphVertex* vertex(AstModule* nodep) {
	// Return corresponding vertex for this module
	if (!nodep->user1p()) {
	    nodep->user1p(new LinkCellsVertex(&m_graph, nodep));
	}
	return (nodep->user1p()->castGraphVertex());
    }

    // VISITs
    virtual void visit(AstNetlist* nodep, AstNUser*) {
	AstNode::user1ClearTree();
	readModNames();
	nodep->iterateChildren(*this);
	// Find levels in graph
	m_graph.removeRedundantEdges(&V3GraphEdge::followAlwaysTrue);
	m_graph.dumpDotFilePrefixed("linkcells");
	m_graph.rank();
	for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp=itp->verticesNextp()) {
	    if (LinkCellsVertex* vvertexp = dynamic_cast<LinkCellsVertex*>(itp)) {
		// +1 so we leave level 1  for the new wrapper we'll make in a moment
		vvertexp->modp()->level(vvertexp->rank()+1);
	    }
	}
	if (v3Global.opt.topModule()!=""
	    && !m_topVertexp) {
	    v3error("Specified --top-module '"<<v3Global.opt.topModule()<<"' was not found in design.");
	}
    }
    virtual void visit(AstModule* nodep, AstNUser*) {
	// Module: Pick up modnames, so we can resolve cells later
	m_modp = nodep;
	UINFO(2,"Link Module: "<<nodep<<endl);
	bool topMatch = (v3Global.opt.topModule()==nodep->name());
	if (topMatch) m_topVertexp = vertex(nodep);
	if (v3Global.opt.topModule()==""
	    ? nodep->inLibrary()   // Library cells are lower
	    : !topMatch) {  // Any non-specified module is lower
	    // Put under a fake vertex so that the graph ranking won't indicate
	    // this is a top level module
	    if (!m_libVertexp) m_libVertexp = new LibraryVertex(&m_graph);
	    new V3GraphEdge(&m_graph, m_libVertexp, vertex(nodep), 1, false);
	}
	nodep->iterateChildren(*this);
	nodep->checkTree();
	m_modp = NULL;
    }

    virtual void visit(AstCell* nodep, AstNUser*) {
	// Cell: Resolve its filename.  If necessary, parse it.
	if (!nodep->modp()) {
	    UINFO(4,"Link Cell: "<<nodep<<endl);
	    // Use findIdUpward instead of findIdFlat; it doesn't matter for now
	    // but we might support modules-under-modules someday.
	    AstModule* modp = m_mods.findIdUpward(nodep->modName())->castModule();
	    if (!modp) {
		// Read-subfile
		V3Read reader (v3Global.rootp());
		reader.readFile(nodep->fileline(), nodep->modName(), false);
		V3Error::abortIfErrors();
		// We've read new modules, grab new pointers to their names
		readModNames();
		// Check again
		modp = m_mods.findIdUpward(nodep->modName())->castModule();
		if (!modp) {
		    nodep->v3error("Can't resolve module reference: "<<nodep->modName());
		}
	    }
	    if (modp) {
		nodep->modp(modp);
		// Track module depths, so can sort list from parent down to children
		new V3GraphEdge(&m_graph, vertex(m_modp), vertex(modp), 1, false);
	    }
	}
	// Convert .* to list of pins
	if (nodep->modp() && nodep->pinStar()) {
	    // Note what pins exist
	    UINFO(9,"  CELL .* connect "<<nodep<<endl);
	    V3SymTable  ports;		// Symbol table of all connected port names
	    for (AstPin* pinp = nodep->pinsp(); pinp; pinp=pinp->nextp()->castPin()) {
		if (pinp->name()=="") pinp->v3error("Connect by position is illegal in .* connected cells");
		if (!ports.findIdFlat(pinp->name())) {
		    ports.insert(pinp->name(), pinp);
		}
	    }
	    // We search ports, rather than in/out declarations as they aren't resolved yet,
	    // and it's easier to do it now than in V3Link when we'd need to repeat steps.
	    for (AstNode* portnodep = nodep->modp()->stmtsp(); portnodep; portnodep=portnodep->nextp()) {
		if (AstPort* portp = portnodep->castPort()) {
		    if (!ports.findIdFlat(portp->name())) {
			UINFO(9,"    need PORT  "<<portp<<endl);
			// Create any not already connected
			AstPin* newp = new AstPin(nodep->fileline(),0,portp->name(),
						  new AstVarRef(nodep->fileline(),portp->name(),false));
			newp->svImplicit(true);
			nodep->addPinsp(newp);
		    }
		}
	    }
	}
	// Convert unnamed pins to pin number based assignments
	for (AstPin* pinp = nodep->pinsp(); pinp; pinp=pinp->nextp()->castPin()) {
	    if (pinp->name()=="") pinp->name("__pinNumber"+cvtToStr(pinp->pinNum()));
	}
	for (AstPin* pinp = nodep->paramsp(); pinp; pinp=pinp->nextp()->castPin()) {
	    if (pinp->name()=="") pinp->name("__paramNumber"+cvtToStr(pinp->pinNum()));
	}
	if (nodep->modp()) {
	    nodep->iterateChildren(*this);
	}
    }

    // Accelerate the recursion
    // Must do statements to support Generates, math though...
    virtual void visit(AstNodeMath* nodep, AstNUser*) {}
    virtual void visit(AstNode* nodep, AstNUser*) {
	// Default: Just iterate
	nodep->iterateChildren(*this);
    }

    // METHODS
    void readModNames() {
	// Look at all modules, and store pointers to all module names
	for (AstModule* nodep = v3Global.rootp()->modulesp(); nodep; nodep=nodep->nextp()->castModule()) {
	    AstNode* foundp = m_mods.findIdUpward(nodep->name());
	    if (foundp && foundp != nodep) {
		nodep->v3error("Duplicate declaration of module: "<<nodep->prettyName());
		foundp->v3error("... Location of original declaration");
	    } else if (!foundp) {
		m_mods.insert(nodep->name(), nodep);
	    }
	}
    }

public:
    // CONSTUCTORS
    LinkCellsVisitor() {
	m_modp = NULL;
	m_libVertexp = NULL;
	m_topVertexp = NULL;
    }
    virtual ~LinkCellsVisitor() {}
    void main(AstNetlist* rootp) {
	rootp->accept(*this);
    }
};

//######################################################################
// Link class functions

void V3LinkCells::link(AstNetlist* rootp) {
    UINFO(4,__FUNCTION__<<": "<<endl);
    LinkCellsVisitor visitor;
    visitor.main(rootp);
}
