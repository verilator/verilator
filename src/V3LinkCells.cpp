//*************************************************************************
// DESCRIPTION: Verilator: Resolve module/signal name references
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2012 by Wilson Snyder.  This program is free software; you can
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
// NO EDITS: Don't replace or delete nodes, as the parser symbol table
//	     has pointers into the ast tree.
//
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
#include "V3Parse.h"
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
    AstNodeModule* m_modp;
public:
    LinkCellsVertex(V3Graph* graphp, AstNodeModule* modp)
	: V3GraphVertex(graphp), m_modp(modp) {}
    virtual ~LinkCellsVertex() {}
    AstNodeModule* modp() const { return m_modp; }
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
    //   AstNodeModule::user1p()	// V3GraphVertex*    Vertex describing this module
    //  Allocated across all readFiles in V3Global::readFiles:
    //   AstNode::user4p()	// V3SymTable*    Package and typedef symbol names
    AstUser1InUse	m_inuser1;

    // STATE
    V3InFilter*		m_filterp;	// Parser filter

    // Below state needs to be preserved between each module call.
    AstNodeModule*	m_modp;		// Current module
    V3SymTable  	m_mods;		// Symbol table of all module names
    LinkCellsGraph	m_graph;	// Linked graph of all cell interconnects
    LibraryVertex*	m_libVertexp;	// Vertex at root of all libraries
    V3GraphVertex*	m_topVertexp;	// Vertex of top module

    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    // METHODS
    V3GraphVertex* vertex(AstNodeModule* nodep) {
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
		AstNodeModule* modp = vvertexp->modp();
		modp->level(vvertexp->rank()+1);
		if (vvertexp == m_topVertexp && modp->level() != 2) {
		    AstNodeModule* abovep = NULL;
		    if (V3GraphEdge* edgep = vvertexp->inBeginp()) {
			if (LinkCellsVertex* eFromVertexp = dynamic_cast<LinkCellsVertex*>(edgep->fromp())) {
			    abovep = eFromVertexp->modp();
			}
		    }
		    v3error("Specified --top-module '"<<v3Global.opt.topModule()
			    <<"' isn't at the top level, it's under another cell '"
			    <<(abovep ? abovep->prettyName() : "UNKNOWN")<<"'");
		}
	    }
	}
	if (v3Global.opt.topModule()!=""
	    && !m_topVertexp) {
	    v3error("Specified --top-module '"<<v3Global.opt.topModule()<<"' was not found in design.");
	}
    }
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	// Module: Pick up modnames, so we can resolve cells later
	m_modp = nodep;
	UINFO(2,"Link Module: "<<nodep<<endl);
	bool topMatch = (v3Global.opt.topModule()==nodep->name());
	if (topMatch) {
	    m_topVertexp = vertex(nodep);
	    UINFO(2,"Link --top-module: "<<nodep<<endl);
	    nodep->inLibrary(false);   // Safer to make sure it doesn't disappear
	}
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
	    AstNodeModule* modp = m_mods.findIdUpward(nodep->modName())->castNodeModule();
	    if (!modp) {
		// Read-subfile
		// If file not found, make AstNotFoundModule, rather than error out.
		// We'll throw the error when we know the module will really be needed.
		V3Parse parser (v3Global.rootp(), m_filterp);
		parser.parseFile(nodep->fileline(), nodep->modName(), false, "");
		V3Error::abortIfErrors();
		// We've read new modules, grab new pointers to their names
		readModNames();
		// Check again
		modp = m_mods.findIdUpward(nodep->modName())->castNodeModule();
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
	// Remove AstCell(AstPin("",NULL)), it's a side effect of how we parse "()"
	// the empty middle is identical to the empty rule that must find pins in "(,)".
	if (nodep->pinsp() && !nodep->pinsp()->nextp()
	    && nodep->pinsp()->name() == ""
	    && !nodep->pinsp()->exprp()) {
	    pushDeletep(nodep->pinsp()->unlinkFrBackWithNext());
	}
	if (nodep->paramsp() && !nodep->paramsp()->nextp()
	    && nodep->paramsp()->name() == ""
	    && !nodep->paramsp()->exprp()) {
	    pushDeletep(nodep->paramsp()->unlinkFrBackWithNext());
	}
	// Convert .* to list of pins
	bool pinStar = false;
	for (AstPin* nextp, *pinp = nodep->pinsp(); pinp; pinp=nextp) {
	    nextp = pinp->nextp()->castPin();
	    if (pinp->dotStar()) {
		if (pinStar) pinp->v3error("Duplicate .* in a cell");
		pinStar = true;
		// Done with this fake pin
		pinp->unlinkFrBack()->deleteTree(); pinp=NULL;
	    }
	}
	if (nodep->modp() && pinStar) {
	    // Note what pins exist
	    UINFO(9,"  CELL .* connect "<<nodep<<endl);
	    V3SymTable  ports;	// Symbol table of all connected port names
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
	for (AstNodeModule* nextp,* nodep = v3Global.rootp()->modulesp(); nodep; nodep=nextp) {
	    nextp = nodep->nextp()->castNodeModule();
	    AstNode* foundp = m_mods.findIdUpward(nodep->name());
	    if (foundp && foundp != nodep) {
		if (!(foundp->fileline()->warnIsOff(V3ErrorCode::MODDUP) || nodep->fileline()->warnIsOff(V3ErrorCode::MODDUP))) {
		    nodep->v3warn(MODDUP,"Duplicate declaration of module: "<<nodep->prettyName());
		    foundp->v3warn(MODDUP,"... Location of original declaration");
		}
		nodep->unlinkFrBack();
		pushDeletep(nodep); nodep=NULL;
	    } else if (!foundp) {
		m_mods.insert(nodep->name(), nodep);
	    }
	}
	//if (debug()>=9) m_mods.dump(cout, "-syms: ");
    }

public:
    // CONSTUCTORS
    LinkCellsVisitor(AstNetlist* rootp, V3InFilter* filterp) {
	m_filterp = filterp;
	m_modp = NULL;
	m_libVertexp = NULL;
	m_topVertexp = NULL;
	rootp->accept(*this);
    }
    virtual ~LinkCellsVisitor() {}
};

//######################################################################
// Link class functions

void V3LinkCells::link(AstNetlist* rootp, V3InFilter* filterp) {
    UINFO(4,__FUNCTION__<<": "<<endl);
    LinkCellsVisitor visitor (rootp, filterp);
}
