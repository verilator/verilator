//*************************************************************************
// DESCRIPTION: Verilator: LValue module/signal name references
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2008 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************
// LinkLValue TRANSFORMATIONS:
//	Top-down traversal
//	    Set lvalue() attributes on appropriate VARREFs.
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
#include "V3LinkLValue.h"
#include "V3Ast.h"

//######################################################################
// Link state, as a visitor of each AstNode

class LinkLValueVisitor : public AstNVisitor {
private:
    // NODE STATE

    // STATE
    bool	m_setRefLvalue;	// Set VarRefs to lvalues for pin assignments
    AstNodeFTask* m_ftaskp;	// Function or task we're inside

    //int debug() { return 9; }

    // METHODS

    // VISITs
    // Result handing
    virtual void visit(AstNodeVarRef* nodep, AstNUser*) {
	// VarRef: LValue its reference
	if (m_setRefLvalue) {
	    nodep->lvalue(true);
	}
	if (nodep->varp()) {
	    if (nodep->lvalue() && nodep->varp()->isInOnly()) {
		if (!m_ftaskp) {
		    nodep->v3error("Assigning to input variable: "<<nodep->prettyName());
		}
	    }
	}
	nodep->iterateChildren(*this);
    }

    // Nodes that start propagating down lvalues
    virtual void visit(AstPin* nodep, AstNUser*) {
	if (nodep->modVarp() && nodep->modVarp()->isOutput()) {
	    // When the varref's were created, we didn't know the I/O state
	    // Now that we do, and it's from a output, we know it's a lvalue
	    m_setRefLvalue = true;
	    nodep->iterateChildren(*this);
	    m_setRefLvalue = false;
	} else {
	    nodep->iterateChildren(*this);
	}
    }
    virtual void visit(AstNodeAssign* nodep, AstNUser*) {
	bool last_setRefLvalue = m_setRefLvalue;
	{
	    m_setRefLvalue = true;
	    nodep->lhsp()->iterateAndNext(*this);
	    m_setRefLvalue = false;
	    nodep->rhsp()->iterateAndNext(*this);
	}
	m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstFOpen* nodep, AstNUser*) {
	bool last_setRefLvalue = m_setRefLvalue;
	{
	    m_setRefLvalue = true;
	    nodep->filep()->iterateAndNext(*this);
	    m_setRefLvalue = false;
	    nodep->filenamep()->iterateAndNext(*this);
	    nodep->modep()->iterateAndNext(*this);
	}
	m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstFClose* nodep, AstNUser*) {
	bool last_setRefLvalue = m_setRefLvalue;
	{
	    m_setRefLvalue = true;
	    nodep->filep()->iterateAndNext(*this);
	}
	m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstFFlush* nodep, AstNUser*) {
	bool last_setRefLvalue = m_setRefLvalue;
	{
	    m_setRefLvalue = true;
	    nodep->filep()->iterateAndNext(*this);
	}
	m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstFGetC* nodep, AstNUser*) {
	bool last_setRefLvalue = m_setRefLvalue;
	{
	    m_setRefLvalue = true;
	    nodep->filep()->iterateAndNext(*this);
	}
	m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstFGetS* nodep, AstNUser*) {
	bool last_setRefLvalue = m_setRefLvalue;
	{
	    m_setRefLvalue = true;
	    nodep->filep()->iterateAndNext(*this);
	    nodep->strgp()->iterateAndNext(*this);
	}
	m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstFScanF* nodep, AstNUser*) {
	bool last_setRefLvalue = m_setRefLvalue;
	{
	    m_setRefLvalue = true;
	    nodep->filep()->iterateAndNext(*this);
	    nodep->exprsp()->iterateAndNext(*this);
	}
	m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstSScanF* nodep, AstNUser*) {
	bool last_setRefLvalue = m_setRefLvalue;
	{
	    m_setRefLvalue = true;
	    nodep->exprsp()->iterateAndNext(*this);
	}
	m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstReadMem* nodep, AstNUser*) {
	bool last_setRefLvalue = m_setRefLvalue;
	{
	    m_setRefLvalue = true;
	    nodep->memp()->iterateAndNext(*this);
	    m_setRefLvalue = false;
	    nodep->filenamep()->iterateAndNext(*this);
	    nodep->lsbp()->iterateAndNext(*this);
	    nodep->msbp()->iterateAndNext(*this);
	}
	m_setRefLvalue = last_setRefLvalue;
    }

    // Nodes that change LValue state
    virtual void visit(AstSel* nodep, AstNUser*) {
	bool last_setRefLvalue = m_setRefLvalue;
	{
	    nodep->lhsp()->iterateAndNext(*this);
	    // Only set lvalues on the from
	    m_setRefLvalue = false;
	    nodep->rhsp()->iterateAndNext(*this);
	    nodep->thsp()->iterateAndNext(*this);
	}
	m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstNodeSel* nodep, AstNUser*) {
	bool last_setRefLvalue = m_setRefLvalue;
	{   // Only set lvalues on the from
	    nodep->lhsp()->iterateAndNext(*this);
	    m_setRefLvalue = false;
	    nodep->rhsp()->iterateAndNext(*this);
	}
	m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstNodePreSel* nodep, AstNUser*) {
	bool last_setRefLvalue = m_setRefLvalue;
	{   // Only set lvalues on the from
	    nodep->lhsp()->iterateAndNext(*this);
	    m_setRefLvalue = false;
	    nodep->rhsp()->iterateAndNext(*this);
	    nodep->thsp()->iterateAndNext(*this);
	}
	m_setRefLvalue = last_setRefLvalue;
    }
    virtual void visit(AstNodeFTask* nodep, AstNUser*) {
	m_ftaskp = nodep;
	nodep->iterateChildren(*this);
	m_ftaskp = NULL;
    }

    virtual void visit(AstNode* nodep, AstNUser*) {
	// Default: Just iterate
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    LinkLValueVisitor(AstNode* nodep, bool start) {
	m_setRefLvalue = start;
	m_ftaskp = NULL;
	nodep->accept(*this);
    }
    virtual ~LinkLValueVisitor() {}
};

//######################################################################
// Link class functions

void V3LinkLValue::linkLValue(AstNetlist* rootp) {
    UINFO(4,__FUNCTION__<<": "<<endl);
    LinkLValueVisitor visitor(rootp, false);
}
void V3LinkLValue::linkLValueSet(AstNode* nodep) {
    // Called by later link functions when it is known a node needs
    // to be converted to a lvalue.
    UINFO(9,__FUNCTION__<<": "<<endl);
    LinkLValueVisitor visitor(nodep, true);
}
