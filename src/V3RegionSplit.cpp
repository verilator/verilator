// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Block code splitting
//
// Code available from: https://verilator.org
//
//*************************************************************************
// V3RegionSplit's Transformations:
//
//  Split Always, Initial, CFunc blocks based on regions of statements
//    Each block should contain statements only from a single region
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3RegionSplit.h"
#include "V3EmitCBase.h"
#include "V3Ast.h"

#include <list>

// Always visitor

class AlwaysVisitor : public AstNVisitor {
    AstAlways* m_alwaysp;
    std::list<AstAlways*> m_newAlways;
private:
    void move(AstNodeStmt* nodep) {
        AstAlways* alwaysp = NULL;
        for (auto const& ap : m_newAlways) {
            if (nodep->region() == ap->region())
                alwaysp = ap;
        }
        if (!alwaysp) {
            alwaysp = new AstAlways(m_alwaysp->fileline(), VAlwaysKwd::ALWAYS, m_alwaysp->sensesp(), NULL);
            alwaysp->region(nodep->region());
            m_newAlways.push_front(alwaysp);
            m_alwaysp->addNext(alwaysp);
        }

        nodep->unlinkFrBack();
        alwaysp->addStmtp(nodep);
    }

    virtual void visit(AstNodeStmt* nodep) VL_OVERRIDE {
        UINFO(4, __FUNCTION__ << ": " << nodep << endl);
        if (m_alwaysp->region().isNone()) {
            m_alwaysp->region(nodep->region());
        } else if (nodep->region().isNone() || nodep->region() == m_alwaysp->region()){
            // Regions match
        } else {
            // Mismatched regions
            move(nodep);
        }
    }

    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }

public:
    explicit AlwaysVisitor(AstAlways* nodep)
        : m_alwaysp (nodep) {
        iterateChildren(nodep);
    }
    virtual ~AlwaysVisitor() {}
};

// Initial visitor

class InitialVisitor : public AstNVisitor {
    AstInitial* m_initialp;
private:
    virtual void visit(AstNodeStmt* nodep) VL_OVERRIDE {
        UINFO(4, __FUNCTION__ << ": " << nodep << endl);
        if (m_initialp->region().isNone()) {
            m_initialp->region(nodep->region());
        } else if (nodep->region().isNone() || nodep->region() == m_initialp->region()){
            // Regions match
        } else {
            // Mismatched regions
        }
    }

    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }

public:
    explicit InitialVisitor(AstInitial* nodep)
        : m_initialp (nodep) {
        iterateChildren(nodep);
    }
    virtual ~InitialVisitor() {}
};

// CFunc visitor

class CFuncVisitor : public AstNVisitor {
    AstCFunc* m_cfuncp;
    AstScope* m_scopep;
    AstActive* m_activep;
    std::list<AstCFunc*> m_newFuncs;
private:
    AstCFunc* createCFunc(VRegion region, bool slow) {
        AstCFunc* funcp = NULL;
        string name = m_cfuncp->name() + "_" + region.ascii();

        funcp = new AstCFunc(m_cfuncp->fileline(), name, m_scopep);
        funcp->argTypes(EmitCBaseVisitor::symClassVar());
        funcp->symProlog(true);
        funcp->slow(slow);
        funcp->region(region);
        m_scopep->addActivep(funcp);

        AstCCall* callp = new AstCCall(m_cfuncp->fileline(), funcp);
        callp->region(region);
        callp->argTypes("vlSymsp");
        m_activep->addStmtsp(callp);

        return funcp;
    }

    void move(AstInitial* nodep) {
        AstCFunc* funcp = NULL;
        for (auto const& fp : m_newFuncs) {
            if (nodep->region() == fp->region())
                funcp = fp;
        }
        if (!funcp) {
            funcp = createCFunc(nodep->region(), true);
            m_newFuncs.push_front(funcp);
            UINFO(5, "move: created new CFunc " << funcp << endl);
        }
        nodep->unlinkFrBack();
        funcp->addStmtsp(nodep);
    }

    void move(AstAlways* nodep) {
        AstCFunc* funcp = NULL;
        for (auto const& fp : m_newFuncs) {
            if (nodep->region() == fp->region())
                funcp = fp;
        }
        if (!funcp) {
            funcp = createCFunc(nodep->region(), false);
            m_newFuncs.push_front(funcp);
            UINFO(5, "move: created new CFunc " << funcp << endl);
        }
        nodep->unlinkFrBack();
        funcp->addStmtsp(nodep);
    }

    virtual void visit(AstInitial* nodep) VL_OVERRIDE {
        InitialVisitor visitor(nodep); // Mark every AstInitial with region information

        if (m_cfuncp->region().isNone()) {
            m_cfuncp->region(nodep->region());
        } else if (nodep->region().isNone() || nodep->region() == m_cfuncp->region()){
            // Regions match
        } else {
            // Mismatched regions
            move(nodep);
        }
    }

    virtual void visit(AstAlways* nodep) VL_OVERRIDE {
        AlwaysVisitor visitor(nodep); // Mark every AstAlways with region information

        if (m_cfuncp->region().isNone()) {
            m_cfuncp->region(nodep->region());
        } else if (nodep->region().isNone() || nodep->region() == m_cfuncp->region()){
            // Regions match
        } else {
            // Mismatched regions
            move(nodep);
        }
    }

    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }

public:
    explicit CFuncVisitor(AstCFunc* nodep, AstScope* scopep, AstActive* activep)
        : m_activep (activep)
        , m_cfuncp(nodep)
        , m_scopep(scopep) {
        UINFO(4, "CFuncVisitor " << nodep << endl);
        iterateChildren(nodep);
    }

    virtual ~CFuncVisitor() {}
};

// CCall visitor

class CallVisitor : public AstNVisitor {
    AstScope* m_scopep;
    AstActive* m_activep;
private:
    virtual void visit(AstScope* nodep) VL_OVERRIDE {
        m_scopep = nodep;
        iterateChildren(nodep);
        m_scopep = NULL;
    }

    virtual void visit(AstActive* nodep) VL_OVERRIDE {
        m_activep = nodep;
        iterateChildren(nodep);
        m_activep = NULL;
    }

    virtual void visit(AstCCall* nodep) VL_OVERRIDE {
        CFuncVisitor visitor(nodep->funcp(), m_scopep, m_activep);
    }

    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }

public:
    explicit CallVisitor(AstNetlist* nodep) {
        m_scopep = NULL;
        m_activep = NULL;
        iterateChildren(nodep);
        V3Global::dumpCheckGlobalTree("region_split", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
    }

    virtual ~CallVisitor() {}
};

//######################################################################
// RegionSplit class functions

void V3RegionSplit::splitRegions(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    CallVisitor visitor(nodep);
}
