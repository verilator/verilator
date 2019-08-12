// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Simulate code to determine output values/variables
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2019 by Wilson Snyder.  This program is free software; you can
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
//
// void example_usage() {
//      SimulateVisitor simvis (false, false);
//      simvis.clear();
//      // Set all inputs to the constant
//      for (deque<AstVarScope*>::iterator it = m_inVarps.begin(); it!=m_inVarps.end(); ++it) {
//          simvis.newValue(invscp, #);
//      }
//      // Simulate
//      simvis.main(nodep);
//      // Read outputs
//      for (deque<AstVarScope*>::iterator it = m_outVarps.begin(); it!=m_outVarps.end(); ++it) {
//          AstConst* outconstp = simvis.fetchOutNumberNull(outvscp);
//
//*************************************************************************


#ifndef _V3SIMULATE_H_
#define _V3SIMULATE_H_ 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3Ast.h"
#include "V3Width.h"
#include "V3Task.h"

#include <deque>
#include <sstream>

//============================================================================

//######################################################################
// Simulate class functions

class SimStackNode {
public:
    // MEMBERS
    AstFuncRef*         m_funcp;
    V3TaskConnects*     m_tconnects;
    // CONSTRUCTORS
    SimStackNode(AstFuncRef* funcp, V3TaskConnects* tconnects):
        m_funcp(funcp),
        m_tconnects(tconnects) {}
    ~SimStackNode() {}
};

typedef std::deque<AstConst*> ConstDeque;
typedef std::map<AstNodeDType*, ConstDeque> ConstPile;

class SimulateVisitor : public AstNVisitor {
    // Simulate a node tree, returning value of variables
    // Two major operating modes:
    //   Test the tree to see if it is conformant
    //   Given a set of input values, find the output values
    // Both are done in this same visitor to reduce risk; if a visitor
    // is missing, we will simply not apply the optimization, rather then bomb.

private:
    // NODE STATE
    // Cleared on each always/assignw
    AstUser1InUse       m_inuser1;
    AstUser2InUse       m_inuser2;
    AstUser3InUse       m_inuser3;

    // Checking:
    //  AstVar(Scope)::user1()  -> VarUsage.  Set true to indicate tracking as lvalue/rvalue
    // Simulating:
    //  AstVar(Scope)::user3()  -> AstConst*. Input value of variable or node
    //    (and output for non-delayed assignments)
    //  AstVar(Scope)::user2()  -> AstCont*. Output value of variable (delayed assignments)

    enum VarUsage { VU_NONE=0, VU_LV=1, VU_RV=2, VU_LVDLY=4 };

    // STATE
    // Major mode
    bool        m_checkOnly;            ///< Checking only (no simulation) mode
    bool        m_scoped;               ///< Running with AstVarScopes instead of AstVars
    bool        m_params;               ///< Doing parameter propagation
    // Checking:
    string      m_whyNotOptimizable;    ///< String explaining why not optimizable or NULL to optimize
    AstNode*    m_whyNotNodep;          ///< First node not optimizable
    bool        m_anyAssignDly;         ///< True if found a delayed assignment
    bool        m_anyAssignComb;        ///< True if found a non-delayed assignment
    bool        m_inDlyAssign;          ///< Under delayed assignment
    int         m_instrCount;           ///< Number of nodes
    int         m_dataCount;            ///< Bytes of data
    AstJumpGo*  m_jumpp;                ///< Jump label we're branching from
    // Simulating:
    ConstPile   m_constFreeps;          ///< List of all AstConst* free and not in use
    ConstPile   m_constAllps;           ///< List of all AstConst* free and in use
    std::deque<SimStackNode*> m_callStack;  ///< Call stack for verbose error messages

    // Cleanup
    // V3Numbers that represents strings are a bit special and the API for
    // V3Number does not allow changing them.
    std::deque<AstConst*> m_stringValuesp;  // List of allocated string numbers


    // Note level 8&9 include debugging each simulation value
    VL_DEBUG_FUNC;  // Declare debug()

    // Potentially very slow, intended for debugging
    string prettyNumber(const V3Number* nump, AstNodeDType* dtypep) {
        if (AstRefDType* refdtypep = VN_CAST(dtypep, RefDType)) {
            dtypep = refdtypep->skipRefp();
        }
        if (AstStructDType* stp = VN_CAST(dtypep, StructDType)) {
            if (stp->packed()) {
                std::ostringstream out;
                out<<"'{";
                for (AstMemberDType* itemp = stp->membersp();
                     itemp; itemp=VN_CAST(itemp->nextp(), MemberDType)) {
                    int width = itemp->width();
                    int lsb = itemp->lsb();
                    int msb = lsb + width - 1;
                    V3Number fieldNum(nump, width);
                    fieldNum.opSel(*nump, msb, lsb);
                    out<<itemp->name()<<": ";
                    if (AstNodeDType * childTypep = itemp->subDTypep()) {
                        out<<prettyNumber(&fieldNum, childTypep);
                    } else {
                        out<<fieldNum;
                    }
                    if (itemp->nextp()) out<<", ";
                }
                out<<"}";
                return out.str();
            }
        } else if (AstPackArrayDType * arrayp = VN_CAST(dtypep, PackArrayDType)) {
            if (AstNodeDType * childTypep = arrayp->subDTypep()) {
                std::ostringstream out;
                out<<"[";
                int arrayElements = arrayp->elementsConst();
                for (int element = 0; element < arrayElements; ++element) {
                    int width = childTypep->width();
                    int lsb = width * element;
                    int msb = lsb + width - 1;
                    V3Number fieldNum(nump, width);
                    fieldNum.opSel(*nump, msb, lsb);
                    int arrayElem = arrayp->lsb() + element;
                    out<<arrayElem<<" = "<<prettyNumber(&fieldNum, childTypep);
                    if (element < arrayElements - 1) out<<", ";
                }
                out<<"]";
                return out.str();
            }
        }
        return nump->ascii();
    }

    // Checking METHODS
public:
    /// Call other-this function on all new *non-constant* var references
    virtual void varRefCb(AstVarRef* nodep) {}

    void clearOptimizable(AstNode* nodep/*null ok*/, const string& why) {
        //  Something bad found.  optimizable() will return false,
        //  and fetchConst should not be called or it may assert.
        if (!m_whyNotNodep) {
            m_whyNotNodep = nodep;
            if (debug()>=5) {
                UINFO(0,"Clear optimizable: "<<why);
                if (nodep) cout<<": "<<nodep;
                cout<<endl;
            }
            m_whyNotOptimizable = why;
            std::ostringstream stack;
            for (std::deque<SimStackNode*>::iterator it=m_callStack.begin();
                 it != m_callStack.end(); ++it) {
                AstFuncRef* funcp = (*it)->m_funcp;
                stack<<"\n        "<<funcp->fileline()
                     <<"... Called from "
                     <<funcp->prettyName()<<"() with parameters:";
                V3TaskConnects* tconnects = (*it)->m_tconnects;
                for (V3TaskConnects::iterator conIt = tconnects->begin();
                     conIt != tconnects->end(); ++conIt) {
                    AstVar* portp = conIt->first;
                    AstNode* pinp = conIt->second->exprp();
                    AstNodeDType* dtypep = pinp->dtypep();
                    stack<<"\n           "<<portp->prettyName(
                        )<<" = "<<prettyNumber(&fetchConst(pinp)->num(), dtypep);
                }
            }
            m_whyNotOptimizable += stack.str();
        }
    }
    bool optimizable() const { return m_whyNotNodep==NULL; }
    string whyNotMessage() const { return m_whyNotOptimizable; }
    AstNode* whyNotNodep() const { return m_whyNotNodep; }

    bool isAssignDly() const { return m_anyAssignDly; }
    int instrCount() const { return m_instrCount; }
    int dataCount() const { return m_dataCount; }

    // Simulation METHODS
private:
    AstConst* allocConst(AstNode* nodep) {
        // Save time - kept a list of allocated but unused values
        // It would be more efficient to do this by size, but the extra accounting
        // slows things down more than we gain.
        AstConst* constp;
        AstNodeDType* dtypep = nodep->dtypep();
        if (!m_constFreeps[dtypep].empty()) {
            //UINFO(7,"Num Reuse "<<nodep->width()<<endl);
            constp = m_constFreeps[dtypep].back(); m_constFreeps[dtypep].pop_back();
            constp->num().nodep(nodep);
        } else {
            //UINFO(7,"Num New "<<nodep->width()<<endl);
            constp = new AstConst(nodep->fileline(), AstConst::DtypedValue(), nodep->dtypep(), 0);
            m_constAllps[constp->dtypep()].push_back(constp);
        }
        constp->num().isDouble(nodep->isDouble());
        constp->num().isString(nodep->isString());
        return constp;
    }
private:
    AstConst* newValue(AstNode* nodep) {
        // Set a constant value for this node
        if (!nodep->user3p()) {
            AstConst* constp = allocConst(nodep);
            setValue(nodep, constp);
            return constp;
        } else {
            return fetchConst(nodep);
        }
    }
    AstConst* newOutValue(AstNode* nodep) {
        // Set a constant value for this node
        if (!nodep->user2p()) {
            AstConst* constp = allocConst(nodep);
            setOutValue(nodep, constp);
            return constp;
        } else {
            return fetchOutConst(nodep);
        }
    }
    void newOutValue(AstNode* nodep, const AstConst* constr) {
        newOutValue(nodep)->num().opAssign(constr->num());
    }
    AstConst* fetchConstNull(AstNode* nodep) {
        return ((AstConst*)nodep->user3p());
    }
    AstConst* fetchOutConstNull(AstNode* nodep) {
        return ((AstConst*)nodep->user2p());
    }
    AstConst* fetchConst(AstNode* nodep) {
        AstConst* constp = fetchConstNull(nodep);
        UASSERT_OBJ(constp, nodep, "No value found for node.");
        //UINFO(9,"     fetch num "<<*constp<<" on "<<nodep<<endl);
        return constp;
    }
    AstConst* fetchOutConst(AstNode* nodep) {
        AstConst* constp = fetchOutConstNull(nodep);
        UASSERT_OBJ(constp, nodep, "No value found for node.");
        return constp;
    }
public:
    void newValue(AstNode* nodep, const AstConst* constp) {
        newValue(nodep)->num().opAssign(constp->num());
    }
    V3Number* fetchNumberNull(AstNode* nodep) {
        AstConst* constp = fetchConstNull(nodep);
        if (constp) {
            return &constp->num();
        }
        return NULL;
    }
    V3Number* fetchOutNumberNull(AstNode* nodep) {
        AstConst* constp = fetchOutConstNull(nodep);
        if (constp) {
            return &constp->num();
        }
        return NULL;
    }
private:
    void setValue(AstNode* nodep, const AstConst* constp) {
        UINFO(9,"     set num "<<constp->name()<<" on "<<nodep<<endl);
        nodep->user3p((void*)constp);
    }
    void setOutValue(AstNode* nodep, const AstConst* constp) {
        UINFO(9,"     set onum "<<constp->name()<<" on "<<nodep<<endl);
        nodep->user2p((void*)constp);
    }

    void checkNodeInfo(AstNode* nodep) {
        if (m_checkOnly) {
            m_instrCount += nodep->instrCount();
            m_dataCount += nodep->width();
        }
        if (!nodep->isPredictOptimizable()) {
            //UINFO(9,"     !predictopt "<<nodep<<endl);
            clearOptimizable(nodep, "Isn't predictable");
        }
    }

    void badNodeType(AstNode* nodep) {
        // Call for default node types, or other node types we don't know how to handle
        checkNodeInfo(nodep);
        if (optimizable()) {
            // Hmm, what is this then?
            // In production code, we'll just not optimize.  It should be fixed though.
            clearOptimizable(nodep, "Unknown node type, perhaps missing visitor in SimulateVisitor");
#ifdef VL_DEBUG
            UINFO(0,"Unknown node type in SimulateVisitor: "<<nodep->prettyTypeName()<<endl);
#endif
        }
    }

    AstNode* varOrScope(AstVarRef* nodep) {
        AstNode* vscp;
        if (m_scoped) vscp = nodep->varScopep();
        else vscp = nodep->varp();
        UASSERT_OBJ(vscp, nodep, "Not linked");
        return vscp;
    }
    int unrollCount() {
        return m_params ? v3Global.opt.unrollCount()*16
            : v3Global.opt.unrollCount();
    }
    bool jumpingOver(AstNode* nodep) {
        // True to jump over this node - all visitors must call this up front
        return (m_jumpp && m_jumpp->labelp()!=nodep);
    }
    void assignOutValue(AstNodeAssign* nodep, AstNode* vscp, const AstConst* valuep) {
        if (VN_IS(nodep, AssignDly)) {
            // Don't do setValue, as value isn't yet visible to following statements
            newOutValue(vscp, valuep);
        } else {
            newValue(vscp, valuep);
            newOutValue(vscp, valuep);
        }
    }

    // VISITORS
    virtual void visit(AstAlways* nodep) {
        if (jumpingOver(nodep)) return;
        checkNodeInfo(nodep);
        iterateChildren(nodep);
    }
    virtual void visit(AstSenTree* nodep) {
        // Sensitivities aren't inputs per se; we'll keep our tree under the same sens.
    }
    virtual void visit(AstVarRef* nodep) {
        if (jumpingOver(nodep)) return;
        if (!optimizable()) return;  // Accelerate
        UASSERT_OBJ(nodep->varp(), nodep, "Unlinked");
        iterateChildren(nodep->varp());
        AstNode* vscp = varOrScope(nodep);

        // We can't have non-delayed assignments with same value on LHS and RHS
        // as we don't figure out variable ordering.
        // Delayed is OK though, as we'll decode the next state separately.
        if (!VN_IS(nodep->varp()->dtypeSkipRefp(), BasicDType)
            && !VN_IS(nodep->varp()->dtypeSkipRefp(), PackArrayDType)
            && !VN_IS(nodep->varp()->dtypeSkipRefp(), StructDType))
            clearOptimizable(nodep, "Array references/not basic");
        if (nodep->lvalue()) {
            if (m_inDlyAssign) {
                if (!(vscp->user1() & VU_LVDLY)) {
                    vscp->user1( vscp->user1() | VU_LVDLY);
                    if (m_checkOnly) varRefCb(nodep);
                }
            } else {  // nondly asn
                if (!(vscp->user1() & VU_LV)) {
                    if (!m_params && (vscp->user1() & VU_RV)) {
                        clearOptimizable(nodep, "Var read & write");
                    }
                    vscp->user1( vscp->user1() | VU_LV);
                    if (m_checkOnly) varRefCb(nodep);
                }
            }
        } else {
            if (!(vscp->user1() & VU_RV)) {
                if (!m_params && (vscp->user1() & VU_LV)) {
                    clearOptimizable(nodep, "Var write & read");
                }
                vscp->user1( vscp->user1() | VU_RV);
                bool isConst = nodep->varp()->isParam();
                AstConst* constp = isConst ? fetchConstNull(nodep->varp()->valuep()) : NULL;
                if (isConst && constp) {  // Propagate PARAM constants for constant function analysis
                    if (!m_checkOnly && optimizable()) {
                        newValue(vscp, constp);
                    }
                } else {
                    if (m_checkOnly) varRefCb(nodep);
                }
            }
        }
        if (!m_checkOnly && optimizable()) {  // simulating
            UASSERT_OBJ(!nodep->lvalue(), nodep,
                        "LHS varref should be handled in AstAssign visitor.");
            {
                // Return simulation value - copy by reference instead of value for speed
                AstConst* constp = fetchConstNull(vscp);
                if (!constp) {
                    if (m_params) {
                        clearOptimizable(nodep, "Language violation: reference to non-function-local variable");
                    } else {
                        nodep->v3fatalSrc("Variable value should have been set before any visitor called.");
                    }
                    constp = allocConst(nodep);  // Any value; just so recover from error
                }
                setValue(nodep, constp);
            }
        }
    }
    virtual void visit(AstVarXRef* nodep) {
        if (jumpingOver(nodep)) return;
        if (m_scoped) { badNodeType(nodep); return; }
        else { clearOptimizable(nodep, "Language violation: Dotted hierarchical references not allowed in constant functions"); }
    }
    virtual void visit(AstNodeFTask* nodep) {
        if (jumpingOver(nodep)) return;
        if (!m_params) { badNodeType(nodep); return; }
        if (nodep->dpiImport()) {
            clearOptimizable(nodep, "DPI import functions aren't simulatable");
        }
        checkNodeInfo(nodep);
        iterateChildren(nodep);
    }
    virtual void visit(AstNodeIf* nodep) {
        if (jumpingOver(nodep)) return;
        UINFO(5,"   IF "<<nodep<<endl);
        checkNodeInfo(nodep);
        if (m_checkOnly) {
            iterateChildren(nodep);
        } else {
            iterateAndNextNull(nodep->condp());
            if (optimizable()) {
                if (fetchConst(nodep->condp())->num().isNeqZero()) {
                    iterateAndNextNull(nodep->ifsp());
                } else {
                    iterateAndNextNull(nodep->elsesp());
                }
            }
        }
    }
    virtual void visit(AstConst* nodep) {
        checkNodeInfo(nodep);
        if (!m_checkOnly && optimizable()) {
            newValue(nodep, nodep);
        }
    }
    virtual void visit(AstEnumItemRef* nodep) {
        checkNodeInfo(nodep);
        UASSERT_OBJ(nodep->itemp(), nodep, "Not linked");
        if (!m_checkOnly && optimizable()) {
            AstNode* valuep = nodep->itemp()->valuep();
            if (valuep) {
                iterateAndNextNull(valuep);
                if (optimizable()) {
                    newValue(nodep, fetchConst(valuep));
                }
            } else {
                clearOptimizable(nodep, "No value found for enum item");
            }
        }
    }
    virtual void visit(AstNodeUniop* nodep) {
        if (!optimizable()) return;  // Accelerate
        checkNodeInfo(nodep);
        iterateChildren(nodep);
        if (!m_checkOnly && optimizable()) {
            nodep->numberOperate(newValue(nodep)->num(),
                                 fetchConst(nodep->lhsp())->num());
        }
    }
    virtual void visit(AstNodeBiop* nodep) {
        if (!optimizable()) return;  // Accelerate
        checkNodeInfo(nodep);
        iterateChildren(nodep);
        if (!m_checkOnly && optimizable()) {
            nodep->numberOperate(newValue(nodep)->num(),
                                 fetchConst(nodep->lhsp())->num(),
                                 fetchConst(nodep->rhsp())->num());
        }
    }
    virtual void visit(AstNodeTriop* nodep) {
        if (!optimizable()) return;  // Accelerate
        checkNodeInfo(nodep);
        iterateChildren(nodep);
        if (!m_checkOnly && optimizable()) {
            nodep->numberOperate(newValue(nodep)->num(),
                                 fetchConst(nodep->lhsp())->num(),
                                 fetchConst(nodep->rhsp())->num(),
                                 fetchConst(nodep->thsp())->num());
        }
    }
    virtual void visit(AstLogAnd* nodep) {
        // Need to short circuit
        if (!optimizable()) return;  // Accelerate
        checkNodeInfo(nodep);
        if (m_checkOnly) {
            iterateChildren(nodep);
        } else {
            iterate(nodep->lhsp());
            if (optimizable()) {
                if (fetchConst(nodep->lhsp())->num().isNeqZero()) {
                    iterate(nodep->rhsp());
                    newValue(nodep, fetchConst(nodep->rhsp()));
                } else {
                    newValue(nodep, fetchConst(nodep->lhsp()));  // a zero
                }
            }
        }
    }
    virtual void visit(AstLogOr* nodep) {
        // Need to short circuit
        if (!optimizable()) return;  // Accelerate
        checkNodeInfo(nodep);
        if (m_checkOnly) {
            iterateChildren(nodep);
        } else {
            iterate(nodep->lhsp());
            if (optimizable()) {
                if (fetchConst(nodep->lhsp())->num().isNeqZero()) {
                    newValue(nodep, fetchConst(nodep->lhsp()));  // a one
                } else {
                    iterate(nodep->rhsp());
                    newValue(nodep, fetchConst(nodep->rhsp()));
                }
            }
        }
    }
    virtual void visit(AstLogIf* nodep) {
        // Need to short circuit, same as (!A || B)
        if (!optimizable()) return;  // Accelerate
        checkNodeInfo(nodep);
        if (m_checkOnly) {
            iterateChildren(nodep);
        } else {
            iterate(nodep->lhsp());
            if (optimizable()) {
                if (fetchConst(nodep->lhsp())->num().isEqZero()) {
                    AstConst cnst(nodep->fileline(), AstConst::WidthedValue(), 1, 1);  // a one
                    newValue(nodep, &cnst);  // a one
                } else {
                    iterate(nodep->rhsp());
                    newValue(nodep, fetchConst(nodep->rhsp()));
                }
            }
        }
    }
    virtual void visit(AstNodeCond* nodep) {
        // We could use above visit(AstNodeTriop), but need to do short circuiting.
        // It's also slower even O(n^2) to evaluate both sides when we
        // really only need to evaluate one side.
        if (!optimizable()) return;  // Accelerate
        checkNodeInfo(nodep);
        if (m_checkOnly) {
            iterateChildren(nodep);
        } else {
            iterate(nodep->condp());
            if (optimizable()) {
                if (fetchConst(nodep->condp())->num().isNeqZero()) {
                    iterate(nodep->expr1p());
                    newValue(nodep, fetchConst(nodep->expr1p()));
                } else {
                    iterate(nodep->expr2p());
                    newValue(nodep, fetchConst(nodep->expr2p()));
                }
            }
        }
    }

    void handleAssignSel(AstNodeAssign* nodep, AstSel* selp) {
        AstVarRef* varrefp = NULL;
        V3Number lsb(nodep);
        iterateAndNextNull(nodep->rhsp());  // Value to assign
        handleAssignSelRecurse(nodep, selp, varrefp/*ref*/, lsb/*ref*/, 0);
        if (!m_checkOnly && optimizable()) {
            UASSERT_OBJ(varrefp, nodep,
                        "Indicated optimizable, but no variable found on RHS of select");
            AstNode* vscp = varOrScope(varrefp);
            AstConst* outconst = NULL;
            if (AstConst* vscpnump = fetchOutConstNull(vscp)) {
                outconst = vscpnump;
            } else if (AstConst* vscpnump = fetchConstNull(vscp)) {
                outconst = vscpnump;
            } else {  // Assignment to unassigned variable, all bits are X or 0
                outconst = new AstConst(nodep->fileline(), AstConst::WidthedValue(), varrefp->varp()->widthMin(), 0);
                if (varrefp->varp()->basicp() && varrefp->varp()->basicp()->isZeroInit()) {
                    outconst->num().setAllBits0();
                } else {
                    outconst->num().setAllBitsX();
                }
            }
            outconst->num().opSelInto(fetchConst(nodep->rhsp())->num(),
                                      lsb,
                                      selp->widthConst());
            assignOutValue(nodep, vscp, outconst);
        }
    }
    void handleAssignSelRecurse(AstNodeAssign* nodep, AstSel* selp,
                                AstVarRef*& outVarrefpRef, V3Number& lsbRef,
                                int depth) {
        // Recurse down to find final variable being set (outVarrefp), with
        // value to write on nodep->rhsp()
        checkNodeInfo(selp);
        iterateAndNextNull(selp->lsbp());  // Bit index
        if (AstVarRef* varrefp = VN_CAST(selp->fromp(), VarRef)) {
            outVarrefpRef = varrefp;
            lsbRef = fetchConst(selp->lsbp())->num();
            return;  // And presumably still optimizable()
        } else if (AstSel* subselp = VN_CAST(selp->lhsp(), Sel)) {
            V3Number sublsb(nodep);
            handleAssignSelRecurse(nodep, subselp, outVarrefpRef, sublsb/*ref*/, depth+1);
            if (optimizable()) {
                lsbRef = sublsb;
                lsbRef.opAdd(sublsb, fetchConst(selp->lsbp())->num());
            }
        } else {
            clearOptimizable(nodep, "Select LHS isn't simple variable");
        }
    }

    virtual void visit(AstNodeAssign* nodep) {
        if (jumpingOver(nodep)) return;
        if (!optimizable()) return;  // Accelerate
        if (VN_IS(nodep, AssignDly)) {
            if (m_anyAssignComb) clearOptimizable(nodep, "Mix of dly/non-dly assigns");
            m_anyAssignDly = true;
            m_inDlyAssign = true;
        } else {
            if (m_anyAssignDly) clearOptimizable(nodep, "Mix of dly/non-dly assigns");
            m_anyAssignComb = true;
        }

        if (AstSel* selp = VN_CAST(nodep->lhsp(), Sel)) {
            if (!m_params) { clearOptimizable(nodep, "LHS has select"); return; }
            handleAssignSel(nodep, selp);
        }
        else if (!VN_IS(nodep->lhsp(), VarRef)) {
            clearOptimizable(nodep, "LHS isn't simple variable");
        }
        else if (m_checkOnly) {
            iterateChildren(nodep);
        }
        else if (optimizable()) {
            iterateAndNextNull(nodep->rhsp());
            if (optimizable()) {
                AstNode* vscp = varOrScope(VN_CAST(nodep->lhsp(), VarRef));
                assignOutValue(nodep, vscp, fetchConst(nodep->rhsp()));
            }
        }
        m_inDlyAssign = false;
    }
    virtual void visit(AstBegin* nodep) {
        checkNodeInfo(nodep);
        iterateChildren(nodep);
    }
    virtual void visit(AstNodeCase* nodep) {
        if (jumpingOver(nodep)) return;
        UINFO(5,"   CASE "<<nodep<<endl);
        checkNodeInfo(nodep);
        if (m_checkOnly) {
            iterateChildren(nodep);
        } else if (optimizable()) {
            iterateAndNextNull(nodep->exprp());
            bool hit = false;
            for (AstCaseItem* itemp = nodep->itemsp();
                 itemp; itemp=VN_CAST(itemp->nextp(), CaseItem)) {
                if (!itemp->isDefault()) {
                    for (AstNode* ep = itemp->condsp(); ep; ep=ep->nextp()) {
                        if (hit) break;
                        iterateAndNextNull(ep);
                        if (optimizable()) {
                            V3Number match (nodep, 1);
                            match.opEq(fetchConst(nodep->exprp())->num(), fetchConst(ep)->num());
                            if (match.isNeqZero()) {
                                iterateAndNextNull(itemp->bodysp());
                                hit = true;
                            }
                        }
                    }
                }
            }
            // Else default match
            for (AstCaseItem* itemp = nodep->itemsp();
                 itemp; itemp = VN_CAST(itemp->nextp(), CaseItem)) {
                if (hit) break;
                if (!hit && itemp->isDefault()) {
                    iterateAndNextNull(itemp->bodysp());
                    hit = true;
                }
            }
        }
    }

    virtual void visit(AstCaseItem* nodep) {
        // Real handling is in AstNodeCase
        if (jumpingOver(nodep)) return;
        checkNodeInfo(nodep);
        iterateChildren(nodep);
    }

    virtual void visit(AstComment*) {}

    virtual void visit(AstJumpGo* nodep) {
        if (jumpingOver(nodep)) return;
        checkNodeInfo(nodep);
        if (!m_checkOnly) {
            UINFO(5,"   JUMP GO "<<nodep<<endl);
            m_jumpp = nodep;
        }
    }
    virtual void visit(AstJumpLabel* nodep) {
        if (jumpingOver(nodep)) return;
        checkNodeInfo(nodep);
        iterateChildren(nodep);
        if (m_jumpp && m_jumpp->labelp() == nodep) {
            UINFO(5,"   JUMP DONE "<<nodep<<endl);
            m_jumpp = NULL;
        }
    }
    virtual void visit(AstStop* nodep) {
        if (jumpingOver(nodep)) return;
        if (m_params) {  // This message seems better than an obscure $stop
            // The spec says $stop is just ignored, it seems evil to ignore assertions
            clearOptimizable(nodep, "$stop executed during function constification; maybe indicates assertion firing");
        }
        checkNodeInfo(nodep);
    }

    virtual void visit(AstNodeFor* nodep) {
        // Doing lots of Whiles is slow, so only for parameters
        UINFO(5,"   FOR "<<nodep<<endl);
        if (!m_params) { badNodeType(nodep); return; }
        checkNodeInfo(nodep);
        if (m_checkOnly) {
            iterateChildren(nodep);
        } else if (optimizable()) {
            int loops = 0;
            iterateAndNextNull(nodep->initsp());
            while (1) {
                UINFO(5,"    FOR-ITER "<<nodep<<endl);
                iterateAndNextNull(nodep->condp());
                if (!optimizable()) break;
                if (!fetchConst(nodep->condp())->num().isNeqZero()) {
                    break;
                }
                iterateAndNextNull(nodep->bodysp());
                iterateAndNextNull(nodep->incsp());
                if (loops++ > unrollCount()*16) {
                    clearOptimizable(nodep, "Loop unrolling took too long; probably this is an"
                                     "infinite loop, or set --unroll-count above "
                                     + cvtToStr(unrollCount()));
                    break;
                }
            }
        }
    }

    virtual void visit(AstWhile* nodep) {
        // Doing lots of Whiles is slow, so only for parameters
        if (jumpingOver(nodep)) return;
        UINFO(5,"   WHILE "<<nodep<<endl);
        if (!m_params) { badNodeType(nodep); return; }
        checkNodeInfo(nodep);
        if (m_checkOnly) {
            iterateChildren(nodep);
        } else if (optimizable()) {
            int loops = 0;
            while (1) {
                UINFO(5,"    WHILE-ITER "<<nodep<<endl);
                iterateAndNextNull(nodep->precondsp());
                if (jumpingOver(nodep)) break;
                iterateAndNextNull(nodep->condp());
                if (jumpingOver(nodep)) break;
                if (!optimizable()) break;
                if (!fetchConst(nodep->condp())->num().isNeqZero()) {
                    break;
                }
                iterateAndNextNull(nodep->bodysp());
                if (jumpingOver(nodep)) break;
                iterateAndNextNull(nodep->incsp());
                if (jumpingOver(nodep)) break;

                // Prep for next loop
                if (loops++ > unrollCount()*16) {
                    clearOptimizable(nodep, "Loop unrolling took too long; probably this is an infinite"
                                     " loop, or set --unroll-count above "+cvtToStr(unrollCount()));
                    break;
                }
            }
        }
    }

    virtual void visit(AstFuncRef* nodep) {
        if (jumpingOver(nodep)) return;
        if (!optimizable()) return;  // Accelerate
        UINFO(5,"   FUNCREF "<<nodep<<endl);
        if (!m_params) { badNodeType(nodep); return; }
        AstNodeFTask* funcp = VN_CAST(nodep->taskp(), NodeFTask);
        UASSERT_OBJ(funcp, nodep, "Not linked");
        if (m_params) { V3Width::widthParamsEdit(funcp); } VL_DANGLING(funcp);  // Make sure we've sized the function
        funcp = VN_CAST(nodep->taskp(), NodeFTask); UASSERT_OBJ(funcp, nodep, "Not linked");
        // Apply function call values to function
        V3TaskConnects tconnects = V3Task::taskConnects(nodep, nodep->taskp()->stmtsp());
        // Must do this in two steps, eval all params, then apply them
        // Otherwise chained functions may have the wrong results
        for (V3TaskConnects::iterator it=tconnects.begin(); it!=tconnects.end(); ++it) {
            AstVar* portp = it->first;
            AstNode* pinp = it->second->exprp();
            if (pinp) {  // Else too few arguments in function call - ignore it
                if (portp->isWritable()) {
                    clearOptimizable(portp, "Language violation: Outputs/refs not allowed in constant functions");
                    return;
                }
                // Evaluate pin value
                iterate(pinp);
            }
        }
        for (V3TaskConnects::iterator it=tconnects.begin(); it!=tconnects.end(); ++it) {
            AstVar* portp = it->first;
            AstNode* pinp = it->second->exprp();
            if (pinp) {  // Else too few arguments in function call - ignore it
                // Apply value to the function
                if (!m_checkOnly && optimizable()) {
                    newValue(portp, fetchConst(pinp));
                }
            }
        }
        SimStackNode stackNode(nodep, &tconnects);
        m_callStack.push_front(&stackNode);
        // Evaluate the function
        iterate(funcp);
        m_callStack.pop_front();
        if (!m_checkOnly && optimizable()) {
            // Grab return value from output variable (if it's a function)
            UASSERT_OBJ(funcp->fvarp(), nodep, "Function reference points at non-function");
            newValue(nodep, fetchConst(funcp->fvarp()));
        }
    }

    virtual void visit(AstVar* nodep) {
        if (jumpingOver(nodep)) return;
        if (!m_params) { badNodeType(nodep); return; }
    }

    virtual void visit(AstScopeName *nodep) {
        if (jumpingOver(nodep)) return;
        if (!m_params) { badNodeType(nodep); return; }
        // Ignore
    }

    virtual void visit(AstSFormatF *nodep) {
        if (jumpingOver(nodep)) return;
        if (!optimizable()) return;  // Accelerate
        iterateChildren(nodep);
        if (m_params) {
            AstNode* nextArgp = nodep->exprsp();

            string result;
            string format = nodep->text();
            string::const_iterator pos = format.begin();
            bool inPct = false;
            for (; pos != format.end(); ++pos) {
                if (!inPct && pos[0] == '%') {
                    inPct = true;
                } else if (!inPct) {  // Normal text
                    result += *pos;
                } else {  // Format character
                    inPct = false;

                    if (V3Number::displayedFmtLegal(tolower(pos[0]))) {
                        AstNode* argp = nextArgp;
                        nextArgp = nextArgp->nextp();
                        AstConst* constp = fetchConstNull(argp);
                        if (!constp) {
                            clearOptimizable(nodep, "Argument for $display like statement is not constant");
                            break;
                        }
                        string format = string("%") + pos[0];
                        result += constp->num().displayed(nodep, format);
                    } else {
                        switch (tolower(pos[0])) {
                        case '%':
                            result += "%";
                            break;
                        case 'm':
                            // This happens prior to AstScope so we don't
                            // know the scope name. Leave the %m in place.
                            result += "%m";
                            break;
                        default:
                            clearOptimizable(nodep, "Unknown $display-like format code.");
                            break;
                        }
                    }
                }
            }

            AstConst* resultConstp = new AstConst(nodep->fileline(), AstConst::String(), result);
            setValue(nodep, resultConstp);
            m_stringValuesp.push_back(resultConstp);
        }
    }

    virtual void visit(AstDisplay *nodep) {
        if (jumpingOver(nodep)) return;
        if (!optimizable()) return;  // Accelerate
        iterateChildren(nodep);
        if (m_params) {
            AstConst* textp = fetchConst(nodep->fmtp());
            switch (nodep->displayType()) {
            case AstDisplayType::DT_DISPLAY:  // FALLTHRU
            case AstDisplayType::DT_INFO:
                v3warn(USERINFO, textp->name());
                break;
            case AstDisplayType::DT_ERROR:
                v3warn(USERERROR, textp->name());
                break;
            case AstDisplayType::DT_WARNING:
                v3warn(USERWARN, textp->name());
                break;
            case AstDisplayType::DT_FATAL:
                v3warn(USERFATAL, textp->name());
                break;
            case AstDisplayType::DT_WRITE:  // FALLTHRU
            default:
                clearOptimizable(nodep, "Unexpected display type");
            }
        }
    }

    // default
    // These types are definately not reducable
    //   AstCoverInc, AstArraySel, AstFinish,
    //   AstRand, AstTime, AstUCFunc, AstCCall, AstCStmt, AstUCStmt
    virtual void visit(AstNode* nodep) {
        if (jumpingOver(nodep)) return;
        badNodeType(nodep);
    }

private:
    // MEMBERS - called by constructor
    void setMode(bool scoped, bool checkOnly, bool params) {
        m_checkOnly = checkOnly;
        m_scoped = scoped;
        m_params = params;
    }
    void mainGuts(AstNode* nodep) {
        iterate(nodep);
        UASSERT_OBJ(!m_jumpp, m_jumpp, "JumpGo branched to label that wasn't found");
    }
public:
    // CONSTRUCTORS
    SimulateVisitor() {
        // Note AstUser#InUse ensures only one invocation exists at once
        setMode(false, false, false);
        clear();  // We reuse this structure in the main loop, so put initializers inside clear()
    }
    void clear() {
        m_whyNotOptimizable = "";
        m_whyNotNodep = NULL;
        m_anyAssignComb = false;
        m_anyAssignDly = false;
        m_inDlyAssign = false;
        m_instrCount = 0;
        m_dataCount = 0;
        m_jumpp = NULL;

        AstNode::user1ClearTree();
        AstNode::user2ClearTree();
        AstNode::user3ClearTree();

        // Move all allocated numbers to the free pool
        m_constFreeps = m_constAllps;
    }
    void mainTableCheck(AstNode* nodep) {
        setMode(true/*scoped*/, true/*checking*/, false/*params*/);
        mainGuts(nodep);
    }
    void mainTableEmulate(AstNode* nodep) {
        setMode(true/*scoped*/, false/*checking*/, false/*params*/);
        mainGuts(nodep);
    }
    void mainCheckTree(AstNode* nodep) {
        setMode(false/*scoped*/, true/*checking*/, false/*params*/);
        mainGuts(nodep);
    }
    void mainParamEmulate(AstNode* nodep) {
        setMode(false/*scoped*/, false/*checking*/, true/*params*/);
        mainGuts(nodep);
    }
    virtual ~SimulateVisitor() {
        for (ConstPile::iterator it = m_constAllps.begin();
             it != m_constAllps.end(); ++it) {
            for (ConstDeque::iterator it2 = it->second.begin();
                 it2 != it->second.end(); ++it2) {
                delete (*it2);
            }
        }
        for (std::deque<AstConst*>::iterator it = m_stringValuesp.begin();
             it != m_stringValuesp.end(); ++it) {
            delete (*it);
        }
        m_stringValuesp.clear();
        m_constFreeps.clear();
        m_constAllps.clear();
    }
};

#endif  // Guard
