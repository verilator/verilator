// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Replicate modules for parameterization
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
// PARAM TRANSFORMATIONS:
//   Top down traversal:
//      For each cell:
//          If parameterized,
//              Determine all parameter widths, constant values.
//              (Interfaces also matter, as if an interface is parameterized
//              this effectively changes the width behavior of all that
//              reference the iface.)
//              Clone module cell calls, renaming with __{par1}_{par2}_...
//              Substitute constants for cell's module's parameters.
//              Relink pins and cell and ifacerefdtype to point to new module.
//
//              For interface Parent's we have the AstIfaceRefDType::cellp()
//              pointing to this module.  If that parent cell's interface
//              module gets parameterized, AstIfaceRefDType::cloneRelink
//              will update AstIfaceRefDType::cellp(), and V3LinkDot will
//              see the new interface.
//
//              However if a submodule's AstIfaceRefDType::ifacep() points
//              to the old (unparameterized) interface and needs correction.
//              To detect this we must walk all pins looking for interfaces
//              that the parent has changed and propagate down.
//
//          Then process all modules called by that cell.
//          (Cells never referenced after parameters expanded must be ignored.)
//
//   After we complete parameters, the varp's will be wrong (point to old module)
//   and must be relinked.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Param.h"
#include "V3Ast.h"
#include "V3Case.h"
#include "V3Const.h"
#include "V3Width.h"
#include "V3Unroll.h"
#include "V3Hashed.h"

#include <cstdarg>
#include <deque>
#include <map>
#include <vector>

//######################################################################
// Param state, as a visitor of each AstNode

class ParamVisitor : public AstNVisitor {
private:
    // NODE STATE
    //   AstNodeModule::user5() // bool   True if processed
    //   AstGenFor::user5()     // bool   True if processed
    //   AstVar::user5()        // bool   True if constant propagated
    //   AstVar::user4()        // int    Global parameter number (for naming new module)
    //                          //        (0=not processed, 1=iterated, but no number,
    //                          //         65+ parameter numbered)
    //   AstCell::user5p()      // string* Generate portion of hierarchical name
    AstUser4InUse       m_inuser4;
    AstUser5InUse       m_inuser5;
    // User1/2/3 used by constant function simulations

    // TYPES
    typedef std::deque<std::pair<AstIfaceRefDType*,AstIfaceRefDType*> > IfaceRefRefs;  // Note may have duplicate entries

    // STATE
    typedef std::map<AstNode*,AstNode*> CloneMap;
    struct ModInfo {
        AstNodeModule*  m_modp;         // Module with specified name
        CloneMap        m_cloneMap;     // Map of old-varp -> new cloned varp
        explicit ModInfo(AstNodeModule* modp) { m_modp = modp; }
    };
    typedef std::map<string,ModInfo> ModNameMap;
    ModNameMap  m_modNameMap;   // Hash of created module flavors by name

    typedef std::map<string,string> LongMap;
    LongMap     m_longMap;      // Hash of very long names to unique identity number
    int         m_longId;

    typedef std::pair<int,string> ValueMapValue;
    typedef std::map<V3Hash,ValueMapValue> ValueMap;
    ValueMap    m_valueMap;     // Hash of node hash to (param value, name)
    int         m_nextValue;    // Next value to use in m_valueMap

    typedef std::multimap<int,AstNodeModule*> LevelModMap;
    LevelModMap m_todoModps;    // Modules left to process

    typedef std::deque<AstCell*> CellList;
    CellList    m_cellps;       // Cells left to process (in this module)

    AstNodeModule* m_modp;  // Current module being processed

    string m_unlinkedTxt;       // Text for AstUnlinkedRef

    UnrollStateful m_unroller;  // Loop unroller

    string m_generateHierName;  // Generate portion of hierarchical name

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    void makeSmallNames(AstNodeModule* modp) {
        std::vector<int> usedLetter; usedLetter.resize(256);
        // Pass 1, assign first letter to each gparam's name
        for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp=stmtp->nextp()) {
            if (AstVar* varp = VN_CAST(stmtp, Var)) {
                if (varp->isGParam()||varp->isIfaceRef()) {
                    char ch = varp->name()[0];
                    ch = toupper(ch); if (ch<'A' || ch>'Z') ch='Z';
                    varp->user4(usedLetter[static_cast<int>(ch)]*256 + ch);
                    usedLetter[static_cast<int>(ch)]++;
                }
            } else if (AstParamTypeDType* typep = VN_CAST(stmtp, ParamTypeDType)) {
                char ch = 'T';
                typep->user4(usedLetter[static_cast<int>(ch)]*256 + ch);
                usedLetter[static_cast<int>(ch)]++;
            }
        }
    }
    string paramSmallName(AstNodeModule* modp, AstNode* varp) {
        if (varp->user4()<=1) {
            makeSmallNames(modp);
        }
        int index = varp->user4()/256;
        char ch   = varp->user4()&255;
        string st = cvtToStr(ch);
        while (index) {
            st += cvtToStr(char((index%25)+'A'));
            index /= 26;
        }
        return st;
    }
    string paramValueNumber(AstNode* nodep) {
        string key = nodep->name();
        if (AstIfaceRefDType* ifrtp = VN_CAST(nodep, IfaceRefDType)) {
            if (ifrtp->cellp() && ifrtp->cellp()->modp()) {
                key = ifrtp->cellp()->modp()->name();
            } else if (ifrtp->ifacep()) {
                key = ifrtp->ifacep()->name();
        } else {
                nodep->v3fatalSrc("Can't parameterize interface without module name");
            }
        } else if (AstBasicDType* bdtp = VN_CAST(nodep, BasicDType)) {
            if (bdtp->isRanged()) {
                key += "["+cvtToStr(bdtp->left())+":"+cvtToStr(bdtp->right())+"]";
            }
        }
        V3Hash hash = V3Hashed::uncachedHash(nodep);
        // Force hash collisions -- for testing only
        if (VL_UNLIKELY(v3Global.opt.debugCollision())) {
            hash = V3Hash();
        }
        int num;
        ValueMap::iterator it = m_valueMap.find(hash);
        if (it != m_valueMap.end() && it->second.second == key) {
            num = it->second.first;
        } else {
            num = m_nextValue++;
            m_valueMap[hash] = make_pair(num, key);
        }
        return string("z")+cvtToStr(num);
    }
    void collectPins(CloneMap* clonemapp, AstNodeModule* modp) {
        // Grab all I/O so we can remap our pins later
        for (AstNode* stmtp=modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVar* varp = VN_CAST(stmtp, Var)) {
                if (varp->isIO() || varp->isGParam() || varp->isIfaceRef()) {
                    // Cloning saved a pointer to the new node for us, so just follow that link.
                    AstVar* oldvarp = varp->clonep();
                    //UINFO(8,"Clone list 0x"<<hex<<(uint32_t)oldvarp<<" -> 0x"<<(uint32_t)varp<<endl);
                    clonemapp->insert(make_pair(oldvarp, varp));
                }
            }
            else if (AstParamTypeDType* ptp = VN_CAST(stmtp, ParamTypeDType)) {
                if (ptp->isGParam()) {
                    AstParamTypeDType* oldptp = ptp->clonep();
                    clonemapp->insert(make_pair(oldptp, ptp));
                }
            }
        }
    }
    void relinkPins(CloneMap* clonemapp, AstPin* startpinp) {
        for (AstPin* pinp = startpinp; pinp; pinp=VN_CAST(pinp->nextp(), Pin)) {
            if (pinp->modVarp()) {
                // Find it in the clone structure
                //UINFO(8,"Clone find 0x"<<hex<<(uint32_t)pinp->modVarp()<<endl);
                CloneMap::iterator cloneiter = clonemapp->find(pinp->modVarp());
                UASSERT_OBJ(cloneiter != clonemapp->end(), pinp,
                            "Couldn't find pin in clone list");
                pinp->modVarp(VN_CAST(cloneiter->second, Var));
            }
            else if (pinp->modPTypep()) {
                CloneMap::iterator cloneiter = clonemapp->find(pinp->modPTypep());
                UASSERT_OBJ(cloneiter != clonemapp->end(), pinp,
                            "Couldn't find pin in clone list");
                pinp->modPTypep(VN_CAST(cloneiter->second, ParamTypeDType));
            }
            else {
                pinp->v3fatalSrc("Not linked?");
            }
        }
    }
    void visitCell(AstCell* nodep, const string& hierName);
    void visitModules() {
        // Loop on all modules left to process
        // Hitting a cell adds to the appropriate level of this level-sorted list,
        // so since cells originally exist top->bottom we process in top->bottom order too.
        while (!m_todoModps.empty()) {
            LevelModMap::iterator itm = m_todoModps.begin();
            AstNodeModule* nodep = itm->second;
            m_todoModps.erase(itm);
            if (!nodep->user5SetOnce()) {  // Process once; note clone() must clear so we do it again
                m_modp = nodep;
                UINFO(4," MOD   "<<nodep<<endl);
                if (m_modp->hierName().empty()) m_modp->hierName(m_modp->origName());
                iterateChildren(nodep);
                // Note above iterate may add to m_todoModps
                //
                // Process interface cells, then non-interface which may ref an interface cell
                for (int nonIf=0; nonIf<2; ++nonIf) {
                    for (CellList::iterator it=m_cellps.begin(); it!=m_cellps.end(); ++it) {
                        AstCell* nodep = *it;
                        if ((nonIf==0 && VN_IS(nodep->modp(), Iface))
                            || (nonIf==1 && !VN_IS(nodep->modp(), Iface))) {
                            string fullName (m_modp->hierName());
                            if (string* genHierNamep = (string *) nodep->user5p()) {
                                fullName += *genHierNamep;
                            }
                            visitCell(nodep, fullName);
                        }
                    }
                }
                for (CellList::iterator it=m_cellps.begin(); it!=m_cellps.end(); ++it) {
                    AstCell* cellp = *it;
                    if (string* genHierNamep = (string *) cellp->user5p()) {
                        cellp->user5p(NULL);
                        VL_DO_DANGLING(delete genHierNamep, genHierNamep);
                    }
                }
                m_cellps.clear();
                m_modp = NULL;
            }
        }
    }

    // VISITORS
    virtual void visit(AstNetlist* nodep) VL_OVERRIDE {
        // Modules must be done in top-down-order
        iterateChildren(nodep);
    }
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        if (nodep->dead()) {
            UINFO(4," MOD-dead.  "<<nodep<<endl);  // Marked by LinkDot
        } else if (nodep->recursiveClone()) {
            UINFO(4," MOD-recursive-dead.  "<<nodep<<endl);  // Fake, made for recursive elimination
            nodep->dead(true);  // So Dead checks won't count references to it
        } else if (nodep->level() <= 2  // Haven't added top yet, so level 2 is the top
                   || VN_IS(nodep, Package)) {  // Likewise haven't done wrapTopPackages yet
            // Add request to END of modules left to process
            m_todoModps.insert(make_pair(nodep->level(), nodep));
            m_generateHierName = "";
            visitModules();
        } else if (nodep->user5()) {
            UINFO(4," MOD-done   "<<nodep<<endl);  // Already did it
        } else {
            UINFO(4," MOD-dead?  "<<nodep<<endl);  // Should have been done by now, if not dead
        }
    }
    virtual void visit(AstCell* nodep) VL_OVERRIDE {
        // Must do ifaces first, so push to list and do in proper order
        string* genHierNamep = new string(m_generateHierName);
        nodep->user5p(genHierNamep);
        m_cellps.push_back(nodep);
    }

    // Make sure all parameters are constantified
    virtual void visit(AstVar* nodep) VL_OVERRIDE {
        if (!nodep->user5SetOnce()) {  // Process once
            iterateChildren(nodep);
            if (nodep->isParam()) {
                if (!nodep->valuep()) {
                    nodep->v3error("Parameter without initial value is never given value"
                                   <<" (IEEE 1800-2017 6.20.1): "
                                   <<nodep->prettyNameQ());
                } else {
                    V3Const::constifyParamsEdit(nodep);  // The variable, not just the var->init()
                    if (!VN_IS(nodep->valuep(), Const)) {  // Complex init, like an array
                        // Make a new INITIAL to set the value.
                        // This allows the normal array/struct handling code to properly
                        // initialize the parameter.
                        nodep->addNext(
                            new AstInitial(nodep->fileline(),
                                           new AstAssign(
                                               nodep->fileline(),
                                               new AstVarRef(nodep->fileline(), nodep, true),
                                               nodep->valuep()->cloneTree(true))));
                    }
                }
            }
        }
    }
    // Make sure varrefs cause vars to constify before things above
    virtual void visit(AstVarRef* nodep) VL_OVERRIDE {
        if (nodep->varp()) iterate(nodep->varp());
    }
    bool ifaceParamReplace(AstVarXRef* nodep, AstNode* candp) {
        for (; candp; candp = candp->nextp()) {
            if (nodep->name() == candp->name()) {
                if (AstVar* varp = VN_CAST(candp, Var)) {
                    UINFO(9,"Found interface parameter: "<<varp<<endl);
                    nodep->varp(varp);
                    return true;
                } else if (AstPin* pinp = VN_CAST(candp, Pin)) {
                    UINFO(9,"Found interface parameter: "<<pinp<<endl);
                    UASSERT_OBJ(pinp->exprp(), pinp, "Interface parameter pin missing expression");
                    VL_DO_DANGLING(nodep->replaceWith(pinp->exprp()->cloneTree(false)), nodep);
                    return true;
                }
            }
        }
        return false;
    }
    virtual void visit(AstVarXRef* nodep) VL_OVERRIDE {
        // Check to see if the scope is just an interface because interfaces are special
        string dotted = nodep->dotted();
        if (!dotted.empty() && nodep->varp() && nodep->varp()->isParam()) {
            AstNode* backp = nodep;
            while ((backp = backp->backp())) {
                if (VN_IS(backp, NodeModule)) {
                    UINFO(9,"Hit module boundary, done looking for interface"<<endl);
                    break;
                }
                if (VN_IS(backp, Var)
                    && VN_CAST(backp, Var)->isIfaceRef()
                    && VN_CAST(backp, Var)->childDTypep()
                    && (VN_CAST(VN_CAST(backp, Var)->childDTypep(), IfaceRefDType)
                        || (VN_CAST(VN_CAST(backp, Var)->childDTypep(), UnpackArrayDType)
                            && VN_CAST(VN_CAST(backp, Var)->childDTypep()->getChildDTypep(),
                                       IfaceRefDType)))) {
                    AstIfaceRefDType* ifacerefp
                        = VN_CAST(VN_CAST(backp, Var)->childDTypep(), IfaceRefDType);
                    if (!ifacerefp) {
                        ifacerefp = VN_CAST(VN_CAST(backp, Var)->childDTypep()->getChildDTypep(),
                                            IfaceRefDType);
                    }
                    // Interfaces passed in on the port map have ifaces
                    if (AstIface* ifacep = ifacerefp->ifacep()) {
                        if (dotted == backp->name()) {
                            UINFO(9,"Iface matching scope:  "<<ifacep<<endl);
                            if (ifaceParamReplace(nodep, ifacep->stmtsp())) {
                                return;
                            }
                        }
                    }
                    // Interfaces declared in this module have cells
                    else if (AstCell* cellp = ifacerefp->cellp()) {
                        if (dotted == cellp->name()) {
                            UINFO(9,"Iface matching scope:  "<<cellp<<endl);
                            if (ifaceParamReplace(nodep, cellp->paramsp())) {
                                return;
                            }
                        }
                    }
                }
            }
        }
        nodep->varp(NULL);  // Needs relink, as may remove pointed-to var
    }

    virtual void visit(AstUnlinkedRef* nodep) VL_OVERRIDE {
        AstVarXRef* varxrefp = VN_CAST(nodep->op1p(), VarXRef);
        AstNodeFTaskRef* taskrefp = VN_CAST(nodep->op1p(), NodeFTaskRef);
        if (varxrefp) {
            m_unlinkedTxt = varxrefp->dotted();
        } else if (taskrefp) {
            m_unlinkedTxt = taskrefp->dotted();
        } else {
            nodep->v3fatalSrc("Unexpected AstUnlinkedRef node");
            return;
        }
        iterate(nodep->cellrefp());

        if (varxrefp) {
            varxrefp->dotted(m_unlinkedTxt);
        } else {
            taskrefp->dotted(m_unlinkedTxt);
        }
        nodep->replaceWith(nodep->op1p()->unlinkFrBack());
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    virtual void visit(AstCellArrayRef* nodep) VL_OVERRIDE {
        V3Const::constifyParamsEdit(nodep->selp());
        if (const AstConst* constp = VN_CAST(nodep->selp(), Const)) {
            string index = AstNode::encodeNumber(constp->toSInt());
            string replacestr = nodep->name() + "__BRA__??__KET__";
            size_t pos = m_unlinkedTxt.find(replacestr);
            if (pos == string::npos) {
                nodep->v3error("Could not find array index in unlinked text: '"
                               <<m_unlinkedTxt<<"' for node: "<<nodep);
                return;
            }
            m_unlinkedTxt.replace(pos, replacestr.length(),
                                  nodep->name()+"__BRA__"+index+"__KET__");
        } else {
            nodep->v3error("Could not expand constant selection inside dotted reference: "
                           <<nodep->selp()->prettyNameQ());
            return;
        }
    }

    // Generate Statements
    virtual void visit(AstGenIf* nodep) VL_OVERRIDE {
        UINFO(9,"  GENIF "<<nodep<<endl);
        iterateAndNextNull(nodep->condp());
        // We suppress errors when widthing params since short-circuiting in
        // the conditional evaluation may mean these error can never occur. We
        // then make sure that short-circuiting is used by constifyParamsEdit.
        V3Width::widthGenerateParamsEdit(nodep);  // Param typed widthing will
                                                  // NOT recurse the body.
        V3Const::constifyGenerateParamsEdit(nodep->condp());  // condp may change
        if (const AstConst* constp = VN_CAST(nodep->condp(), Const)) {
            AstNode* keepp = (constp->isZero()
                              ? nodep->elsesp()
                              : nodep->ifsp());
            if (keepp) {
                keepp->unlinkFrBackWithNext();
                nodep->replaceWith(keepp);
            } else {
                nodep->unlinkFrBack();
            }
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            // Normal edit rules will now recurse the replacement
        } else {
            nodep->condp()->v3error("Generate If condition must evaluate to constant");
        }
    }

    //! Parameter substitution for generated for loops.
    //! @todo Unlike generated IF, we don't have to worry about short-circuiting the conditional
    //!       expression, since this is currently restricted to simple comparisons. If we ever do
    //!       move to more generic constant expressions, such code will be needed here.
    virtual void visit(AstBegin* nodep) VL_OVERRIDE {
        if (nodep->genforp()) {
            AstGenFor* forp = VN_CAST(nodep->genforp(), GenFor);
            UASSERT_OBJ(forp, nodep, "Non-GENFOR under generate-for BEGIN");
            // We should have a GENFOR under here.  We will be replacing the begin,
            // so process here rather than at the generate to avoid iteration problems
            UINFO(9,"  BEGIN "<<nodep<<endl);
            UINFO(9,"  GENFOR "<<forp<<endl);
            V3Width::widthParamsEdit(forp);  // Param typed widthing will NOT recurse the body
            // Outer wrapper around generate used to hold genvar, and to ensure genvar
            // doesn't conflict in V3LinkDot resolution with other genvars
            // Now though we need to change BEGIN("zzz", GENFOR(...)) to
            // a BEGIN("zzz__BRA__{loop#}__KET__")
            string beginName = nodep->name();
            // Leave the original Begin, as need a container for the (possible) GENVAR
            // Note V3Unroll will replace some AstVarRef's to the loop variable with constants
            // Don't remove any deleted nodes in m_unroller until whole process finishes,
            // (are held in m_unroller), as some AstXRefs may still point to old nodes.
            VL_DO_DANGLING(m_unroller.unrollGen(forp, beginName), forp);
            // Blocks were constructed under the special begin, move them up
            // Note forp is null, so grab statements again
            if (AstNode* stmtsp = nodep->genforp()) {
                stmtsp->unlinkFrBackWithNext();
                nodep->addNextHere(stmtsp);
                // Note this clears nodep->genforp(), so begin is no longer special
            }
        } else {
            string rootHierName(m_generateHierName);
            m_generateHierName += "." + nodep->prettyName();
            iterateChildren(nodep);
            m_generateHierName = rootHierName;
        }
    }
    virtual void visit(AstGenFor* nodep) VL_OVERRIDE {
        nodep->v3fatalSrc("GENFOR should have been wrapped in BEGIN");
    }
    virtual void visit(AstGenCase* nodep) VL_OVERRIDE {
        UINFO(9,"  GENCASE "<<nodep<<endl);
        AstNode* keepp = NULL;
        iterateAndNextNull(nodep->exprp());
        V3Case::caseLint(nodep);
        V3Width::widthParamsEdit(nodep);  // Param typed widthing will NOT recurse the body,
                                          // don't trigger errors yet.
        V3Const::constifyParamsEdit(nodep->exprp());  // exprp may change
        AstConst* exprp = VN_CAST(nodep->exprp(), Const);
        // Constify
        for (AstCaseItem* itemp = nodep->itemsp();
             itemp; itemp = VN_CAST(itemp->nextp(), CaseItem)) {
            for (AstNode* ep = itemp->condsp(); ep; ) {
                AstNode* nextp = ep->nextp();  // May edit list
                iterateAndNextNull(ep);
                VL_DO_DANGLING(V3Const::constifyParamsEdit(ep), ep);  // ep may change
                ep = nextp;
            }
        }
        // Item match
        for (AstCaseItem* itemp = nodep->itemsp();
             itemp; itemp = VN_CAST(itemp->nextp(), CaseItem)) {
            if (!itemp->isDefault()) {
                for (AstNode* ep = itemp->condsp(); ep; ep=ep->nextp()) {
                    if (const AstConst* ccondp = VN_CAST(ep, Const)) {
                        V3Number match (nodep, 1);
                        match.opEq(ccondp->num(), exprp->num());
                        if (!keepp && match.isNeqZero()) {
                            keepp = itemp->bodysp();
                        }
                    } else {
                        itemp->v3error("Generate Case item does not evaluate to constant");
                    }
                }
            }
        }
        // Else default match
        for (AstCaseItem* itemp = nodep->itemsp();
             itemp; itemp = VN_CAST(itemp->nextp(), CaseItem)) {
            if (itemp->isDefault()) {
                if (!keepp) keepp = itemp->bodysp();
            }
        }
        // Replace
        if (keepp) {
            keepp->unlinkFrBackWithNext();
            nodep->replaceWith(keepp);
        }
        else nodep->unlinkFrBack();
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }

    // Default: Just iterate
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit ParamVisitor(AstNetlist* nodep) {
        m_longId = 0;
        m_modp = NULL;
        m_nextValue = 1;
        //
        iterate(nodep);
    }
    virtual ~ParamVisitor() {}
};

//----------------------------------------------------------------------
// VISITs

void ParamVisitor::visitCell(AstCell* nodep, const string& hierName) {
    // Cell: Check for parameters in the instantiation.
    iterateChildren(nodep);
    UASSERT_OBJ(nodep->modp(), nodep, "Not linked?");
    // We always run this, even if no parameters, as need to look for interfaces,
    // and remove any recursive references
    {
        UINFO(4,"De-parameterize: "<<nodep<<endl);
        // Create new module name with _'s between the constants
        if (debug()>=10) nodep->dumpTree(cout, "-cell: ");
        // Evaluate all module constants
        V3Const::constifyParamsEdit(nodep);
        AstNodeModule* srcModp = nodep->modp();
        srcModp->hierName(hierName + "." + nodep->name());

        // Make sure constification worked
        // Must be a separate loop, as constant conversion may have changed some pointers.
        //if (debug()) nodep->dumpTree(cout, "-cel2: ");
        string longname = srcModp->name();
        bool any_overrides = false;
        if (nodep->recursive()) any_overrides = true;  // Must always clone __Vrcm (recursive modules)
        longname += "_";
        if (debug()>8) nodep->paramsp()->dumpTreeAndNext(cout, "-cellparams: ");
        for (AstPin* pinp = nodep->paramsp(); pinp; pinp=VN_CAST(pinp->nextp(), Pin)) {
            if (!pinp->exprp()) continue;  // No-connect
            if (AstVar* modvarp = pinp->modVarp()) {
                if (!modvarp->isGParam()) {
                    pinp->v3error("Attempted parameter setting of non-parameter: Param "
                                  <<pinp->prettyNameQ()<<" of "<<nodep->prettyNameQ());
                } else if (VN_IS(pinp->exprp(), InitArray)
                           && VN_IS(modvarp->subDTypep(), UnpackArrayDType)) {
                    // Array assigned to array
                    AstNode* exprp = pinp->exprp();
                    longname += "_" + paramSmallName(srcModp, modvarp) + paramValueNumber(exprp);
                    any_overrides = true;
                } else {
                    AstConst* exprp = VN_CAST(pinp->exprp(), Const);
                    AstConst* origp = VN_CAST(modvarp->valuep(), Const);
                    if (!exprp) {
                        //if (debug()) pinp->dumpTree(cout, "error:");
                        pinp->v3error("Can't convert defparam value to constant: Param "
                                      <<pinp->prettyNameQ()<<" of "<<nodep->prettyNameQ());
                        pinp->exprp()->replaceWith(
                            new AstConst(pinp->fileline(),
                                         AstConst::WidthedValue(), modvarp->width(), 0));
                    } else if (origp && exprp->sameTree(origp)) {
                        // Setting parameter to its default value.  Just ignore it.
                        // This prevents making additional modules, and makes coverage more
                        // obvious as it won't show up under a unique module page name.
                    } else if (exprp->num().isDouble()
                               || exprp->num().isString()
                               ||  exprp->num().isFourState()) {
                        longname += ("_" + paramSmallName(srcModp, modvarp)
                                     + paramValueNumber(exprp));
                        any_overrides = true;
                    } else {
                        longname += ("_" + paramSmallName(srcModp, modvarp)
                                     + exprp->num().ascii(false));
                        any_overrides = true;
                    }
                }
            } else if (AstParamTypeDType* modvarp = pinp->modPTypep()) {
                AstNodeDType* exprp = VN_CAST(pinp->exprp(), NodeDType);
                AstNodeDType* origp = modvarp->subDTypep();
                if (!exprp) {
                    pinp->v3error("Parameter type pin value isn't a type: Param "
                                  <<pinp->prettyNameQ()<<" of "<<nodep->prettyNameQ());
                } else if (!origp) {
                    pinp->v3error("Parameter type variable isn't a type: Param "
                                  <<modvarp->prettyNameQ());
                } else {
                    UINFO(9,"Parameter type assignment expr="<<exprp<<" to "<<origp<<endl);
                    if (exprp->sameTree(origp)) {
                        // Setting parameter to its default value.  Just ignore it.
                        // This prevents making additional modules, and makes coverage more
                        // obvious as it won't show up under a unique module page name.
                    } else {
                        V3Const::constifyParamsEdit(exprp);
                        longname += "_" + paramSmallName(srcModp, modvarp) + paramValueNumber(exprp);
                        any_overrides = true;
                    }
                }
            } else {
                pinp->v3error("Parameter not found in sub-module: Param "
                              <<pinp->prettyNameQ()<<" of "<<nodep->prettyNameQ());
            }
        }
        IfaceRefRefs ifaceRefRefs;
        for (AstPin* pinp = nodep->pinsp(); pinp; pinp=VN_CAST(pinp->nextp(), Pin)) {
            AstVar* modvarp = pinp->modVarp();
            if (modvarp->isIfaceRef()) {
                AstIfaceRefDType* portIrefp = VN_CAST(modvarp->subDTypep(), IfaceRefDType);
                if (!portIrefp && VN_IS(modvarp->subDTypep(), UnpackArrayDType)) {
                    portIrefp = VN_CAST(VN_CAST(modvarp->subDTypep(), UnpackArrayDType)->subDTypep(), IfaceRefDType);
                }

                AstIfaceRefDType* pinIrefp = NULL;
                AstNode* exprp = pinp->exprp();
                if (exprp
                    && VN_IS(exprp, VarRef)
                    && VN_CAST(exprp, VarRef)->varp()
                    && VN_CAST(exprp, VarRef)->varp()->subDTypep()
                    && VN_IS(VN_CAST(exprp, VarRef)->varp()->subDTypep(), IfaceRefDType)) {
                    pinIrefp = VN_CAST(VN_CAST(exprp, VarRef)->varp()->subDTypep(), IfaceRefDType);
                } else if (exprp
                           && exprp->op1p()
                           && VN_IS(exprp->op1p(), VarRef)
                           && VN_CAST(exprp->op1p(), VarRef)->varp()
                           && VN_CAST(exprp->op1p(), VarRef)->varp()->subDTypep()
                           && VN_CAST(VN_CAST(exprp->op1p(), VarRef)->varp()->subDTypep(), UnpackArrayDType)
                           && VN_CAST(VN_CAST(exprp->op1p(), VarRef)->varp()->subDTypep(), UnpackArrayDType)->subDTypep()
                           && VN_CAST(VN_CAST(VN_CAST(exprp->op1p(), VarRef)->varp()->subDTypep(), UnpackArrayDType)->subDTypep(), IfaceRefDType)) {
                    pinIrefp = VN_CAST(VN_CAST(VN_CAST(exprp->op1p(), VarRef)->varp()->subDTypep(), UnpackArrayDType)->subDTypep(), IfaceRefDType);
                } else if (exprp
                           && VN_IS(exprp, VarRef)
                           && VN_CAST(exprp, VarRef)->varp()
                           && VN_CAST(exprp, VarRef)->varp()->subDTypep()
                           && VN_CAST(VN_CAST(exprp, VarRef)->varp()->subDTypep(), UnpackArrayDType)
                           && VN_CAST(VN_CAST(exprp, VarRef)->varp()->subDTypep(), UnpackArrayDType)->subDTypep()
                           && VN_CAST(VN_CAST(VN_CAST(exprp, VarRef)->varp()->subDTypep(), UnpackArrayDType)->subDTypep(), IfaceRefDType)) {
                    pinIrefp = VN_CAST(VN_CAST(VN_CAST(exprp, VarRef)->varp()->subDTypep(), UnpackArrayDType)->subDTypep(), IfaceRefDType);
                }

                UINFO(9,"     portIfaceRef "<<portIrefp<<endl);

                if (!portIrefp) {
                    pinp->v3error("Interface port "<<modvarp->prettyNameQ()
                                  <<" is not an interface " << modvarp);
                } else if (!pinIrefp) {
                    pinp->v3error("Interface port "<<modvarp->prettyNameQ()
                                  <<" is not connected to interface/modport pin expression");
                } else {
                    UINFO(9,"     pinIfaceRef "<<pinIrefp<<endl);
                    if (portIrefp->ifaceViaCellp() != pinIrefp->ifaceViaCellp()) {
                        UINFO(9,"     IfaceRefDType needs reconnect  "<<pinIrefp<<endl);
                        longname += ("_" + paramSmallName(srcModp, pinp->modVarp())
                                     + paramValueNumber(pinIrefp));
                        any_overrides = true;
                        ifaceRefRefs.push_back(make_pair(portIrefp, pinIrefp));
                        if (portIrefp->ifacep() != pinIrefp->ifacep()
                            // Might be different only due to param cloning, so check names too
                            && portIrefp->ifaceName() != pinIrefp->ifaceName()) {
                            pinp->v3error("Port "<<pinp->prettyNameQ()<<" expects "
                                          <<AstNode::prettyNameQ(portIrefp->ifaceName())
                                          <<" interface but pin connects "
                                          <<AstNode::prettyNameQ(pinIrefp->ifaceName())
                                          <<" interface");
                        }
                    }
                }
            }
        }

        if (!any_overrides) {
            UINFO(8,"Cell parameters all match original values, skipping expansion.\n");
        } else {
            // If the name is very long, we don't want to overwhelm the filename limit
            // We don't do this always, as it aids debugability to have intuitive naming.
            // TODO can use new V3Name hash replacement instead of this
            string newname = longname;
            if (longname.length()>30) {
                LongMap::iterator iter = m_longMap.find(longname);
                if (iter != m_longMap.end()) {
                    newname = iter->second;
                } else {
                    newname = srcModp->name();
                    newname += "__pi"+cvtToStr(++m_longId);  // We use all upper case above, so lower here can't conflict
                    m_longMap.insert(make_pair(longname, newname));
                }
            }
            UINFO(4,"Name: "<<srcModp->name()<<"->"<<longname<<"->"<<newname<<endl);

            //
            // Already made this flavor?
            AstNodeModule* cellmodp = NULL;
            ModNameMap::iterator iter = m_modNameMap.find(newname);
            if (iter != m_modNameMap.end()) cellmodp = iter->second.m_modp;
            if (!cellmodp) {
                // Deep clone of new module
                // Note all module internal variables will be re-linked to the new modules by clone
                // However links outside the module (like on the upper cells) will not.
                cellmodp = srcModp->cloneTree(false);
                cellmodp->name(newname);
                cellmodp->user5(false);  // We need to re-recurse this module once changed
                cellmodp->recursive(false);
                cellmodp->recursiveClone(false);
                nodep->recursive(false);
                // Recursion may need level cleanups
                if (cellmodp->level() <= m_modp->level()) cellmodp->level(m_modp->level()+1);
                if ((cellmodp->level() - srcModp->level())
                    >= (v3Global.opt.moduleRecursionDepth() - 2)) {
                    nodep->v3error("Exceeded maximum --module-recursion-depth of "
                                   <<v3Global.opt.moduleRecursionDepth());
                }
                // Keep tree sorted by level
                AstNodeModule* insertp = srcModp;
                while (VN_IS(insertp->nextp(), NodeModule)
                       && VN_CAST(insertp->nextp(), NodeModule)->level() < cellmodp->level()) {
                    insertp = VN_CAST(insertp->nextp(), NodeModule);
                }
                insertp->addNextHere(cellmodp);

                m_modNameMap.insert(make_pair(cellmodp->name(), ModInfo(cellmodp)));
                iter = m_modNameMap.find(newname);
                CloneMap* clonemapp = &(iter->second.m_cloneMap);
                UINFO(4,"     De-parameterize to new: "<<cellmodp<<endl);

                // Grab all I/O so we can remap our pins later
                // Note we allow multiple users of a parameterized model,
                // thus we need to stash this info.
                collectPins(clonemapp, cellmodp);
                // Relink parameter vars to the new module
                relinkPins(clonemapp, nodep->paramsp());

                // Fix any interface references
                for (IfaceRefRefs::iterator it=ifaceRefRefs.begin();
                     it!=ifaceRefRefs.end(); ++it) {
                    AstIfaceRefDType* portIrefp = it->first;
                    AstIfaceRefDType* pinIrefp = it->second;
                    AstIfaceRefDType* cloneIrefp = portIrefp->clonep();
                    UINFO(8,"     IfaceOld "<<portIrefp<<endl);
                    UINFO(8,"     IfaceTo  "<<pinIrefp<<endl);
                    UASSERT_OBJ(cloneIrefp, portIrefp,
                                "parameter clone didn't hit AstIfaceRefDType");
                    UINFO(8,"     IfaceClo "<<cloneIrefp<<endl);
                    cloneIrefp->ifacep(pinIrefp->ifaceViaCellp());
                    UINFO(8,"     IfaceNew "<<cloneIrefp<<endl);
                }

                // Assign parameters to the constants specified
                // DOES clone() so must be finished with module clonep() before here
                for (AstPin* pinp = nodep->paramsp(); pinp; pinp=VN_CAST(pinp->nextp(), Pin)) {
                    if (pinp->exprp()) {
                        if (AstVar* modvarp = pinp->modVarp()) {
                            AstNode* newp = pinp->exprp();  // Const or InitArray
                            // Remove any existing parameter
                            if (modvarp->valuep()) modvarp->valuep()->unlinkFrBack()->deleteTree();
                            // Set this parameter to value requested by cell
                            modvarp->valuep(newp->cloneTree(false));
                        }
                        else if (AstParamTypeDType* modptp = pinp->modPTypep()) {
                            AstNodeDType* dtypep = VN_CAST(pinp->exprp(), NodeDType);
                            UASSERT_OBJ(dtypep, pinp, "unlinked param dtype");
                            if (modptp->childDTypep()) {
                                pushDeletep(modptp->childDTypep()->unlinkFrBack());
                            }
                            // Set this parameter to value requested by cell
                            modptp->childDTypep(dtypep->cloneTree(false));
                            // Later V3LinkDot will convert the ParamDType to a Typedef
                            // Not done here as may be localparams, etc, that also need conversion
                        }
                    }
                }

            } else {
                UINFO(4,"     De-parameterize to old: "<<cellmodp<<endl);
            }

            // Have child use this module instead.
            nodep->modp(cellmodp);
            nodep->modName(newname);

            // We need to relink the pins to the new module
            CloneMap* clonemapp = &(iter->second.m_cloneMap);
            relinkPins(clonemapp, nodep->pinsp());
            UINFO(8,"     Done with "<<cellmodp<<endl);
        }  // if any_overrides

        nodep->recursive(false);

        // Delete the parameters from the cell; they're not relevant any longer.
        if (nodep->paramsp()) nodep->paramsp()->unlinkFrBackWithNext()->deleteTree();
        UINFO(8,"     Done with "<<nodep<<endl);
        //if (debug()>=10) v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("param-out.tree"));
    }

    // Now remember to process the child module at the end of the module
    m_todoModps.insert(make_pair(nodep->modp()->level(), nodep->modp()));
}

//######################################################################
// Param class functions

void V3Param::param(AstNetlist* rootp) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        ParamVisitor visitor (rootp);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("param", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
