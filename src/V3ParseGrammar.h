// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Parse syntax tree
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3Ast.h"
#include "V3Const.h"
#include "V3Control.h"
#include "V3Global.h"
#include "V3ParseImp.h"  // Defines YYTYPE; before including bison header

#include <stack>
#include <vector>

class V3ParseGrammar final {
public:
    AstVar* m_varAttrp = nullptr;  // Current variable for attribute adding
    AstRange* m_gateRangep = nullptr;  // Current range for gate declarations
    AstNode* m_scopedSigAttr = nullptr;  // Pointer to default signal attribute
    AstCase* m_caseAttrp = nullptr;  // Current case statement for attribute adding
    AstNodeDType* m_varDTypep = nullptr;  // Pointer to data type for next signal declaration
    AstNodeDType* m_memDTypep = nullptr;  // Pointer to data type for next member declaration
    AstDelay* m_netDelayp = nullptr;  // Pointer to delay for next signal declaration
    AstStrengthSpec* m_netStrengthp = nullptr;  // Pointer to strength for next net declaration
    FileLine* m_instModuleFl = nullptr;  // Fileline of module referenced for instantiations
    AstPin* m_instParamp = nullptr;  // Parameters for instantiations
    string m_instModule;  // Name of module referenced for instantiations
    VVarType m_varDecl = VVarType::UNKNOWN;  // Type for next signal declaration (reg/wire/etc)
    VDirection m_varIO = VDirection::NONE;  // Direction for next signal declaration (reg/wire/etc)
    VLifetime m_varLifetime;  // Static/Automatic for next signal
    V3Control::VarSpecKind m_vltVarSpecKind = V3Control::VarSpecKind::VAR;
    bool m_impliedDecl = false;  // Allow implied wire declarations
    bool m_varDeclTyped = false;  // Var got reg/wire for dedup check
    bool m_pinAnsi = false;  // In ANSI parameter or port list
    bool m_tracingParse = true;  // Tracing disable for parser
    bool m_inImplements = false;  // Is inside class implements list
    bool m_insideProperty = false;  // Is inside property declaration
    bool m_specifyignWarned = false;  // Issued a SPECIFYIGN warning
    bool m_typedPropertyPort = false;  // Typed property port occurred on port lists
    bool m_modportImpExpActive
        = false;  // Standalone ID is a tf_identifier instead of port_identifier
    bool m_modportImpExpLastIsExport
        = false;  // Last import_export statement in modportPortsDecl is an export

    int m_pinNum = -1;  // Pin number currently parsing
    std::stack<int> m_pinStack;  // Queue of pin numbers being parsed

    static int s_typeImpNum;  // Implicit type number, incremented each module

    // CONSTRUCTORS
    V3ParseGrammar() {}
    static V3ParseGrammar* singletonp() {
        static V3ParseGrammar singleton;
        return &singleton;
    }

    // METHODS
    AstArg* argWrapList(AstNodeExpr* nodep) VL_MT_DISABLED;
    bool allTracingOn(const FileLine* fl) const {
        return v3Global.opt.trace() && m_tracingParse && fl->tracingOn();
    }
    AstRange* scrubRange(AstNodeRange* rangep) VL_MT_DISABLED;
    AstNodePreSel* scrubSel(AstNodeExpr* fromp, AstNodePreSel* selp) VL_MT_DISABLED;
    AstNodeDType* createArray(AstNodeDType* basep, AstNodeRange* rangep,
                              bool isPacked) VL_MT_DISABLED;
    AstVar* createVariable(FileLine* fileline, const string& name, AstNodeRange* arrayp,
                           AstNode* attrsp) VL_MT_DISABLED;
    AstAssignW* createSupplyExpr(FileLine* fileline, const string& name, int value) VL_MT_DISABLED;
    std::string textQuoted(FileLine* fileline, const std::string& text) {
        return singletonp()->unquoteString(fileline, text);
    }
    AstNode* createCell(FileLine* fileline, const string& name, AstPin* pinlistp,
                        AstNodeRange* rangelistp) {
        // Must clone m_instParamp as may be comma'ed list of instances
        AstCell* const nodep = new AstCell{
            fileline,
            singletonp()->m_instModuleFl,
            name,
            singletonp()->m_instModule,
            pinlistp,
            (singletonp()->m_instParamp ? singletonp()->m_instParamp->cloneTree(true) : nullptr),
            singletonp()->scrubRange(rangelistp)};
        nodep->trace(singletonp()->allTracingOn(fileline));
        return nodep;
    }
    // Helper to move bins from parser list to coverpoint
    void addCoverpointBins(AstCoverpoint* cp, AstNode* binsList) {
        if (!binsList) return;

        // CRITICAL FIX: The parser creates a linked list of bins. When we try to move them
        // to the coverpoint one by one while they're still linked, the addNext() logic
        // that updates headtailp pointers creates circular references. We must fully
        // unlink ALL bins before adding ANY to the coverpoint.
        std::vector<AstCoverBin*> bins;
        std::vector<AstCoverOption*> options;

        // To unlink the head node (which has no backp), create a temporary parent
        AstBegin* tempParent = new AstBegin{binsList->fileline(), "[TEMP]", nullptr, true};
        tempParent->addStmtsp(binsList);  // Now binsList has a backp

        // Now unlink all bins - they all have backp now
        for (AstNode *binp = binsList, *nextp; binp; binp = nextp) {
            nextp = binp->nextp();

            if (AstCoverBin* cbinp = VN_CAST(binp, CoverBin)) {
                cbinp->unlinkFrBack();  // Now this works for all bins including head
                bins.push_back(cbinp);
            } else if (AstCgOptionAssign* optp = VN_CAST(binp, CgOptionAssign)) {
                optp->unlinkFrBack();
                // Convert AstCgOptionAssign to AstCoverOption
                VCoverOptionType optType = VCoverOptionType::COMMENT;  // default
                if (optp->name() == "at_least") {
                    optType = VCoverOptionType::AT_LEAST;
                } else if (optp->name() == "weight") {
                    optType = VCoverOptionType::WEIGHT;
                } else if (optp->name() == "goal") {
                    optType = VCoverOptionType::GOAL;
                } else if (optp->name() == "auto_bin_max") {
                    optType = VCoverOptionType::AUTO_BIN_MAX;
                } else if (optp->name() == "per_instance") {
                    optType = VCoverOptionType::PER_INSTANCE;
                } else if (optp->name() == "comment") {
                    optType = VCoverOptionType::COMMENT;
                } else {
                    optp->v3warn(COVERIGN,
                                 "Ignoring unsupported coverage option: " + optp->name());
                }
                AstCoverOption* coverOptp = new AstCoverOption{optp->fileline(), optType,
                                                               optp->valuep()->cloneTree(false)};
                options.push_back(coverOptp);
                VL_DO_DANGLING(optp->deleteTree(), optp);
            } else {
                binp->v3warn(COVERIGN,
                             "Unexpected node in bins list, ignoring");  // LCOV_EXCL_LINE
                VL_DO_DANGLING(binp->deleteTree(), binp);
            }
        }

        // Delete the temporary parent
        VL_DO_DANGLING(tempParent->deleteTree(), tempParent);

        // Now add standalone bins and options to coverpoint
        for (AstCoverBin* cbinp : bins) { cp->addBinsp(cbinp); }
        for (AstCoverOption* optp : options) { cp->addOptionsp(optp); }
    }
    AstDisplay* createDisplayError(FileLine* fileline) {
        AstDisplay* nodep = new AstDisplay{fileline, VDisplayType::DT_ERROR, "", nullptr, nullptr};
        AstNode::addNext<AstNode, AstNode>(nodep, new AstStop{fileline, false});
        return nodep;
    }
    AstNodeExpr* createGatePin(AstNodeExpr* exprp) {
        AstRange* const rangep = m_gateRangep;
        if (!rangep) {
            return exprp;
        } else {
            return new AstGatePin{rangep->fileline(), exprp, rangep->cloneTree(true)};
        }
    }
    AstSenTree* createSenTreeChanged(FileLine* fl, AstNodeExpr* exprp) {
        return new AstSenTree{fl, new AstSenItem{fl, VEdgeType::ET_CHANGED, exprp}};
    }
    AstSenTree* createSenTreeDotStar(FileLine* fl) {
        return new AstSenTree{fl, new AstSenItem{fl, VEdgeType::ET_COMBO_STAR, nullptr}};
    }
    AstNodeExpr* createGlobalClockParseRef(FileLine* fl) {
        return new AstParseRef{fl, "__024global_clock", nullptr, nullptr};
    }
    AstSenTree* createGlobalClockSenTree(FileLine* fl) {
        return createSenTreeChanged(fl, createGlobalClockParseRef(fl));
    }
    AstNode* createNettype(FileLine* fl, const string& name) {
        // As nettypes are unsupported, we just alias to logic
        AstTypedef* const nodep = new AstTypedef{fl, name, nullptr, VFlagChildDType{},
                                                 new AstBasicDType{fl, VFlagLogicPacked{}, 1}};
        V3ParseImp::parsep()->tagNodep(nodep);
        return nodep;
    }
    AstNode* createTypedef(FileLine* fl, const string& name, AstNode* attrsp, AstNodeDType* basep,
                           AstNodeRange* rangep) {
        AstTypedef* const nodep = new AstTypedef{fl, name, attrsp, VFlagChildDType{},
                                                 singletonp()->createArray(basep, rangep, false)};
        V3ParseImp::parsep()->tagNodep(nodep);
        return nodep;
    }
    AstNode* createTypedefFwd(FileLine* fl, const string& name, const VFwdType& fwdType) {
        AstTypedefFwd* const nodep = new AstTypedefFwd{fl, name, fwdType};
        V3ParseImp::parsep()->tagNodep(nodep);
        return nodep;
    }
    void endLabel(FileLine* fl, const AstNode* nodep, const string* endnamep) {
        endLabel(fl, nodep->prettyName(), endnamep);
    }
    void endLabel(FileLine* fl, const string& name, const string* endnamep) {
        if (fl && endnamep && *endnamep != "" && name != *endnamep
            && name != AstNode::prettyName(*endnamep)) {
            fl->v3warn(ENDLABEL, "End label '" << *endnamep << "' does not match begin label '"
                                               << name << "'");
        }
    }
    void setDType(AstNodeDType* dtypep) {
        if (m_varDTypep) {
            UASSERT_OBJ(!m_varDTypep->backp(), m_varDTypep, "Should not link directly");
            VL_DO_CLEAR(m_varDTypep->deleteTree(), m_varDTypep = nullptr);
        }
        m_varDTypep = dtypep;
    }
    void setNetDelay(AstDelay* netDelayp) {
        if (m_netDelayp) {
            UASSERT_OBJ(!m_netDelayp->backp(), m_netDelayp, "Should not link directly");
            VL_DO_CLEAR(m_netDelayp->deleteTree(), m_netDelayp = nullptr);
        }
        m_netDelayp = netDelayp;
    }
    void setNetStrength(AstStrengthSpec* netStrengthp) { m_netStrengthp = netStrengthp; }
    void pinPush() {
        m_pinStack.push(m_pinNum);
        m_pinNum = 1;
    }
    void pinPop(FileLine* fl) {
        if (VL_UNCOVERABLE(m_pinStack.empty())) fl->v3fatalSrc("Underflow of pin stack");
        m_pinNum = m_pinStack.top();
        m_pinStack.pop();
    }
    AstNodeDType* addRange(AstBasicDType* dtypep, AstNodeRange* rangesp, bool isPacked) {
        // If dtypep isn't basic, don't use this, call createArray() instead
        if (!rangesp) {
            return dtypep;
        } else {
            // If rangesp is "wire [3:3][2:2][1:1] foo [5:5][4:4]"
            // then [1:1] becomes the basicdtype range; everything else is arraying
            // the final [5:5][4:4] will be passed in another call to createArray
            AstNodeRange* rangearraysp = nullptr;
            if (dtypep->isRanged()) {
                rangearraysp = rangesp;  // Already a range; everything is an array
            } else {
                AstNodeRange* finalp = rangesp;
                while (finalp->nextp()) finalp = VN_CAST(finalp->nextp(), Range);
                if (finalp != rangesp) {
                    finalp->unlinkFrBack();
                    rangearraysp = rangesp;
                }
                if (AstRange* const finalRangep = VN_CAST(finalp, Range)) {  // not an UnsizedRange
                    if (dtypep->implicit()) {
                        // It's no longer implicit but a wire logic type
                        AstBasicDType* const newp = new AstBasicDType{
                            dtypep->fileline(), VBasicDTypeKwd::LOGIC, dtypep->numeric(),
                            dtypep->width(), dtypep->widthMin()};
                        VL_DO_DANGLING(dtypep->deleteTree(), dtypep);
                        dtypep = newp;
                    }
                    dtypep->rangep(finalRangep);
                }
            }
            return createArray(dtypep, rangearraysp, isPacked);
        }
    }
    string unquoteString(FileLine* fileline, const std::string& text) VL_MT_DISABLED;
    void checkDpiVer(FileLine* fileline, const string& str) {
        if (str != "DPI-C" && !v3Global.opt.bboxSys())
            fileline->v3warn(E_UNSUPPORTED, "Unsupported DPI type '"
                                                << str
                                                << "': Use 'DPI-C' (IEEE 1800-2023 35.5.4)");
    }
    // Given a list of clocking declarations, put them in clocking items
    AstClockingItem* makeClockingItemList(FileLine* flp, const VDirection direction,
                                          AstNodeExpr* skewp, AstNode* const clockingDeclps) {
        AstClockingItem* itemsp = nullptr;
        for (AstNode *nodep = clockingDeclps, *nextp; nodep; nodep = nextp) {
            nextp = nodep->nextp();
            if (nextp) nextp->unlinkFrBackWithNext();
            if (itemsp && skewp) skewp = skewp->cloneTree(false);
            AstClockingItem* itemp = new AstClockingItem{flp, direction, skewp, nodep};
            itemsp = AstNode::addNextNull(itemsp, itemp);
        }
        return itemsp;
    }

    void setScopedSigAttr(AstNode* attrsp) {
        if (m_scopedSigAttr) {  // clearing set attribute
            UASSERT_OBJ(!m_scopedSigAttr->backp(), m_scopedSigAttr, "Should not link directly");
            VL_DO_DANGLING(m_scopedSigAttr->deleteTree(), m_scopedSigAttr);
        }
        m_scopedSigAttr = attrsp;
    }

    void createScopedSigAttr(VAttrType vattrT) {
        setScopedSigAttr(new AstAttrOf{V3ParseImp::parsep()->lexFileline(), vattrT});
    }

    AstNode* cloneScopedSigAttr() const {
        return m_scopedSigAttr ? m_scopedSigAttr->cloneTree(true) : nullptr;
    }

    void createGenericIface(AstNode* const nodep, AstNodeRange* const rangep,
                            AstNode* sigAttrListp, FileLine* const modportFileline = nullptr,
                            const string& modportstrp = "") {
        m_varDecl = VVarType::GPARAM;
        m_varIO = VDirection::NONE;
        setDType(new AstParseTypeDType{nodep->fileline(), VFwdType::GENERIC_INTERFACE});
        m_varDeclTyped = true;
        const std::string uniqueName = "__VGIfaceParam" + nodep->name();
        AstNode::addNext(nodep,
                         createVariable(nodep->fileline(), uniqueName, rangep, sigAttrListp));
        m_varDecl = VVarType::IFACEREF;
        AstIfaceGenericDType* const refdtypep
            = new AstIfaceGenericDType{nodep->fileline(), modportFileline, modportstrp};
        setDType(refdtypep);
        m_varDeclTyped = true;
        m_varIO = VDirection::INPUT;
        AstNode::addNext(nodep,
                         createVariable(nodep->fileline(), nodep->name(), rangep, sigAttrListp));
        m_varDecl = VVarType::VAR;
    }

    // Wrap all statements in the given list in an AstBegin (except those already an AstBegin)
    static AstBegin* wrapInBegin(AstNodeStmt* stmtsp) {
        AstBegin* resp = nullptr;
        for (AstNodeStmt *nodep = stmtsp, *nextp; nodep; nodep = nextp) {
            nextp = VN_AS(nodep->nextp(), NodeStmt);
            if (nextp) nextp->unlinkFrBackWithNext();
            AstBegin* beginp = VN_CAST(nodep, Begin);
            if (!beginp) beginp = new AstBegin{nodep->fileline(), "", nodep, true};
            resp = AstNode::addNext(resp, beginp);
        }
        return resp;
    }
};
