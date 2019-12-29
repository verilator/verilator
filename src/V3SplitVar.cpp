// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break variables into separate words to avoid UNOPTFLAT
//
// Code available from: https://verilator.org
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
// V3SplitVar divides a variable into multiple variables to avoid UNOPTFLAT warning
// and get better perfomance.
// Variables to be split must be marked by /*verilator split_var*/ pragma.
// There are sveral kinds of data types that may cause the warning.
// 1) Unpacked arrays
// 2) Packed arrays
// 3) Unpacked structs
// 4) Packed structs
// 5) Bitfields within a signal. (Especially Verilog code predating structs/2D arrays.)
// 2-5 above are treated as bitfields in verilator.
//
// What this pass does looks as below.
//
// <pre>
// logic [1:0] unpcked_array_var[0:3]; /*verilator split_var*/
// always_comb begin
//    unpacked_array_var[1] = unpacked_array_var[0]; // UNOPTFLAT warning
//    unpacked_array_var[2] = unpacked_array_var[1];
//    unpacked_array_var[3] = unpacked_array_var[2];
// end
// </pre>
//
// is converted to
//
// <pre>
// logic [1:0] unpcked_array_var0;
// logic [1:0] unpcked_array_var1;
// logic [1:0] unpcked_array_var2;
// logic [1:0] unpcked_array_var3;
// always_comb begin
//    unpacked_array_var1 = unpacked_array_var0;
//    unpacked_array_var2 = unpacked_array_var1;
//    unpacked_array_var3 = unpacked_array_var2;
// end
// </pre>
//
//
// Limitations: (planned to be resolved)
// - Only 1D unpacked array can be split
// - Splitting 2) - 5) will be supported later
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Const.h"
#include "V3Global.h"
#include "V3SplitVar.h"
#include "V3Stats.h"

#include <vector>
#include VL_INCLUDE_UNORDERED_MAP
#include VL_INCLUDE_UNORDERED_SET

//######################################################################
//

class SplitUnpackedVarVisitor : public AstNVisitor {
    AstNodeModule* m_modp;  // current module
    AstVar* m_lastVarp;     // the most recently declared variable
    int m_numSplit;         // total number of split variable
    // key:variable to be split. value:location where the variable is referenced.
    vl_unordered_map<AstVar*, std::vector<AstArraySel*> > m_refs;

    static AstConst* constifyIfNot(AstNode* nodep) {
        AstConst* constp = VN_CAST(nodep, Const);
        if (!constp) {
            UINFO(4, nodep << " is expected to be constant, but not\n");
            AstNode* const constified = V3Const::constifyEdit(nodep);
            UINFO(4, "After constified:" << constified << '\n');
            constp = VN_CAST(constified, Const);
        }
        return constp;
    }
    virtual void visit(AstNode* nodep) VL_OVERRIDE { iterateChildren(nodep); }
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        UASSERT_OBJ(m_modp == NULL, m_modp, "Nested module declration");
        m_modp = nodep;
        m_lastVarp = NULL;
        iterateChildren(nodep);
        split();
        m_modp = NULL;
    }
    virtual void visit(AstVar* nodep) VL_OVERRIDE { m_lastVarp = nodep; }
    virtual void visit(AstPragma* pragmap) VL_OVERRIDE {
        if (pragmap->pragType() != AstPragmaType::SPLIT_VAR) return;  // nothing to do
        if (!m_lastVarp) {
            pragmap->v3warn(SPLITVAR, "Stray pragma of split_var is detected.");
        } else if (!canSplit(m_lastVarp)) {
            pragmap->v3warn(SPLITVAR,
                            "Pragma split_var is specified on "
                                << m_lastVarp->prettyNameQ()
                                << " which type is not supported yet. "
                                   "Only unpacked 1D array is supported by this version.");
        } else {  // finally find a good candidate
            UINFO(4, m_lastVarp->name() << " is added to candidate list.\n");
            m_refs.insert(std::make_pair(m_lastVarp, std::vector<AstArraySel*>()));
        }
        m_lastVarp = NULL;
        pragmap->unlinkFrBack()->deleteTree(); VL_DANGLING(pragmap); // consume the pragma here anyway.
    }
    virtual void visit(AstArraySel* nodep) VL_OVERRIDE {
        AstVarRef* const vrefp = VN_CAST(nodep->fromp(), VarRef);
        if (!vrefp) return;

        AstVar* const varp = vrefp->varp();
        if (m_refs.find(varp) == m_refs.end()) return;  // variable without split_var pragma

        AstConst* const indexp = constifyIfNot(nodep->bitp());

        if (indexp) {  // OK
            m_refs[varp].push_back(nodep);
        } else {
            nodep->bitp()->v3warn(SPLITVAR,
                                  "Variable " << vrefp->prettyNameQ()
                                              << " will not be split because index cannot be determined statically.");
            m_refs.erase(varp);
        }
    }
    // The actual splitting operation is done in this function, so don't forget to call this function.
    // The reason not doing things in dtor is to avoid throwing an exception in dtor.
    void split() {
        for (vl_unordered_map<AstVar*, std::vector<AstArraySel*> >::iterator it = m_refs.begin(),
                                                                             it_end = m_refs.end();
             it != it_end; ++it) {
            UINFO(3, "In module " << m_modp->name() << " var " << it->first->prettyNameQ()
                                  << " which has "
                                  << it->second.size() << " refs"
                                  << " will be split.\n");
            AstVar* varp = it->first;
            AstUnpackArrayDType* const dtypep = VN_CAST(varp->subDTypep(), UnpackArrayDType);
            std::vector<AstVar*> vars;
            // Add the split variables
            AstConst* const lsbp = constifyIfNot(dtypep->rangep()->lsbp());
            AstConst* const msbp = constifyIfNot(dtypep->rangep()->msbp());
            UASSERT_OBJ(lsbp, dtypep->rangep()->lsbp(), "must be constant");
            UASSERT_OBJ(msbp, dtypep->rangep()->msbp(), "must be constant");
            const vlsint32_t lsb = lsbp->toSInt(), msb = msbp->toSInt();
            UASSERT_OBJ(lsb <= msb, dtypep->rangep(), "lsb must not greater than msb");
            for (vlsint32_t i = 0; i <= msb - lsb; ++i) {
                const std::string name = varp->name() + "__BRA__" + cvtToStr(i) + "__KET__";
                AstVar* const newp = new AstVar(varp->fileline(), varp->varType(), name, dtypep->subDTypep());
                m_modp->addStmtp(newp);
                vars.push_back(newp);
            }

            // refer the split variable
            for (size_t i = 0; i < it->second.size(); ++i) {
                AstArraySel* selp = it->second[i];
                AstVarRef* const vrefp = VN_CAST(selp->fromp(), VarRef);
                AstConst* const indexp = VN_CAST(selp->bitp(), Const);
                UASSERT_OBJ(vrefp && indexp, selp, "already checked");
                const uint32_t idx = indexp->toUInt();
                // V3Width:width() removes VAR_BASE attribute and make index 0-origin.
                AstVarRef* const new_vref = new AstVarRef(selp->fileline(), vars.at(idx), vrefp->lvalue());
                selp->replaceWith(new_vref); selp->deleteTree(); VL_DANGLING(selp);
            }
            varp->unlinkFrBack()->deleteTree(); VL_DANGLING(varp);
            ++m_numSplit;
        }
        m_refs.clear();  // done
    }

public:
    explicit SplitUnpackedVarVisitor(AstNetlist* nodep)
        : m_modp(NULL)
        , m_lastVarp(NULL)
        , m_numSplit(0) {
        iterate(nodep);
    }
    ~SplitUnpackedVarVisitor() {
        UASSERT(m_refs.empty(), "Don't forget to call split()");
        V3Stats::addStat("SplitVar, Split Unpacked Array", m_numSplit);
    }
    VL_DEBUG_FUNC;  // Declare debug()

    // Check if the passed variable can be split.
    // Even if this function returns true, the variable may not be split
    // because the access to the variable cannot be determined statically.
    static bool canSplit(const AstVar* nodep) {
        if (AstNodeDType* dtypep = nodep->subDTypep()) {
            const std::pair<uint32_t, uint32_t> dim = dtypep->dimensions(false);
            UINFO(5, "Unpacked Dim of " << nodep->prettyNameQ() << ":" << dim.second << '\n');
            // Support just 1D in unpacked side.
            // Traced or public variable cannot be split.
            return dim.second == 1 && !nodep->isSigPublic() && !nodep->isTrace();
        }
        return false;
    }
};



//######################################################################
// Split class functions
void V3SplitVar::splitUnpackedVariable(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    {
        SplitUnpackedVarVisitor visitor(nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("split_var", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}

bool V3SplitVar::canSplitVar(const AstVar* varp) {
    return SplitUnpackedVarVisitor::canSplit(varp);
}
