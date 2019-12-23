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
// Variables to be splitted must be marked by /*verilator split_var*/ pragma.
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
// - Only 1D unpacked array can be splitted
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

namespace {
//######################################################################
//

class SplitVarVisitor : public AstNVisitor {
    AstNodeModule* m_modp;  // current module
    AstVar* m_lastVar;      // the most recently declared variable
    // key:variable to be splitted. value:location where the variable is referenced.
    vl_unordered_map<AstVar*, std::vector<AstArraySel*> > m_refs;
    virtual void visit(AstNode* nodep) VL_OVERRIDE;
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE;
    virtual void visit(AstVar* nodep) VL_OVERRIDE;
    virtual void visit(AstPragma* pragmap) VL_OVERRIDE;
    virtual void visit(AstArraySel* nodep) VL_OVERRIDE;

public:
    explicit SplitVarVisitor(AstNodeModule* modp);
    explicit SplitVarVisitor(AstNode* nodep);
    ~SplitVarVisitor();
    void split();  // must call before dtor
    static bool canSplit(const AstVar* nodep);
    static int debug(bool reset = false);
};

// Check if the passed variable can be splitted.
// Even if this function returns true, the variable may not be splitted
// because the access to the variable cannot be determined statically.
bool SplitVarVisitor::canSplit(const AstVar* nodep) {
    if (AstNodeDType* dtypep = nodep->subDTypep()) {
        const std::pair<uint32_t, uint32_t> dim = dtypep->dimensions(false);
        UINFO(5, "Unpacked Dim of \"" << nodep->name() << "\":" << dim.second << '\n');
        // Support just 1D in unpacked side.
        // Traced or public variable cannot be splitted.
        return dim.second == 1 && !nodep->isSigPublic() && !nodep->isTrace();
    }
    return false;
}

int SplitVarVisitor::debug(bool reset) {
    static int level = -1;
    if (VL_UNLIKELY(level < 0) || reset) {
        level = v3Global.opt.debugSrcLevel(__FILE__);
    }
    return level;
}

void SplitVarVisitor::visit(AstNode* nodep) {
    iterateChildren(nodep);
}

void SplitVarVisitor::visit(AstNodeModule* nodep) {
    if (m_modp) {
        SplitVarVisitor visitor(nodep);
        visitor.split();
    } else {
        m_modp = nodep;
        iterateChildren(nodep);
    }
}

void SplitVarVisitor::visit(AstVar* nodep) {
    m_lastVar = nodep;
}

void SplitVarVisitor::visit(AstPragma* pragmap) {
    if (pragmap->pragType() != AstPragmaType::SPLIT_VAR) return;  // nothing to do
    if (!m_lastVar) {
        pragmap->v3warn(SPLITVAR, "Stray pragma of split_var is detected.");
    } else if (!canSplit(m_lastVar)) {
        pragmap->v3warn(SPLITVAR,
                        "Pragma split_var is specified on a variable whose type is not supported yet. "
                        "Only unpacked 1D array is supported by this version.");
    } else {  // finally find a good candidate
        UINFO(4, m_lastVar->name() << " is added to candidate list.\n");
        m_refs.insert(std::make_pair(m_lastVar, std::vector<AstArraySel*>()));
    }
    m_lastVar = NULL;
    pragmap->unlinkFrBack()->deleteTree();  // consume the pragma here anyway.
}

void SplitVarVisitor::visit(AstArraySel* nodep) {
    AstVarRef* const vrefp = VN_CAST(nodep->fromp(), VarRef);
    if (!vrefp) return;

    AstVar* const varp = vrefp->varp();
    if (m_refs.find(varp) == m_refs.end()) return;  // variable without split_var pragma

    AstConst* indexp = VN_CAST(nodep->bitp(), Const);
    if (!indexp) {  // index is not constant yet.
        UINFO(4, "Index of " << vrefp->name() << " is " << nodep->bitp()
                             << " which is not constant.\n");
        AstNode* const constified = V3Const::constifyEdit(nodep->bitp());
        UINFO(4, "After constified:" << constified << '\n');
        indexp = VN_CAST(constified, Const);
    }

    if (indexp) {  // OK
        m_refs[varp].push_back(nodep);
    } else {
        nodep->bitp()->v3warn(SPLITVAR,
                              "Variable \"" << vrefp->name() << "\" will not be splitted "
                              "because index cannot be determined statically.");
        m_refs.erase(varp);
    }
}

// The actual splitting operation is done in this function, so don't forget to call this function.
// The reason not doing things in dtor is to avoid throwing an exception in dtor.
void SplitVarVisitor::split() {
    for (vl_unordered_map<AstVar*, std::vector<AstArraySel*> >::iterator it = m_refs.begin(),
                                                                         it_end = m_refs.end();
        it != it_end; ++it) {
        UINFO(3, "In module " << m_modp->name() << " var " << it->first->name() << " which has "
                              << it->second.size() << " refs"
                              << " will be splitted.\n");
        AstVar* const varp = it->first;
        AstUnpackArrayDType* const dtypep = VN_CAST(varp->subDTypep(), UnpackArrayDType);
        std::vector<AstVar*> vars;
        // Add the splitted variables
        for (uint32_t i = 0; i < dtypep->arrayUnpackedElements(); ++i) {
            std::stringstream name;
            name << varp->name() << std::dec << i;
            AstVar* const newp = new AstVar(varp->fileline(), varp->varType(), name.str(), dtypep->subDTypep());
            m_modp->addStmtp(newp);
            vars.push_back(newp);
        }

        // refer the splitted variable
        for (size_t i = 0; i < it->second.size(); ++i) {
            AstArraySel* selp = it->second[i];
            AstVarRef* const vrefp = VN_CAST(selp->fromp(), VarRef);
            AstConst* const indexp = VN_CAST(selp->bitp(), Const);
            UASSERT_OBJ(vrefp && indexp, selp, "already checked");
            const uint32_t idx = indexp->toUInt();
            std::cout << "Access idx:" << idx << std::endl;
            AstVarRef* const new_vref = new AstVarRef(selp->fileline(), vars.at(idx), vrefp->lvalue());
            selp->replaceWith(new_vref); selp->deleteTree(); VL_DANGLING(selp);
        }
        varp->unlinkFrBack()->deleteTree();
    }
    m_refs.clear();  // done
}


SplitVarVisitor::SplitVarVisitor(AstNodeModule* modp)
    : m_modp(modp)
    , m_lastVar(NULL) {
    iterateChildren(modp);
}

SplitVarVisitor::SplitVarVisitor(AstNode* nodep)
    : m_modp(NULL)
    , m_lastVar(NULL) {
    iterate(nodep);
}

SplitVarVisitor::~SplitVarVisitor() {
    UASSERT(m_refs.empty(), "Don't forget to call split()");
}
}  // unnamed namespace

//######################################################################
// Split class functions
void V3SplitVar::splitVariable(AstNode* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    {
        SplitVarVisitor visitor(nodep);
        visitor.split();
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("split_array", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}

bool V3SplitVar::canSplitVar(const AstVar* varp) {
    return SplitVarVisitor::canSplit(varp);
}
