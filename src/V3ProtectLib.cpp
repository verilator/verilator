// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Build DPI protected C++ and SV
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

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3String.h"
#include "V3ProtectLib.h"
#include "V3File.h"
#include "V3Hashed.h"
#include "V3Task.h"

#include <list>


//######################################################################
// ProtectLib top-level visitor

class ProtectVisitor : public AstNVisitor {
  private:
    AstVFile* m_vfilep;                 // DPI-enabled Verilog wrapper
    AstCFile* m_cfilep;                 // C implementation of DPI functions
    // Verilog text blocks
    AstTextBlock* m_modPortsp;          // Module port list
    AstTextBlock* m_comboPortsp;        // Combo function port list
    AstTextBlock* m_seqPortsp;          // Sequential function port list
    AstTextBlock* m_comboIgnorePortsp;  // Combo ignore function port list
    AstTextBlock* m_comboDeclsp;        // Combo signal declaration list
    AstTextBlock* m_seqDeclsp;          // Sequential signal declaration list
    AstTextBlock* m_tmpDeclsp;          // Temporary signal declaration list
    AstTextBlock* m_hashValuep;         // CPP hash value
    AstTextBlock* m_comboParamsp;       // Combo function parameter list
    AstTextBlock* m_clkSensp;           // Clock sensitivity list
    AstTextBlock* m_comboIgnoreParamsp; // Combo ignore parameter list
    AstTextBlock* m_seqParamsp;         // Sequential parameter list
    AstTextBlock* m_nbAssignsp;         // Non-blocking assignment list
    AstTextBlock* m_seqAssignsp;        // Sequential assignment list
    AstTextBlock* m_comboAssignsp;      // Combo assignment list
    // C text blocks
    AstTextBlock* m_cHashValuep;        // CPP hash value
    AstTextBlock* m_cComboParamsp;      // Combo function parameter list
    AstTextBlock* m_cComboInsp;         // Combo input copy list
    AstTextBlock* m_cComboOutsp;        // Combo output copy list
    AstTextBlock* m_cSeqParamsp;        // Sequential parameter list
    AstTextBlock* m_cSeqClksp;          // Sequential clock copy list
    AstTextBlock* m_cSeqOutsp;          // Sequential output copy list
    AstTextBlock* m_cIgnoreParamsp;     // Combo ignore parameter list
    string m_libName;
    string m_topName;
    bool m_foundTop;                    // Have seen the top module

    // VISITORS
    virtual void visit(AstNetlist* nodep) VL_OVERRIDE {
        m_vfilep = new AstVFile(nodep->fileline(),
                                v3Global.opt.makeDir()+"/"+m_libName+".sv");
        nodep->addFilesp(m_vfilep);
        m_cfilep = new AstCFile(nodep->fileline(),
                                v3Global.opt.makeDir()+"/"+m_libName+".cpp");
        nodep->addFilesp(m_cfilep);
        iterateChildren(nodep);
    }

    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        if (!nodep->isTop()) {
            return;
        } else {
            UASSERT_OBJ(!m_foundTop, nodep, "Multiple root modules");
        }
        FileLine* fl = nodep->fileline();
        createSvFile(fl);
        createCppFile(fl);

        iterateChildren(nodep);

        V3Hash hash = V3Hashed::uncachedHash(m_cfilep);
        m_hashValuep->addText(fl, cvtToStr(hash.fullValue())+";\n");
        m_cHashValuep->addText(fl, cvtToStr(hash.fullValue())+"U;\n");
        m_foundTop = true;
    }

    void addComment(AstTextBlock* txtp, FileLine* fl, const string& comment) {
        txtp->addNodep(new AstComment(fl, comment));
    }

    void hashComment(AstTextBlock* txtp, FileLine* fl) {
        addComment(txtp, fl, "Checks to make sure the .sv wrapper and library agree");
    }

    void initialComment(AstTextBlock* txtp, FileLine* fl) {
        addComment(txtp, fl, "Creates an instance of the secret module at initial-time");
        addComment(txtp, fl, "(one for each instance in the user's design) also evaluates");
        addComment(txtp, fl, "the secret module's initial process");
    }

    void comboComment(AstTextBlock* txtp, FileLine* fl) {
        addComment(txtp, fl, "Updates all non-clock inputs and retrieves the results");
    }

    void seqComment(AstTextBlock* txtp, FileLine* fl) {
        addComment(txtp, fl, "Updates all clocks and retrieves the results");
    }

    void comboIgnoreComment(AstTextBlock* txtp, FileLine* fl) {
        addComment(txtp, fl, "Need to convince some simulators that the input to the module");
        addComment(txtp, fl, "must be evaluated before evaluating the clock edge");
    }

    void finalComment(AstTextBlock* txtp, FileLine* fl) {
        addComment(txtp, fl, "Evaluates the secret module's final process");
    }

    void createSvFile(FileLine* fl) {
        // Comments
        AstTextBlock* txtp = new AstTextBlock(fl);
        addComment(txtp, fl, "Wrapper module for DPI protected library");
        addComment(txtp, fl, "This module requires lib"+m_libName+
                   ".a or lib"+m_libName+".so to work");
        addComment(txtp, fl, "See instructions in your simulator for how"
                   " to use DPI libraries\n");

        // Module declaration
        m_modPortsp = new AstTextBlock(fl, "module "+m_libName+" (\n", false, true);
        txtp->addNodep(m_modPortsp);
        txtp->addText(fl, ");\n\n");

        // DPI declarations
        hashComment(txtp, fl);
        txtp->addText(fl, "import \"DPI-C\" function void "+
                      m_libName+"_protectlib_check_hash(int protectlib_hash__V);\n\n");
        initialComment(txtp, fl);
        txtp->addText(fl, "import \"DPI-C\" function chandle "+
                      m_libName+"_protectlib_create(string scope__V);\n\n");
        comboComment(txtp, fl);
        m_comboPortsp = new AstTextBlock(fl, "import \"DPI-C\" function longint "+
                                         m_libName+"_protectlib_combo_update "
                                         "(\n", false, true);
        m_comboPortsp->addText(fl, "chandle handle__V\n");
        txtp->addNodep(m_comboPortsp);
        txtp->addText(fl, ");\n\n");
        seqComment(txtp, fl);
        m_seqPortsp = new AstTextBlock(fl, "import \"DPI-C\" function longint "+
                                       m_libName+"_protectlib_seq_update"
                                       "(\n", false, true);
        m_seqPortsp->addText(fl, "chandle handle__V\n");
        txtp->addNodep(m_seqPortsp);
        txtp->addText(fl, ");\n\n");
        comboIgnoreComment(txtp, fl);
        m_comboIgnorePortsp = new AstTextBlock(fl, "import \"DPI-C\" function void "+
                                               m_libName+"_protectlib_combo_ignore"
                                               "(\n", false, true);
        m_comboIgnorePortsp->addText(fl, "chandle handle__V\n");
        txtp->addNodep(m_comboIgnorePortsp);
        txtp->addText(fl, ");\n\n");
        finalComment(txtp, fl);
        txtp->addText(fl, "import \"DPI-C\" function void "+
                      m_libName+"_protectlib_final(chandle handle__V);\n\n");

        // Local variables
        txtp->addText(fl, "chandle handle__V;\n\n");
        m_comboDeclsp = new AstTextBlock(fl);
        txtp->addNodep(m_comboDeclsp);
        m_seqDeclsp = new AstTextBlock(fl);
        txtp->addNodep(m_seqDeclsp);
        m_tmpDeclsp = new AstTextBlock(fl);
        txtp->addNodep(m_tmpDeclsp);
        txtp->addText(fl, "\ntime last_combo_seqnum__V;\n");
        txtp->addText(fl, "time last_seq_seqnum__V;\n\n");

        // CPP hash value
        addComment(txtp, fl, "Hash value to make sure this file and the corresponding");
        addComment(txtp, fl, "library agree");
        m_hashValuep = new AstTextBlock(fl, "localparam int protectlib_hash__V = ");
        txtp->addNodep(m_hashValuep);
        txtp->addText(fl, "\n");

        // Initial
        txtp->addText(fl, "initial begin\n");
        txtp->addText(fl, m_libName+"_protectlib_check_hash(protectlib_hash__V);\n");
        txtp->addText(fl, "handle__V = "+m_libName+"_protectlib_create"
                      "($sformatf(\"%m\"));\n");
        txtp->addText(fl, "end\n\n");

        // Combinatorial process
        addComment(txtp, fl, "Combinatorialy evaluate changes to inputs");
        m_comboParamsp = new AstTextBlock(fl, "always @(*) begin\n"
                                          "last_combo_seqnum__V = "+
                                          m_libName+"_protectlib_combo_update(\n",
                                          false, true);
        m_comboParamsp->addText(fl, "handle__V\n");
        txtp->addNodep(m_comboParamsp);
        txtp->addText(fl, ");\n");
        txtp->addText(fl, "end\n\n");

        // Sequential process
        addComment(txtp, fl, "Evaluate clock edges");
        m_clkSensp = new AstTextBlock(fl, "always @(", false, true);
        txtp->addNodep(m_clkSensp);
        txtp->addText(fl, ") begin\n");
        m_comboIgnoreParamsp = new AstTextBlock(fl, m_libName+"_protectlib_combo_ignore(\n",
                                                false, true);
        m_comboIgnoreParamsp->addText(fl, "handle__V\n");
        txtp->addNodep(m_comboIgnoreParamsp);
        txtp->addText(fl, ");\n");
        m_seqParamsp = new AstTextBlock(fl, "last_seq_seqnum__V <= "+m_libName+
                                        "_protectlib_seq_update(\n",
                                        false, true);
        m_seqParamsp->addText(fl, "handle__V\n");
        txtp->addNodep(m_seqParamsp);
        txtp->addText(fl, ");\n");
        m_nbAssignsp = new AstTextBlock(fl);
        txtp->addNodep(m_nbAssignsp);
        txtp->addText(fl, "end\n\n");

        // Select between combinatorial and sequential results
        addComment(txtp, fl, "Select between combinatorial and sequential results");
        txtp->addText(fl, "always @(*) begin\n");
        m_seqAssignsp = new AstTextBlock(fl, "if (last_seq_seqnum__V > "
                                         "last_combo_seqnum__V) begin\n");
        txtp->addNodep(m_seqAssignsp);
        m_comboAssignsp = new AstTextBlock(fl, "end else begin\n");
        txtp->addNodep(m_comboAssignsp);
        txtp->addText(fl, "end\n");
        txtp->addText(fl, "end\n\n");

        // Final
        txtp->addText(fl, "final "+m_libName+"_protectlib_final(handle__V);\n\n");

        txtp->addText(fl, "endmodule\n");
        m_vfilep->tblockp(txtp);
    }

    void castPtr(FileLine* fl, AstTextBlock* txtp) {
        txtp->addText(fl, m_topName+"_container* handlep__V = "
                      "static_cast<"+m_topName+"_container*>(vhandlep__V);\n");
    }

    void createCppFile(FileLine* fl) {
        // Comments
        AstTextBlock* txtp = new AstTextBlock(fl);
        addComment(txtp, fl, "Wrapper functions for DPI protected library\n");

        // Includes
        txtp->addText(fl, "#include \""+m_topName+".h\"\n");
        txtp->addText(fl, "#include \"verilated_dpi.h\"\n\n");
        txtp->addText(fl, "#include <cstdio>\n");
        txtp->addText(fl, "#include <cstdlib>\n\n");

        // Verilated module plus sequence number
        addComment(txtp, fl, "Container class to house verilated object and sequence number");
        txtp->addText(fl, "class "+m_topName+"_container: public "+m_topName+" {\n");
        txtp->addText(fl, "public:\n");
        txtp->addText(fl, "long long m_seqnum;\n");
        txtp->addText(fl, m_topName+"_container(const char* scopep__V):\n");
        txtp->addText(fl, m_topName+"(scopep__V) {}\n");
        txtp->addText(fl, "};\n\n");

        // Extern C
        txtp->addText(fl, "extern \"C\" {\n\n");

        // Hash check
        hashComment(txtp, fl);
        txtp->addText(fl, "void "+m_libName+"_protectlib_check_hash"
                      "(int protectlib_hash__V) {\n");
        m_cHashValuep = new AstTextBlock(fl, "int expected_hash__V = ");
        txtp->addNodep(m_cHashValuep);
        txtp->addText(fl, "if (protectlib_hash__V != expected_hash__V) {\n");
        txtp->addText(fl, "fprintf(stderr, \"%%Error: cannot use "+m_libName+" library, "
                      "Verliog (%u) and library (%u) hash values do not "
                      "agree\\n\", protectlib_hash__V, expected_hash__V);\n");
        txtp->addText(fl, "exit(EXIT_FAILURE);\n");
        txtp->addText(fl, "}\n");
        txtp->addText(fl, "}\n\n");

        // Initial
        initialComment(txtp, fl);
        txtp->addText(fl, "void* "+m_libName+"_protectlib_create"
                      " (const char* scopep__V) {\n");
        txtp->addText(fl, m_topName+"_container* handlep__V = "
                      "new "+m_topName+"_container(scopep__V);\n");
        txtp->addText(fl, "return handlep__V;\n");
        txtp->addText(fl, "}\n\n");

        // Updates
        comboComment(txtp, fl);
        m_cComboParamsp = new AstTextBlock(fl, "long long "+m_libName+"_protectlib_combo_update(\n",
                                           false, true);
        m_cComboParamsp->addText(fl, "void* vhandlep__V\n");
        txtp->addNodep(m_cComboParamsp);
        txtp->addText(fl, ")\n");
        m_cComboInsp = new AstTextBlock(fl, "{\n");
        castPtr(fl, m_cComboInsp);
        txtp->addNodep(m_cComboInsp);
        m_cComboOutsp = new AstTextBlock(fl, "handlep__V->eval();\n");
        txtp->addNodep(m_cComboOutsp);
        txtp->addText(fl, "return handlep__V->m_seqnum++;\n");
        txtp->addText(fl, "}\n\n");

        seqComment(txtp, fl);
        m_cSeqParamsp = new AstTextBlock(fl, "long long "+m_libName+"_protectlib_seq_update(\n",
                                         false, true);
        m_cSeqParamsp->addText(fl, "void* vhandlep__V\n");
        txtp->addNodep(m_cSeqParamsp);
        txtp->addText(fl, ")\n");
        m_cSeqClksp = new AstTextBlock(fl, "{\n");
        castPtr(fl, m_cSeqClksp);
        txtp->addNodep(m_cSeqClksp);
        m_cSeqOutsp = new AstTextBlock(fl, "handlep__V->eval();\n");
        txtp->addNodep(m_cSeqOutsp);
        txtp->addText(fl, "return handlep__V->m_seqnum++;\n");
        txtp->addText(fl, "}\n\n");

        comboIgnoreComment(txtp, fl);
        m_cIgnoreParamsp = new AstTextBlock(fl, "void "+m_libName+"_protectlib_combo_ignore(\n",
                                            false, true);
        m_cIgnoreParamsp->addText(fl, "void* vhandlep__V\n");
        txtp->addNodep(m_cIgnoreParamsp);
        txtp->addText(fl, ")\n");
        txtp->addText(fl, "{ }\n\n");

        // Final
        finalComment(txtp, fl);
        txtp->addText(fl, "void "+m_libName+"_protectlib_final(void* vhandlep__V) {\n");
        castPtr(fl, txtp);
        txtp->addText(fl, "handlep__V->final();\n");
        txtp->addText(fl, "delete handlep__V;\n");
        txtp->addText(fl, "}\n\n");

        txtp->addText(fl, "}\n");
        m_cfilep->tblockp(txtp);
    }

    virtual void visit(AstVar* nodep) VL_OVERRIDE {
        if (!nodep->isIO()) return;
        if (VN_IS(nodep->dtypep(), UnpackArrayDType)) {
            nodep->v3error("Unsupported: unpacked arrays with protect-lib on "<<nodep->prettyNameQ());
        }
        if (nodep->direction() == VDirection::INPUT) {
            if (nodep->isUsedClock()
                || nodep->attrClocker() == VVarAttrClocker::CLOCKER_YES) {
                handleClock(nodep);
            } else {
                handleDataInput(nodep);
            }
        } else if (nodep->direction() == VDirection::OUTPUT) {
            handleOutput(nodep);
        } else {
            nodep->v3error("Unsupported: protect-lib port direction: "<<
                           nodep->direction().ascii());
        }
    }

    virtual void visit(AstNode* nodep) VL_OVERRIDE { }

    string cInputConnection(AstVar* varp) {
        string frstmt;
        bool useSetWSvlv = V3Task::dpiToInternalFrStmt(varp, varp->name(), true, frstmt);
        if (useSetWSvlv) {
            return frstmt+" handlep__V->"+varp->name()+", "+varp->name()+");\n";
        }
        return "handlep__V->"+varp->name()+" = "+frstmt+";\n";
    }

    void handleClock(AstVar* varp) {
        FileLine* fl = varp->fileline();
        handleInput(varp);
        m_seqPortsp->addNodep(varp->cloneTree(false));
        m_seqParamsp->addText(fl, varp->name()+"\n");
        m_clkSensp->addText(fl, "edge("+varp->name()+")");
        m_cSeqParamsp->addText(fl, varp->dpiArgType(true, false)+"\n");
        m_cSeqClksp->addText(fl, cInputConnection(varp));
    }

    void handleDataInput(AstVar* varp) {
        FileLine* fl = varp->fileline();
        handleInput(varp);
        m_comboPortsp->addNodep(varp->cloneTree(false));
        m_comboParamsp->addText(fl, varp->name()+"\n");
        m_comboIgnorePortsp->addNodep(varp->cloneTree(false));
        m_comboIgnoreParamsp->addText(fl, varp->name()+"\n");
        m_cComboParamsp->addText(fl, varp->dpiArgType(true, false)+"\n");
        m_cComboInsp->addText(fl, cInputConnection(varp));
        m_cIgnoreParamsp->addText(fl, varp->dpiArgType(true, false)+"\n");
    }

    void handleInput(AstVar* varp) {
        m_modPortsp->addNodep(varp->cloneTree(false));
    }

    void handleOutput(AstVar* varp) {
        FileLine* fl = varp->fileline();
        m_modPortsp->addNodep(varp->cloneTree(false));
        m_comboPortsp->addNodep(varp->cloneTree(false));
        m_comboParamsp->addText(fl, varp->name()+"_combo__V\n");
        m_seqPortsp->addNodep(varp->cloneTree(false));
        m_seqParamsp->addText(fl, varp->name()+"_tmp__V\n");

        AstNodeDType* comboDtypep = varp->dtypep()->cloneTree(false);
        m_comboDeclsp->addNodep(comboDtypep);
        m_comboDeclsp->addText(fl, " "+varp->name()+"_combo__V;\n");

        AstNodeDType* seqDtypep = varp->dtypep()->cloneTree(false);
        m_seqDeclsp->addNodep(seqDtypep);
        m_seqDeclsp->addText(fl, " "+varp->name()+"_seq__V;\n");

        AstNodeDType* tmpDtypep = varp->dtypep()->cloneTree(false);
        m_tmpDeclsp->addNodep(tmpDtypep);
        m_tmpDeclsp->addText(fl, " "+varp->name()+"_tmp__V;\n");

        m_nbAssignsp->addText(fl, varp->name()+"_seq__V <= "+varp->name()+"_tmp__V;\n");
        m_seqAssignsp->addText(fl, varp->name()+" = "+varp->name()+"_seq__V;\n");
        m_comboAssignsp->addText(fl, varp->name()+" = "+varp->name()+"_combo__V;\n");
        m_cComboParamsp->addText(fl, varp->dpiArgType(true, false)+"\n");
        m_cComboOutsp->addText(fl, V3Task::assignInternalToDpi(varp, false, true, "", "",
                                                               "handlep__V->"));
        m_cSeqParamsp->addText(fl, varp->dpiArgType(true, false)+"\n");
        m_cSeqOutsp->addText(fl, V3Task::assignInternalToDpi(varp, false, true, "", "",
                                                               "handlep__V->"));
    }

  public:
    explicit ProtectVisitor(AstNode* nodep):
        m_vfilep(NULL), m_cfilep(NULL), m_modPortsp(NULL),
        m_comboPortsp(NULL), m_seqPortsp(NULL), m_comboIgnorePortsp(NULL), m_comboDeclsp(NULL),
        m_seqDeclsp(NULL), m_tmpDeclsp(NULL), m_hashValuep(NULL),
        m_comboParamsp(NULL),
        m_clkSensp(NULL),
        m_comboIgnoreParamsp(NULL), m_seqParamsp(NULL), m_nbAssignsp(NULL), m_seqAssignsp(NULL),
        m_comboAssignsp(NULL), m_cHashValuep(NULL), m_cComboParamsp(NULL), m_cComboInsp(NULL),
        m_cComboOutsp(NULL), m_cSeqParamsp(NULL), m_cSeqClksp(NULL), m_cSeqOutsp(NULL),
        m_cIgnoreParamsp(NULL), m_libName(v3Global.opt.protectLib()),
        m_topName(v3Global.opt.prefix()), m_foundTop(false)
    {
        iterate(nodep);
    }
};

//######################################################################
// ProtectLib class functions

void V3ProtectLib::protect() {
    UINFO(2,__FUNCTION__<<": "<<endl);
    ProtectVisitor visitor(v3Global.rootp());
}
