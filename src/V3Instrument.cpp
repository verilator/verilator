// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator:
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2025 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Instrumentation's Transformations:
// The instrumentation configuration map is populated with the relevant nodes, as defined by the
// target string specified in the instrumentation configuration within the .vlt file.
// Additionally, the AST (Abstract Syntax Tree) is modified to insert the necessary extra nodes
// required for instrumentation.
// Furthermore, the links between Module, Cell, and Var nodes are adjusted to ensure correct
// connectivity for instrumentation purposes.
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Instrument.h"

#include "V3Control.h"
#include "V3File.h"

#include <iostream>
#include <regex>
#include <set>
#include <sstream>
#include <string>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//##################################################################################
// Instrumentation class finder
class InstrumentTargetFndr final : public VNVisitor {
    AstNetlist* m_netlist
        = nullptr;  // Enable traversing from the beginning if the visitor is to deep
    AstNodeModule* m_cellModp = nullptr;  // Stores the modulep of a Cell node
    AstModule* m_modp = nullptr;  // Stores the current modulep the visitor is looking at
    AstModule* m_targetModp = nullptr;  // Stores the targeted modulep
    bool m_error = false;  // Displays if there was already an error message earlier
    bool m_foundCellp = false;  // If the visitor found the relevant instance
    bool m_foundModp = false;  // If the visitor found the relevant model
    bool m_foundVarp = false;  // If the visitor found the relevant variable
    bool m_initModp = true;  // If the visitor is in the first module node of the netlist
    size_t m_instrIdx = 0;
    string m_currHier;  // Stores the current hierarchy of the visited nodes (Module, Cell, Var)
    string m_target;  // Stores the currently visited target string from the config map

    // METHODS
    //----------------------------------------------------------------------------------
    AstModule* findModp(AstNetlist* netlist, AstModule* modp) {
        for (AstNode* n = netlist->op1p(); n; n = n->nextp()) {
            if (VN_IS(n, Module) && VN_CAST(n, Module) == modp) { return VN_CAST(n, Module); }
        }
        return nullptr;
    }
    // Helper function to compare the target string starts with the given prefix
    bool cmpPrefix(const string& prefix, const string& target) {
        if (target.compare(0, prefix.size(), prefix) == 0
            && (target.size() == prefix.size() || target[prefix.size()] == '.')) {
            return true;
        }
        return false;
    }
    // Helper function to check if a parameter was already added to the tree previously
    bool hasParam(AstModule* modp) {
        for (AstNode* n = modp->op2p(); n; n = n->nextp()) {
            if (n->name() == "INSTRUMENT") { return true; }
        }
        return false;
    }
    // Helper function to check if a pin was already added to the tree previously
    bool hasPin(AstCell* cellp) {
        for (AstNode* n = cellp->paramsp(); n; n = n->nextp()) {
            if (n->name() == "INSTRUMENT") { return true; }
        }
        return false;
    }
    // Check if the multipleCellps flag is set for the given target
    bool hasMultiple(const std::string& target) {
        auto& instrCfg = V3Control::getInstrumentCfg();
        auto it = instrCfg.find(target);
        if (it != instrCfg.end()) { return it->second.multipleCellps; }
        return false;
    }
    // Check if the direct predecessor in the target string has been instrumented,
    // to create the correct link between the already instrumented module and the current one.
    bool hasPrior(AstModule* modulep, const string& target) {
        const auto& instrCfg = V3Control::getInstrumentCfg();
        auto priorTarget = reduce2Depth(split(target), KeyDepth::RelevantModule);
        auto it = instrCfg.find(priorTarget);
        return it != instrCfg.end() && it->second.processed;
    }
    bool targetHasFullName(const string& fullname, const string& target) {
        return fullname == target;
    }
    // Check if the given current Hierarchy matches the top module of the target (Pos: 0)
    bool targetHasTop(const string& currHier, const string& target) {
        return currHier == reduce2Depth(split(target), KeyDepth::TopModule);
    }
    // Check if the current hierarhy string matches the target string until the depth
    // to the module that includes the cell/instance pointing to the targeted module
    bool targetHasPointingMod(const string& pointingModuleName, const string& target) {
        return pointingModuleName == reduce2Depth(split(target), KeyDepth::RelevantModule);
    }
    // Check if the given prefix matches the beginning of the current target string
    bool targetHasPrefix(const string& prefix, const string& target) {
        return cmpPrefix(prefix, target);
    }
    // Helper Function to split a string by '.' and return a vector of tokens
    std::vector<std::string> split(const std::string& str) {
        static const std::regex dot_regex("\\.");
        std::sregex_token_iterator iter(str.begin(), str.end(), dot_regex, -1);
        std::sregex_token_iterator end;
        return std::vector<std::string>(iter, end);
    }
    // Helper function to reduce a given key to a certain hierarchy level.
    enum class KeyDepth { TopModule = 0, RelevantModule = 1, Instance = 2, FullKey = 3 };
    string reduce2Depth(std::vector<std::string> keyTokens, KeyDepth hierarchyLevel) {
        std::string reducedKey = keyTokens[0];
        if (hierarchyLevel == KeyDepth::TopModule) {
            return keyTokens[0];
        } else {
            int d = static_cast<int>(hierarchyLevel);
            for (size_t i = 1; i < keyTokens.size() - d; ++i) { reducedKey += "." + keyTokens[i]; }
            return reducedKey;
        }
    }
    // Helper function for adding the parameters into the tree
    void addParam(AstModule* modp) {
        AstVar* paramp = new AstVar{modp->fileline(), VVarType::GPARAM, "INSTRUMENT",
                                    VFlagChildDType{}, nullptr};
        paramp->valuep(new AstConst{modp->fileline(), AstConst::Signed32{}, 0});
        paramp->dtypep(paramp->valuep()->dtypep());
        paramp->ansi(true);
        modp->addStmtsp(paramp);
    }
    // Helper function for adding the parameters into the tree
    void addPin(AstCell* cellp, bool isInstrumentPath) {
        int pinnum = 0;
        if (isInstrumentPath) {
            for (AstNode* n = cellp->pinsp(); n; n = n->nextp()) { pinnum++; }
            AstPin* pinp = new AstPin{cellp->fileline(), pinnum + 1, "INSTRUMENT",
                                      // The pin is set to 1 to enable the instrumentation path
                                      new AstConst{cellp->fileline(), AstConst::Signed32{}, 1}};
            pinp->param(true);
            cellp->addParamsp(pinp);
        } else {
            for (AstNode* n = cellp->pinsp(); n; n = n->nextp()) { pinnum++; }
            AstPin* pinp = new AstPin{cellp->fileline(), pinnum + 1, "INSTRUMENT",
                                      new AstParseRef{cellp->fileline(), "INSTRUMENT"}};
            pinp->param(true);
            cellp->addParamsp(pinp);
        }
    }
    // Edit the instrumentation data for the cell in the map
    void editInstrData(AstCell* cellp, const string& target) {
        auto& instrCfg = V3Control::getInstrumentCfg();
        auto it = instrCfg.find(target);
        if (it != instrCfg.end()) { it->second.cellp = cellp; }
    }
    // Edit the instrumentation data for the pointing module in the map
    void editInstrData(AstModule* modulep, const string& target) {
        auto& instrCfg = V3Control::getInstrumentCfg();
        auto it = instrCfg.find(target);
        if (it != instrCfg.end()) { it->second.pointingModulep = modulep; }
    }
    // Check for multiple cells pointing to the next module
    void multCellForModp(AstCell* cellp) {
        std::multiset<AstNodeModule*> cellModps;
        for (AstNode* n = m_modp->op2p(); n; n = n->nextp()) {
            if (VN_IS(n, Cell)) { cellModps.insert(VN_CAST(n, Cell)->modp()); }
        }
        m_modp = nullptr;
        m_cellModp = cellp->modp();
        auto modpRepetition = cellModps.count(m_cellModp);
        if (modpRepetition > 1 && !targetHasFullName(m_currHier, m_target)) {
            setMultiple(m_target);
        }
    }
    // Insert the cell node that is/will pointing/point to the targeted module
    void setCell(AstCell* cellp, const string& target) {
        auto& instrCfg = V3Control::getInstrumentCfg();
        auto it = instrCfg.find(target);
        if (it != instrCfg.end()) { it->second.cellp = cellp; }
    }
    // Insert the original and instrumented module nodes to the map
    void setInstrModule(AstModule* origModulep, AstModule* instrModulep, const string& target) {
        auto& instrCfg = V3Control::getInstrumentCfg();
        auto it = instrCfg.find(target);
        if (it != instrCfg.end()) {
            it->second.origModulep = origModulep;
            it->second.instrModulep = instrModulep;
        }
    }
    // Set the multipleCellps flag
    void setMultiple(const string& target) {
        auto& instrCfg = V3Control::getInstrumentCfg();
        auto it = instrCfg.find(target);
        if (it != instrCfg.end()) { it->second.multipleCellps = true; }
    }
    // Insert the module node that includes the cell pointing to the targeted module
    // to the map
    void setPointingMod(AstModule* modulep, const string& target) {
        auto& instrCfg = V3Control::getInstrumentCfg();
        auto it = instrCfg.find(target);
        if (it != instrCfg.end()) { it->second.pointingModulep = modulep; }
    }
    // Set the processed flag
    void setProcessed(const string& target) {
        auto& instrCfg = V3Control::getInstrumentCfg();
        auto it = instrCfg.find(target);
        if (it != instrCfg.end()) { it->second.processed = true; }
    }
    // Insert the top module node of the netlist to the map
    void setTopMod(AstModule* modulep, const string& target) {
        auto& instrCfg = V3Control::getInstrumentCfg();
        auto it = instrCfg.find(target);
        if (it != instrCfg.end()) { it->second.topModulep = modulep; }
    }
    // Insert the original and instrumented variable nodes to the map
    void setVar(AstVar* varp, AstVar* instVarp, const string& target) {
        auto& instrCfg = V3Control::getInstrumentCfg();
        auto it = instrCfg.find(target);
        if (it != instrCfg.end()) {
            for (auto& entry : it->second.entries) {
                if (entry.varTarget == varp->name()) {
                    entry.origVarps = varp;
                    entry.instrVarps = instVarp;
                    entry.found = true;
                    return;
                }
            }
        }
    }

    // VISITORS
    //----------------------------------------------------------------------------------

    //ASTMODULE VISITOR FUNCTION:
    //Iterates over the existing module nodes in the netlist.
    //For the first module in the netlist the node name is checked if it is at the first position
    //in the target string provided by the configuration file. If not an error is thown, otherwise
    //the modules is checked for an already existing INSTRUMENT parameter. If there is no
    //INSTRUMENT parameter present we add it to the module. This parameter is used to control the
    //instrumentation of the target. The module is then added to the map of the instrumentation
    //configs as the top module. Additionally the hierarchy the function viewed is currently add is
    //initialized with the module name. This module hierarchy is used to identify the correct
    //target path in the netlist. The function iterates over the children of the module, with the
    //Cells and Vars beeing the relevant targets.

    //After the iteration of the children the m_modp variable needs to be set by the Cell visitor
    //to continue or there needs no suitable cell to be found. (See CELL VISITOR FUNCTION & VAR
    //VISITOR FUNCTION) Since the module from the m_modp can appear earlier in the tree the
    //fundModp function is used to iterate over the netlift from the beginning to find the module.
    //The module node displayed by the m_modp variable is then checked if this is the module
    //containing the target variable (relevant module) or if it the module containing the cell
    //pointing to the relevant module (pointing module). If the module node suits one of these two
    //conditions the module nodes are added to the instrumentation configs map. Independetly from
    //these conditions the INSTRUMENT parameter is added to the module nodes in the target path.
    //This parameter is used to control the instrumentation of the target.
    void visit(AstModule* nodep) override {
        if (m_initModp) {
            if (targetHasTop(nodep->name(), m_target)) {
                m_foundModp = true;
                m_modp = nodep;
                m_currHier = nodep->name();
                if (!hasParam(nodep)) { addParam(nodep); }
                if (string::npos == m_target.rfind('.')) {
                    m_targetModp = nodep;
                    m_foundCellp = true;  // Set to true since there is no Instance that the cell
                                          // visitor could find
                }
                setTopMod(nodep, m_target);
                iterateChildren(nodep);
            } else if (!m_foundModp && nodep->name() == "@CONST-POOL@") {
                v3error("Verilator-configfile': could not find initial 'module' in "
                        "'module.instance.__'"
                        " ... Target: '"
                        << m_target << "'");
                m_initModp = false;
                m_error = true;
            }
        } else if (m_cellModp != nullptr
                   && (nodep = findModp(m_netlist, VN_CAST(m_cellModp, Module))) != nullptr) {
            if (targetHasFullName(m_currHier, m_target)) {
                AstModule* instrModp = nullptr;
                m_foundModp = true;
                m_targetModp = nodep;
                m_cellModp = nullptr;
                // Check for prior changes made to the tree
                if (hasPrior(nodep, m_currHier)) {
                    auto& instrCfg = V3Control::getInstrumentCfg();
                    instrModp
                        = instrCfg.find(reduce2Depth(split(m_currHier), KeyDepth::RelevantModule))
                              ->second.instrModulep;
                    editInstrData(instrModp, m_currHier);
                    AstCell* cellp = nullptr;
                    for (AstNode* n = instrModp->op2p(); n; n = n->nextp()) {
                        if (VN_IS(n, Cell) && (VN_CAST(n, Cell)->modp() == nodep)
                            && instrCfg.find(m_currHier)->second.cellp->name() == n->name()) {
                            cellp = VN_CAST(n, Cell);
                            break;
                        }
                    }
                    editInstrData(cellp, m_currHier);
                }
                if (!hasParam(nodep)) { addParam(nodep); }
                instrModp = nodep->cloneTree(false);
                instrModp->name(nodep->name() + "__inst__" + std::to_string(m_instrIdx));
                if (hasMultiple(m_target)) { instrModp->inLibrary(true); }
                setInstrModule(nodep, instrModp, m_target);
                iterateChildren(nodep);
            } else if (targetHasPointingMod(m_currHier, m_target)) {
                m_foundModp = true;
                m_foundCellp = false;
                m_modp = nodep;
                m_cellModp = nullptr;
                if (!hasParam(nodep)) { addParam(nodep); }
                setPointingMod(nodep, m_target);
                iterateChildren(nodep);
            } else if (targetHasPrefix(m_currHier, m_target)) {
                m_foundModp = true;
                m_foundCellp = false;
                m_modp = nodep;
                m_cellModp = nullptr;
                if (!hasParam(nodep)) { addParam(nodep); }
                iterateChildren(nodep);
            }
        } else if (!m_error && !m_foundCellp) {
            v3error("Verilator-configfile: could not find 'instance' in "
                    "'__.instance.__' ... Target string: '"
                    << m_target << "'");
        } else if (!m_error && !m_foundVarp) {
            v3error("Verilator-configfile': could not find '.var' in '__.module.var'"
                    " ... Target: '"
                    << m_target << "'");
        }
    }

    //ASTCELL VISITOR FUNCTION:
    //This cell visitor function is called if the module visitor function found a module that
    //matches the target string from the config. The first function call should be when visiting
    //the initial module in the netlist. When a cell is found that matches the target string and is
    //not marked as found, the current hierarchy is updated and the cell marked as found.
    //Additionally, if this is the cell in the initial module, the initial module flag is set to
    //false. The in the current module existing cells are checked if there are multiple cells
    //linking to the next module in the target string. After that the m_modp is updated to match
    //the cell's module pointer, which is needed for the next call of the module visitor. Next the
    //pin for the INSTRUMENT parameter is added to the cell. This parameter is added either as a
    //constant or as a reference, depending on the traversal stage. If there are multiple cells
    //linking to the next module in the target string, the multiple flag is set in the
    //instrumentation config map. For the inistial module the found cell is then added to the
    //instrumentation configuration map with the current hierarchy as the target path. Otherwise
    //the cell is added to the instrumentation configuration map, when the current hierarchy with
    //the cell name fully matches a target path, with the last two entrances removed (Module, Var).
    //This function ensures that the correct cells in the design hierarchy are instrumented and
    //tracked, supporting both unique and repeated module instances.
    void visit(AstCell* nodep) override {
        if (m_initModp) {
            if (targetHasFullName(m_currHier + "." + nodep->name(), m_target)) {
                m_foundCellp = true;
                m_foundModp = false;
                m_initModp = false;
                m_currHier = m_currHier + "." + nodep->name();
                if (!hasPin(nodep)) { addPin(nodep, false); }
                multCellForModp(nodep);
                setCell(nodep, m_target);
            } else if (targetHasPrefix(m_currHier + "." + nodep->name(), m_target)) {
                m_foundCellp = true;
                m_foundModp = false;
                m_initModp = false;
                m_currHier = m_currHier + "." + nodep->name();
                if (!hasPin(nodep)) { addPin(nodep, true); }
                multCellForModp(nodep);
                setCell(nodep, m_target);
            } else if (!m_foundCellp && !VN_IS(nodep->nextp(), Cell)) {
                v3error("Verilator-configfile': could not find initial 'instance' in "
                        "'topModule.instance.__' ... Target string: '"
                        << m_target << "'");
                m_error = true;
                m_initModp = false;
            }
        } else if (m_modp != nullptr
                   && targetHasFullName(m_currHier + "." + nodep->name(), m_target)) {
            m_foundCellp = true;
            m_foundModp = false;
            m_currHier = m_currHier + "." + nodep->name();
            if (!hasPin(nodep)) { addPin(nodep, false); }
            multCellForModp(nodep);
            setCell(nodep, m_target);
        } else if (m_modp != nullptr
                   && targetHasPrefix(m_currHier + "." + nodep->name(), m_target)) {
            m_foundCellp = true;
            m_foundModp = false;
            m_currHier = m_currHier + "." + nodep->name();
            if (!hasPin(nodep)) { addPin(nodep, false); }
            multCellForModp(nodep);
        }
    }

    //ASTVAR VISITOR FUNCTION:
    //The var visitor function is used to find the variable that matches the target string from the
    //config. This is only done if the Cell visitor does not find a matching cell in the current
    //module of the target hierarchy. Since we therefore know that we will not traverse any further
    //in the hierarchy of the model, we can check for this variable. If a variable is found, with
    //its name added to the current hierarchy, that siuts the target string, an edited version and
    //the original version are added to the instrumentation config map.
    void visit(AstVar* nodep) override {
        if (m_targetModp != nullptr) {
            const InstrumentTarget& target
                = V3Control::getInstrumentCfg().find(m_currHier)->second;
            for (const auto& entry : target.entries) {
                if (nodep->name() == entry.varTarget) {
                    int width = 0;
                    AstBasicDType* basicp = nodep->basicp();
                    bool literal = basicp->isLiteralType();
                    bool implicit = basicp->implicit();
                    if (!implicit && nodep->basicp()->rangep() != nullptr) {
                        // Since the basicp is not implicit and there is a rangep, we can use the
                        // rangep for deducting the width
                        width = nodep->basicp()->rangep()->elementsConst();
                    }
                    bool isUnsupportedType = !literal && !implicit;
                    bool isUnsupportedWidth = literal && width > 64;
                    if (isUnsupportedType || isUnsupportedWidth) {
                        v3error("Verilator-configfile: target variable '"
                                << nodep->name() << "' in '" << m_currHier
                                << "' must be a supported type!");
                        return;
                    }
                    AstVar* varp = nodep->cloneTree(false);
                    varp->name("tmp_" + nodep->name());
                    varp->origName("tmp_" + nodep->name());
                    varp->trace(true);
                    if (varp->varType() == VVarType::WIRE) { varp->varType(VVarType::VAR); }
                    setVar(nodep, varp, m_target);
                    if (string::npos == m_currHier.rfind('.')) {
                        AstModule* modulep = m_modp->cloneTree(false);
                        modulep->name(m_modp->name() + "__inst__" + std::to_string(m_instrIdx));
                        setInstrModule(m_modp, modulep, m_currHier);
                        m_initModp = false;
                    }
                    m_foundVarp = true;
                } else if (nodep->nextp() == nullptr && !entry.found) {
                    v3error("Verilator-configfile': could not find defined 'var' in "
                            "'topModule.instance.var' ... Target string: '"
                            << m_target + "." + entry.varTarget << "'");
                    return;
                }
            }
        }
    };

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTOR
    //-------------------------------------------------------------------------------
    explicit InstrumentTargetFndr(AstNetlist* nodep) {
        const auto& instrCfg = V3Control::getInstrumentCfg();
        for (const auto& pair : instrCfg) {
            m_netlist = nodep;
            m_target = pair.first;
            m_initModp = true;
            m_currHier = "";
            iterate(nodep);
            setProcessed(m_target);
            m_foundModp = false;
            m_foundCellp = false;
            m_foundVarp = false;
            m_error = false;
            m_targetModp = nullptr;
            m_modp = nullptr;
            m_instrIdx++;
        }
    };
    ~InstrumentTargetFndr() override = default;
};

//##################################################################################
// Instrumentation class functions
class InstrumentFunc final : public VNVisitor {
    bool m_assignw = false;  // Flag if a assignw exists in the netlist
    bool m_assignNode = false; // Set to true to indicate that the visitor is in an assign
    bool m_addedport = false;  // Flag if a port was already added
    bool m_addedTask = false;  // Flag if a task was already added
    bool m_addedFunc = false;  // Flag if a function was already added
    bool m_interface = false;  // Flag if the ParseRef node is part of an interface
    int m_pinnum = 0;  // Pinnumber for the new Port nodes
    string m_targetKey;  // Stores the target string from the instrumentation config
    string m_task_name;
    size_t m_targetIndex = 0;  // Index of the target variable in the instrumentation config
    AstAlways* m_alwaysp = nullptr;  // Stores the added always node
    AstAssignW* m_assignwp = nullptr;  // Stores the added assignw node
    AstGenBlock* m_instGenBlock
        = nullptr;  // Store the GenBlock node for instrumentation hierarchy check
    AstTask* m_taskp = nullptr;  // // Stores the created task node
    AstFunc* m_funcp = nullptr;  // Stores the created function node
    AstFuncRef* m_funcrefp = nullptr;  // Stores the created funcref node
    AstLoop* m_loopp = nullptr;  // Stores the created loop pointer
    AstTaskRef* m_taskrefp = nullptr;  // Stores the created taskref node
    AstModule* m_current_module = nullptr;  // Stores the currenty visited module
    AstModule* m_current_module_cell_check
        = nullptr;  // Stores the module node(used by cell visitor)
    AstVar* m_tmp_varp = nullptr;  // Stores the instrumented variable node
    AstVar* m_orig_varp = nullptr;  // Stores the original variable node
    AstVar* m_orig_varp_instMod
        = nullptr;  // Stores the original variable node in instrumented module node
    AstVar* m_dpi_trigger
        = nullptr;  // Stores the variable noded for the dpi-trigger, which ensures the changing of
                    // a signal and the execution of the DPI function
    AstPort* m_orig_portp = nullptr;  // Stores the original port node

    // METHODS
    //----------------------------------------------------------------------------------
    // Find the relevant instrumentation config in the map corresponding to the given key
    const InstrumentTarget* getInstrCfg(const std::string& key) {
        const auto& map = V3Control::getInstrumentCfg();
        auto instrCfg = map.find(key);
        if (instrCfg != map.end()) {
            return &instrCfg->second;
        } else {
            return nullptr;
        }
    }
    // Get the Cell nodep pointer from the configuration map for the given key
    AstCell* getMapEntryCell(const std::string& key) {
        if (auto cfg = getInstrCfg(key)) { return cfg->cellp; }
        return nullptr;
    }
    // Get the instrumented Module node pointer from the configuration map for the given key
    AstModule* getMapEntryInstModule(const std::string& key) {
        if (auto cfg = getInstrCfg(key)) { return cfg->instrModulep; }
        return nullptr;
    }
    // Get the Module node pointer pointing to the instrumented/original module from the
    // configuration map for the given key
    AstModule* getMapEntryPointingModule(const std::string& key) {
        if (auto cfg = getInstrCfg(key)) { return cfg->pointingModulep; }
        return nullptr;
    }
    // Get the instrumented variable node pointer from the configuration map for the given key
    AstVar* getMapEntryInstVar(const std::string& key, size_t index) {
        if (auto cfg = getInstrCfg(key)) {
            const auto& entries = cfg->entries;
            if (index < entries.size()) { return entries[index].instrVarps; }
        }
        return nullptr;
    }
    // Get the original variable node pointer from the configuration map for the given key
    AstVar* getMapEntryVar(const std::string& key, size_t index) {
        if (auto cfg = getInstrCfg(key)) {
            const auto& entries = cfg->entries;
            if (index < entries.size()) { return entries[index].origVarps; }
        }
        return nullptr;
    }
    // Check if the given module node pointer is an instrumented module entry in the configuration
    // map for the given key
    bool isInstModEntry(AstModule* nodep, const std::string& key) {
        const auto& map = V3Control::getInstrumentCfg();
        const auto instrCfg = map.find(key);
        if (instrCfg != map.end() && instrCfg->second.instrModulep == nodep) {
            return true;
        } else {
            return false;
        }
    }
    // Check if the given module node pointer is the top module entry in the configuration map
    bool isTopModEntry(AstModule* nodep) {
        auto& instrCfg = V3Control::getInstrumentCfg();
        for (const auto& pair : instrCfg) {
            if (nodep == pair.second.topModulep) { return true; }
        }
        return false;
    }
    // Check if the given module node pointer is the pointing module entry in the configuration map
    bool isPointingModEntry(AstModule* nodep) {
        auto& instrCfg = V3Control::getInstrumentCfg();
        for (const auto& pair : instrCfg) {
            if (nodep == pair.second.pointingModulep) { return true; }
        }
        return false;
    }
    // Check if the given module node pointer has already been instrumented/done flag has been set
    bool isDone(AstModule* nodep) {
        auto& instrCfg = V3Control::getInstrumentCfg();
        for (const auto& pair : instrCfg) {
            if (nodep == pair.second.instrModulep) { return pair.second.done; }
        }
        return true;
    }
    // Check if the multipleCellps flag is set for the given key in the configuration map
    bool hasMultiple(const std::string& key) {
        const auto& map = V3Control::getInstrumentCfg();
        const auto instrCfg = map.find(key);
        if (instrCfg != map.end()) {
            return instrCfg->second.multipleCellps;
        } else {
            return false;
        }
    }
    // Check if the module and instances defined in the target string were found in
    // the previous step
    bool hasNullptr(const std::pair<const string, InstrumentTarget>& pair) {
        bool moduleNullptr = pair.second.origModulep == nullptr;
        bool cellNullptr = pair.second.cellp == nullptr;
        return moduleNullptr || cellNullptr;
    }
    // Check if the, in the target string, defined variable was found in the previous step
    bool isFound(const std::pair<const string, InstrumentTarget>& pair) {
        for (auto& entry : pair.second.entries) {
            if (entry.found == false) { return entry.found; }
        }
        return true;
    }
    // Get the fault case for the given key in the configuration map
    int getMapEntryFaultCase(const std::string& key, size_t index) {
        const auto& map = V3Control::getInstrumentCfg();
        const auto instrCfg = map.find(key);
        if (instrCfg != map.end()) {
            const auto& entries = instrCfg->second.entries;
            if (index < entries.size()) { return entries[index].instrID; }
            return -1;  // Return -1 if index is out of bounds
        } else {
            return -1;
        }
    }
    // Get the instrumentation function name for the given key in the configuration map
    string getMapEntryFunction(const std::string& key, size_t index) {
        const auto& map = V3Control::getInstrumentCfg();
        const auto instrCfg = map.find(key);
        if (instrCfg != map.end()) {
            const auto& entries = instrCfg->second.entries;
            if (index < entries.size()) { return entries[index].instrFunc; }
            return "";
        } else {
            return "";
        }
    }
    // Set the done flag for the given module node pointer in the configuraiton map
    void setDone(AstModule* nodep) {
        auto& instrCfg = V3Control::getInstrumentCfg();
        for (auto& pair : instrCfg) {
            if (nodep == pair.second.instrModulep) { pair.second.done = true; }
        }
    }
    void instrAssigns(AstNodeAssign* nodep) {
        if (m_current_module != nullptr && m_orig_varp != nullptr && m_assignwp != nodep) {
            m_assignNode = true;
            VDirection dir = m_orig_varp->direction();
            if (dir == VDirection::INPUT || dir == VDirection::NONE) {
                // Hier muss was mit dem rhsp gemacht werden
                AstNodeExpr* rhsp = nodep->rhsp();
                if(rhsp->type() != VNType::ParseRef) {
                    // Muss ich hier loopen?
                    for(AstNode* n = rhsp->op1p(); n; n = n->nextp()) {
                        if(n->type() == VNType::ParseRef && n->name() == m_orig_varp->name()) {
                            n->name(m_tmp_varp->name());
                            break;
                        }
                    }
                } else {
                    if(rhsp->name() == m_orig_varp->name()) {
                        rhsp->name(m_tmp_varp->name());
                    }
                }
            }
        } else if (nodep == m_assignwp) {
            iterateChildren(nodep);
        }
        m_assignNode = false;
    }
    AstNode* createDPIInterface(AstModule* nodep, AstVar* orig_varp, const string& task_name) {
        AstVar* varp = nullptr;
        if (orig_varp->basicp()->isLiteralType() || orig_varp->basicp()->implicit()) {
            int width = 0;
            if (!orig_varp->basicp()->implicit() && orig_varp->basicp()->rangep() != nullptr) {
                width = orig_varp->basicp()->rangep()->elementsConst();
            } else {
                // Since Var is implicit set/assume the width as 1 like in V3Width.cpp in the
                // AstVar visitor
                width = 1;
            }
            if (width <= 1) {
                varp = new AstVar{nodep->fileline(), VVarType::VAR, task_name, VFlagChildDType{},
                                  new AstBasicDType{nodep->fileline(), VBasicDTypeKwd::BIT}};
                varp->lifetime(VLifetime::AUTOMATIC_IMPLICIT);
                varp->funcReturn(true);
                varp->direction(VDirection::OUTPUT);
            } else if (width <= 8) {
                varp = new AstVar{nodep->fileline(), VVarType::VAR, task_name, VFlagChildDType{},
                                  new AstBasicDType{nodep->fileline(), VBasicDTypeKwd::BYTE}};
                varp->lifetime(VLifetime::AUTOMATIC_IMPLICIT);
                varp->funcReturn(true);
                varp->direction(VDirection::OUTPUT);
            } else if (width <= 16) {
                varp = new AstVar{nodep->fileline(), VVarType::VAR, task_name, VFlagChildDType{},
                                  new AstBasicDType{nodep->fileline(), VBasicDTypeKwd::SHORTINT}};
                varp->lifetime(VLifetime::AUTOMATIC_IMPLICIT);
                varp->funcReturn(true);
                varp->direction(VDirection::OUTPUT);
            } else if (width <= 32) {
                varp = new AstVar{nodep->fileline(), VVarType::VAR, task_name, VFlagChildDType{},
                                  new AstBasicDType{nodep->fileline(), VBasicDTypeKwd::INT}};
                varp->lifetime(VLifetime::AUTOMATIC_IMPLICIT);
                varp->funcReturn(true);
                varp->direction(VDirection::OUTPUT);
            } else if (width <= 64) {
                varp = new AstVar{nodep->fileline(), VVarType::VAR, task_name, VFlagChildDType{},
                                  new AstBasicDType{nodep->fileline(), VBasicDTypeKwd::LONGINT}};
                varp->lifetime(VLifetime::AUTOMATIC_IMPLICIT);
                varp->funcReturn(true);
                varp->direction(VDirection::OUTPUT);
            }
            return new AstFunc{nodep->fileline(), m_task_name, nullptr, varp};
        } else {
            return new AstTask{nodep->fileline(), m_task_name, nullptr};
        }
    }

    // Visitors
    //----------------------------------------------------------------------------------

    //ASTNETLIST VISITOR FUNCTION:
    //Loop over map entries for module nodes and add them to the tree
    void visit(AstNetlist* nodep) override {
        const auto& instrCfg = V3Control::getInstrumentCfg();
        for (const auto& pair : instrCfg) {
            if (hasNullptr(pair) || !isFound(pair)) {
                v3error(
                    "Verilator-configfile: Incomplete instrumentation configuration for target '"
                    << pair.first
                    << "'. Please check previous Errors from V3Instrument:findTargets and ensure"
                    << " all necessary components are correct defined.");
            } else {
                nodep->addModulesp(pair.second.instrModulep);
                m_targetKey = pair.first;
                iterateChildren(nodep);
                m_assignw = false;
            }
        }
    }

    //ASTMODULE VISITOR FUNCTION:
    //This function is called for each module node in the netlist.
    //It checks if the module node is part of the instrumentation configuratio map.
    //Depending on the type of the module node (Instrumented, Top, Pointing, or Original),
    //it performs different actions:
    //    - If the module is an instrumented module entry and has not been done, it creates a new
    //task for the instrumentation function, adds the temporary variable, and creates a task
    //reference to the instrumentation function.
    //    - If the module is a pointing module or a top module and has no multiple cellps, it
    //    checks
    //the cell for the target key and counts the pins. This pin count is used in the CELL VISITOR
    //FUNCTION to set a siutable pin number for the INSTRUMENT parameter. Look there fore further
    //information.
    //    - If the module is a pointing module and has multiple cellps, it creates a begin block
    //    with
    //a conditional statement to select between the instrumented and original cell.
    //      Additionally like in the previous case, the pin count is used to set a suitable pin
    //number for the INSTRUMENT parameter.\ Since the cell which need to be edited are located not
    //in the original module, but in the pointing/top module, the current_module_cell_check
    //variable is set to the module visited by the function and fulfilling this condition.
    void visit(AstModule* nodep) override {
        const auto& instrCfg = V3Control::getInstrumentCfg().find(m_targetKey);
        const InstrumentTarget& target = instrCfg->second;
        const auto& entries = target.entries;
        for (m_targetIndex = 0; m_targetIndex < entries.size(); ++m_targetIndex) {
            m_tmp_varp = getMapEntryInstVar(m_targetKey, m_targetIndex);
            m_orig_varp = getMapEntryVar(m_targetKey, m_targetIndex);
            m_task_name = getMapEntryFunction(m_targetKey, m_targetIndex);
            if (isInstModEntry(nodep, m_targetKey) && !isDone(nodep)) {
                m_current_module = nodep;
                for (AstNode* n = nodep->op2p(); n; n = n->nextp()) {
                    if (VN_IS(n, Task) && n->name() == m_task_name) {
                        m_taskp = VN_CAST(n, Task);
                        m_addedTask = true;
                        break;
                    }
                    if (VN_IS(n, Func) && n->name() == m_task_name) {
                        m_funcp = VN_CAST(n, Func);
                        m_addedFunc = true;
                        break;
                    }
                }
                if (!m_addedTask && !m_addedFunc) {
                    auto m_dpip = createDPIInterface(nodep, m_orig_varp, m_task_name);
                    if (VN_IS(m_dpip, Func)) {
                        m_funcp = VN_CAST(m_dpip, Func);
                        m_funcp->dpiImport(true);
                        m_funcp->prototype(true);
                        m_funcp->verilogFunction(true);
                        nodep->addStmtsp(m_funcp);
                    }
                    if (VN_IS(m_dpip, Task)) {
                        m_taskp = VN_CAST(m_dpip, Task);
                        m_taskp->dpiImport(true);
                        m_taskp->prototype(true);
                        nodep->addStmtsp(m_taskp);
                    }
                }
                if (m_orig_varp->direction() == VDirection::INPUT) {
                    m_tmp_varp->varType(VVarType::VAR);
                    m_tmp_varp->direction(VDirection::NONE);
                    m_tmp_varp->trace(true);
                }
                nodep->addStmtsp(m_tmp_varp);
                // Pruefung einbauen ob das schon passiert ist.
                if (m_dpi_trigger == nullptr) {
                    m_dpi_trigger = new AstVar{
                        nodep->fileline(), VVarType::VAR, "dpi_trigger", VFlagChildDType{},
                        new AstBasicDType{nodep->fileline(), VBasicDTypeKwd::BIT,
                                          VSigning::NOSIGN}};
                    m_dpi_trigger->trace(false);
                    nodep->addStmtsp(m_dpi_trigger);
                    m_loopp = new AstLoop{nodep->fileline()};
                    AstInitial* initialp = new AstInitial{
                        nodep->fileline(), new AstBegin{nodep->fileline(), "", m_loopp, false}};
                    nodep->addStmtsp(initialp);
                }
                if (m_taskp != nullptr) {
                    m_taskrefp = new AstTaskRef{
                        nodep->fileline(), m_task_name,
                        new AstArg{nodep->fileline(), m_tmp_varp->name(),
                                   new AstVarRef{nodep->fileline(), m_tmp_varp, VAccess::WRITE}}};
                    m_taskrefp->taskp(m_taskp);
                    m_alwaysp
                        = new AstAlways{nodep->fileline(), VAlwaysKwd::ALWAYS, nullptr, nullptr};
                    nodep->addStmtsp(m_alwaysp);
                }
                if (m_funcp != nullptr) {
                    m_funcrefp = new AstFuncRef{nodep->fileline(), m_funcp, nullptr};
                    m_assignwp = new AstAssignW{
                        nodep->fileline(), new AstParseRef{nodep->fileline(), m_tmp_varp->name()},
                        m_funcrefp};
                    AstAlways* alwaysp = new AstAlways{nodep->fileline(), VAlwaysKwd::CONT_ASSIGN,
                                                       nullptr, m_assignwp};
                    nodep->addStmtsp(alwaysp);
                }
                if (m_targetIndex == entries.size() - 1) { setDone(nodep); }
                for (AstNode* n = nodep->op2p(); n; n = n->nextp()) {
                    if (VN_IS(n, Port)) { m_pinnum = VN_CAST(n, Port)->pinNum(); }
                }
                iterateChildren(nodep);
            } else if ((std::count(m_targetKey.begin(), m_targetKey.end(), '.') > 0)
                       && (isPointingModEntry(nodep) || isTopModEntry(nodep))
                       && !hasMultiple(m_targetKey)) {
                m_current_module_cell_check = nodep;
                AstCell* instCellp = getMapEntryCell(m_targetKey);
                for (AstNode* n = instCellp->pinsp(); n; n = n->nextp()) { m_pinnum++; }
                iterateChildren(nodep);
            } else if (isPointingModEntry(nodep) && hasMultiple(m_targetKey)) {
                m_current_module_cell_check = nodep;
                AstCell* instCellp = getMapEntryCell(m_targetKey)->cloneTree(false);
                instCellp->modp(getMapEntryInstModule(m_targetKey));
                for (AstNode* n = instCellp->pinsp(); n; n = n->nextp()) { m_pinnum++; }
                m_instGenBlock = new AstGenBlock{nodep->fileline(), "", instCellp, false};
                AstGenIf* genifp = new AstGenIf{
                    nodep->fileline(), new AstParseRef{nodep->fileline(), "INSTRUMENT"},
                    m_instGenBlock,
                    new AstGenBlock{nodep->fileline(), "",
                                    getMapEntryCell(m_targetKey)->cloneTree(false), false}};

                nodep->addStmtsp(genifp);
                iterateChildren(m_instGenBlock);
                iterateChildren(nodep);
            }
            m_current_module = nullptr;
            m_current_module_cell_check = nullptr;
            m_alwaysp = nullptr;
            m_taskp = nullptr;
            m_taskrefp = nullptr;
            m_addedTask = false;
            m_funcp = nullptr;
            m_addedFunc = false;
            m_addedport = false;
            m_instGenBlock = nullptr;
        }
        m_dpi_trigger = nullptr;
        m_loopp = nullptr;
        m_targetIndex = 0;
    }

    //ASTPORT VISITOR FUNCTION:
    //When the target variable is an ouput port, this function is called.
    //If no port is added yet, two new ports are added to the current module.
    //This enabled the instrumentation of the ouput port and link this instrumented port to the
    //modules reading from the original port. The idea behind this function is to set the
    //instrumented port on the position of the original port in the module and move the original
    //port to another pin number. This should ensure the linking over the name and the port
    //position in the module should work.
    void visit(AstPort* nodep) override {
        if (m_current_module != nullptr && m_orig_varp->direction() == VDirection::OUTPUT
            && nodep->name() == m_orig_varp->name() && !m_addedport) {
            m_orig_portp = nodep->cloneTree(false);
            nodep->unlinkFrBack();
            nodep->deleteTree();
            m_current_module->addStmtsp(
                new AstPort{nodep->fileline(), m_orig_portp->pinNum(), m_tmp_varp->name()});
            m_current_module->addStmtsp(
                new AstPort{nodep->fileline(), m_pinnum + 1, m_orig_portp->name()});
            m_addedport = true;
        }
    }

    //ASTCELL VISITOR FUNCTION:
    //This function visits the cell nodes in the module pointing to the instrumented module.
    //Depending if hasMultiple is set for the target key, two different actions are performed:
    //    - If hasMultiple is false, the cell is modified to link to the instrumented module and
    //    the
    //children are iterated. This ensures that the instrumented mopdule is used in the cell. Also
    //if the original variable is an output variable, the children of this cell nodes are visited
    //by the ASTPIN VISITOR FUNCTION.
    //    - If hasMultiple is true, the cell is unlinked from the back and deleted.
    //      This ensures that the cell is not used anymore in the module, and the conditional
    //statment deciding between the instrumented and the original cell can be created/used. A third
    //action is performed if the variable beeing instrumented is an ouput variable. In this case
    //the children of this cell nodes are visited by the ASTPIN VISITOR FUNCTION.
    void visit(AstCell* nodep) override {
        if (m_current_module_cell_check != nullptr && !hasMultiple(m_targetKey)
            && nodep == getMapEntryCell(m_targetKey)) {
            nodep->modp(getMapEntryInstModule(m_targetKey));
            if (m_orig_varp->direction() == VDirection::OUTPUT) { iterateChildren(nodep); }
        } else if (m_current_module_cell_check != nullptr && hasMultiple(m_targetKey)
                   && nodep == getMapEntryCell(m_targetKey)) {
            nodep->unlinkFrBack();
            nodep->deleteTree();
        } else if (m_instGenBlock != nullptr && nodep->modp() == getMapEntryInstModule(m_targetKey)
                   && m_orig_varp->direction() == VDirection::OUTPUT) {
            iterateChildren(nodep);
        } else if (m_current_module != nullptr && m_orig_varp->direction() == VDirection::INPUT) {
            iterateChildren(nodep);
        }
    }

    //ASTPIN VISITOR FUNCTION:
    //The function is used to change the pin name of the original variable to the instrumented
    //variable name. This is done to ensure that the pin is correctly linked to the instrumented
    //variable in the cell.
    void visit(AstPin* nodep) override {
        if (nodep->name() == m_orig_varp->name()
            && m_orig_varp->direction() == VDirection::INPUT) {
            iterateChildren(nodep);
        } else if (nodep->name() == m_orig_varp->name()) {
            nodep->name(m_tmp_varp->name());
        }
    }

    //ASTTASK VISITOR FUNCTION:
    //The function is used to further specify the task node created at the module visitor.
    void visit(AstTask* nodep) override {
        if (m_addedTask == false && nodep == m_taskp && m_current_module != nullptr) {
            AstVar* instrID = nullptr;
            AstVar* var_x_task = nullptr;
            AstVar* tmp_var_task = nullptr;

            instrID = new AstVar{nodep->fileline(), VVarType::PORT, "instrID", VFlagChildDType{},
                                 new AstBasicDType{nodep->fileline(), VBasicDTypeKwd::INT,
                                                   VSigning::SIGNED, 32, 0}};
            instrID->direction(VDirection::INPUT);

            var_x_task = m_orig_varp->cloneTree(false);
            var_x_task->varType(VVarType::PORT);
            var_x_task->direction(VDirection::INPUT);

            tmp_var_task = m_tmp_varp->cloneTree(false);
            tmp_var_task->varType(VVarType::PORT);
            tmp_var_task->direction(VDirection::OUTPUT);

            nodep->addStmtsp(instrID);
            nodep->addStmtsp(var_x_task);
            nodep->addStmtsp(tmp_var_task);
        }
    }

    //ASTFUNC VISITOR FUNCITON:
    //The function is used to further specify the function node created at the module visitor.
    void visit(AstFunc* nodep) override {
        if (m_addedFunc == false && nodep == m_funcp && m_current_module != nullptr) {
            AstVar* instrID = nullptr;
            AstVar* dpi_trigger = nullptr;
            AstVar* var_x_func = nullptr;

            instrID = new AstVar{nodep->fileline(), VVarType::PORT, "instrID", VFlagChildDType{},
                                 new AstBasicDType{nodep->fileline(), VBasicDTypeKwd::INT,
                                                   VSigning::SIGNED, 32, 0}};
            instrID->direction(VDirection::INPUT);

            var_x_func = m_orig_varp->cloneTree(false);
            var_x_func->varType(VVarType::PORT);
            var_x_func->direction(VDirection::INPUT);
            dpi_trigger = m_dpi_trigger->cloneTree(false);
            dpi_trigger->varType(VVarType::PORT);
            dpi_trigger->direction(VDirection::INPUT);

            nodep->addStmtsp(instrID);
            nodep->addStmtsp(dpi_trigger);
            nodep->addStmtsp(var_x_func);
        }
    }

    //ASTLOOP VISITOR FUNCTION:
    //The function is used to add the logic for the dpi trigger, that triggers the DPI function at
    //the smallest possible time intervals.
    void visit(AstLoop* nodep) override {
        if (nodep == m_loopp && m_current_module != nullptr) {
            AstParseRef* initialParseRefrhsp
                = new AstParseRef{nodep->fileline(), m_dpi_trigger->name()};
            AstParseRef* initialParseReflhsp
                = new AstParseRef{nodep->fileline(), m_dpi_trigger->name()};
            AstBegin* initialBeginp = new AstBegin{
                nodep->fileline(), "",
                new AstAssign{nodep->fileline(), initialParseReflhsp,
                              new AstLogNot{nodep->fileline(), initialParseRefrhsp}},
                false};
            initialBeginp->addStmtsp(
                new AstDelay{nodep->fileline(),
                             new AstConst{nodep->fileline(), AstConst::Unsized32{}, 1}, false});
            nodep->addContsp(initialBeginp);
        }
    }

    //ASTALWAYS VISITOR FUNCTION:
    //The function is used to add the task reference node to the always node and further specify
    //the always node.
    void visit(AstAlways* nodep) override {
        if (nodep == m_alwaysp && m_current_module != nullptr) {
            AstBegin* newBegin = nullptr;

            m_taskrefp = new AstTaskRef{nodep->fileline(), m_task_name, nullptr};

            newBegin = new AstBegin{nodep->fileline(), "",
                                    new AstStmtExpr{nodep->fileline(), m_taskrefp}, false};
            nodep->addStmtsp(newBegin);
        }
        iterateChildren(nodep);
    }

    void visit(AstVar* nodep) override {
        if (m_current_module != nullptr && nodep->name() == m_orig_varp->name()) {
            m_orig_varp_instMod = nodep;
        }
    }

    //ASTTASKREF VISITOR FUNCTION:
    //The function is used to further specify the task reference node called by the always node.
    void visit(AstTaskRef* nodep) override {
        if (nodep == m_taskrefp && m_current_module != nullptr) {
            AstConst* constp_id = nullptr;
            constp_id = new AstConst{
                nodep->fileline(), AstConst::Unsized32{},
                static_cast<uint32_t>(getMapEntryFaultCase(m_targetKey, m_targetIndex))};

            AstVarRef* added_varrefp
                = new AstVarRef{nodep->fileline(), m_orig_varp_instMod, VAccess::READ};

            nodep->addPinsp(new AstArg{nodep->fileline(), "", constp_id});
            nodep->addPinsp(new AstArg{nodep->fileline(), "", added_varrefp});
            nodep->addPinsp(new AstArg{nodep->fileline(), "",
                                       new AstParseRef{nodep->fileline(), m_tmp_varp->name()}});
            m_orig_varp_instMod = nullptr;
        }
    }

    //ASTFUNCREF VISITOR FUNCTION:
    //The function is used to further specify the function reference node called by the assignw
    //node
    void visit(AstFuncRef* nodep) override {
        if (nodep == m_funcrefp && m_current_module != nullptr) {
            AstConst* constp_id = nullptr;

            constp_id = new AstConst{
                nodep->fileline(), AstConst::Unsized32{},
                static_cast<uint32_t>(getMapEntryFaultCase(m_targetKey, m_targetIndex))};

            AstVarRef* added_triggerp
                = new AstVarRef{nodep->fileline(), m_dpi_trigger, VAccess::READ};

            AstVarRef* added_varrefp
                = new AstVarRef{nodep->fileline(), m_orig_varp_instMod, VAccess::READ};

            nodep->addPinsp(new AstArg{nodep->fileline(), "", constp_id});
            nodep->addPinsp(new AstArg{nodep->fileline(), "", added_triggerp});
            nodep->addPinsp(new AstArg{nodep->fileline(), "", added_varrefp});
            m_orig_varp_instMod = nullptr;
            m_funcrefp = nullptr;
        }
    }

    //ASTASSIGNW VISITOR FUNCTION:
    //Sets the m_assignw flag to true if the current module is not null.
    //Necessary for the AstParseRef visitor function to determine if the current node is part of an
    //assignment.
    void visit(AstAssignW* nodep) override {
        instrAssigns(nodep);
    }
    void visit (AstAssign* nodep) override {
        instrAssigns(nodep);
    }
    void visit(AstAssignDly* nodep) override {
        instrAssigns(nodep);
    }
    void visit(AstAssignForce* nodep) override {
        instrAssigns(nodep);
    }

    //ASTPARSE REF VISITOR FUNCTION:
    //The function is used to change the parseref nodes to link to the instrumented variable
    //instead of the original variable. Depending on the direction of the original variable,
    //different actions are performed:
    //    - If the original variable is not an output variable and the assignment is true, the
    //parseref node is changed to link to the instrumented variable. This ensures that the
    //instrumented variable is used in the assignment.
    //    - If the original variable is an input variable, every parseref node is changed to link
    //    to
    //the instrumented variable. This ensures that the instrumented variable is used as the new
    //input.
    void visit(AstParseRef* nodep) override {
        if (m_current_module != nullptr && m_orig_varp != nullptr && m_orig_varp->direction() != VDirection::OUTPUT) {
            if (nodep->name() == m_orig_varp->name() && !m_assignNode) {
                nodep->name(m_tmp_varp->name());
            }
        }
    }

    //-----------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit InstrumentFunc(AstNetlist* nodep) { iterate(nodep); }
    ~InstrumentFunc() override = default;
};

//##################################################################################
// Instrumentation class functions

// Function to find instrumentation targets and additional information for the instrumentation
// process
void V3Instrument::findTargets(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { InstrumentTargetFndr{nodep}; }
    V3Global::dumpCheckGlobalTree("instrumentationFinder", 0, dumpTreeEitherLevel() >= 3);
}

// Function for the actual instrumentation process
void V3Instrument::instrument(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { InstrumentFunc{nodep}; }
    V3Global::dumpCheckGlobalTree("instrumentationFunction", 0, dumpTreeEitherLevel() >= 3);
}
