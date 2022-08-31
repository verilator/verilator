// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Replicate modules for parameterization
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
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

#include "V3Param.h"

#include "V3Ast.h"
#include "V3Case.h"
#include "V3Const.h"
#include "V3Global.h"
#include "V3Hasher.h"
#include "V3Os.h"
#include "V3Parse.h"
#include "V3Unroll.h"
#include "V3Width.h"

#include <cctype>
#include <deque>
#include <map>
#include <memory>
#include <vector>

//######################################################################
// Hierarchical block and parameter db (modules without parameter is also handled)

class ParameterizedHierBlocks final {
    using HierBlockOptsByOrigName = std::multimap<std::string, const V3HierarchicalBlockOption*>;
    using HierMapIt = HierBlockOptsByOrigName::const_iterator;
    using HierBlockModMap = std::map<const std::string, AstNodeModule*>;
    using ParamConstMap = std::map<const std::string, std::unique_ptr<AstConst>>;
    using GParamsMap = std::map<const std::string, AstVar*>;  // key:parameter name value:parameter

    // MEMBERS
    // key:Original module name, value:HiearchyBlockOption*
    // If a module is parameterized, the module is uniquiefied to overridden parameters.
    // This is why HierBlockOptsByOrigName is multimap.
    HierBlockOptsByOrigName m_hierBlockOptsByOrigName;
    // key:mangled module name, value:AstNodeModule*
    HierBlockModMap m_hierBlockMod;
    // Overridden parameters of the hierarchical block
    std::map<const V3HierarchicalBlockOption*, ParamConstMap> m_hierParams;
    std::map<const std::string, GParamsMap>
        m_modParams;  // Parameter variables of hierarchical blocks

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

public:
    ParameterizedHierBlocks(const V3HierBlockOptSet& hierOpts, AstNetlist* nodep) {
        for (const auto& hierOpt : hierOpts) {
            m_hierBlockOptsByOrigName.insert(
                std::make_pair(hierOpt.second.origName(), &hierOpt.second));
            const V3HierarchicalBlockOption::ParamStrMap& params = hierOpt.second.params();
            ParamConstMap& consts = m_hierParams[&hierOpt.second];
            for (V3HierarchicalBlockOption::ParamStrMap::const_iterator pIt = params.begin();
                 pIt != params.end(); ++pIt) {
                std::unique_ptr<AstConst> constp{AstConst::parseParamLiteral(
                    new FileLine(FileLine::EmptySecret()), pIt->second)};
                UASSERT(constp, pIt->second << " is not a valid parameter literal");
                const bool inserted = consts.emplace(pIt->first, std::move(constp)).second;
                UASSERT(inserted, pIt->first << " is already added");
            }
            // origName may be already registered, but it's fine.
            m_modParams.insert({hierOpt.second.origName(), {}});
        }
        for (AstNodeModule* modp = nodep->modulesp(); modp;
             modp = VN_AS(modp->nextp(), NodeModule)) {
            if (hierOpts.find(modp->prettyName()) != hierOpts.end()) {
                m_hierBlockMod.emplace(modp->name(), modp);
            }
            const auto defParamIt = m_modParams.find(modp->name());
            if (defParamIt != m_modParams.end()) {
                // modp is the original of parameterized hierarchical block
                for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                    if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                        if (varp->isGParam()) defParamIt->second.emplace(varp->name(), varp);
                    }
                }
            }
        }
    }
    AstNodeModule* findByParams(const string& origName, AstPin* firstPinp,
                                const AstNodeModule* modp) {
        if (m_hierBlockOptsByOrigName.find(origName) == m_hierBlockOptsByOrigName.end()) {
            return nullptr;
        }
        // This module is a hierarchical block. Need to replace it by the --lib-create wrapper.
        const std::pair<HierMapIt, HierMapIt> candidates
            = m_hierBlockOptsByOrigName.equal_range(origName);
        const auto paramsIt = m_modParams.find(origName);
        UASSERT_OBJ(paramsIt != m_modParams.end(), modp, origName << " must be registered");
        HierMapIt hierIt;
        for (hierIt = candidates.first; hierIt != candidates.second; ++hierIt) {
            bool found = true;
            size_t paramIdx = 0;
            const ParamConstMap& params = m_hierParams[hierIt->second];
            UASSERT(params.size() == hierIt->second->params().size(), "not match");
            for (AstPin* pinp = firstPinp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
                if (!pinp->exprp()) continue;
                UASSERT_OBJ(!pinp->modPTypep(), pinp,
                            "module with type parameter must not be a hierarchical block");
                if (const AstVar* const modvarp = pinp->modVarp()) {
                    AstConst* const constp = VN_AS(pinp->exprp(), Const);
                    UASSERT_OBJ(constp, pinp,
                                "parameter for a hierarchical block must have been constified");
                    const auto paramIt = paramsIt->second.find(modvarp->name());
                    UASSERT_OBJ(paramIt != paramsIt->second.end(), modvarp, "must be registered");
                    AstConst* const defValuep = VN_CAST(paramIt->second->valuep(), Const);
                    if (defValuep && areSame(constp, defValuep)) {
                        UINFO(5, "Setting default value of " << constp << " to " << modvarp
                                                             << std::endl);
                        continue;  // Skip this parameter because setting the same value
                    }
                    const auto pIt = vlstd::as_const(params).find(modvarp->name());
                    UINFO(5, "Comparing " << modvarp->name() << " " << constp << std::endl);
                    if (pIt == params.end() || paramIdx >= params.size()
                        || !areSame(constp, pIt->second.get())) {
                        found = false;
                        break;
                    }
                    UINFO(5, "Matched " << modvarp->name() << " " << constp << " and "
                                        << pIt->second.get() << std::endl);
                    ++paramIdx;
                }
            }
            if (found && paramIdx == hierIt->second->params().size()) break;
        }
        UASSERT_OBJ(hierIt != candidates.second, firstPinp, "No --lib-create wrapper found");
        // parameter settings will be removed in the bottom of caller visitCell().
        const HierBlockModMap::const_iterator modIt
            = m_hierBlockMod.find(hierIt->second->mangledName());
        UASSERT_OBJ(modIt != m_hierBlockMod.end(), firstPinp,
                    hierIt->second->mangledName() << " is not found");

        const auto it = vlstd::as_const(m_hierBlockMod).find(hierIt->second->mangledName());
        if (it == m_hierBlockMod.end()) return nullptr;
        return it->second;
    }
    static bool areSame(AstConst* pinValuep, AstConst* hierOptParamp) {
        if (pinValuep->isString()) {
            return pinValuep->num().toString() == hierOptParamp->num().toString();
        }

        if (hierOptParamp->isDouble()) {
            double var;
            if (pinValuep->isDouble()) {
                var = pinValuep->num().toDouble();
            } else {  // Cast from integer to real
                V3Number varNum{pinValuep, 0.0};
                varNum.opIToRD(pinValuep->num());
                var = varNum.toDouble();
            }
            return v3EpsilonEqual(var, hierOptParamp->num().toDouble());
        } else {  // Now integer type is assumed
            // Bitwidth of hierOptParamp is accurate because V3Width already caluclated in the
            // previous run. Bitwidth of pinValuep is before width analysis, so pinValuep is casted
            // to hierOptParamp width.
            V3Number varNum{pinValuep, hierOptParamp->num().width()};
            if (pinValuep->isDouble()) {  // Need to cast to int
                // Parameter is actually an integral type, but passed value is floating point.
                // Conversion from real to integer uses rounding in V3Width.cpp
                varNum.opRToIRoundS(pinValuep->num());
            } else if (pinValuep->isSigned()) {
                varNum.opExtendS(pinValuep->num(), pinValuep->num().width());
            } else {
                varNum.opAssign(pinValuep->num());
            }
            V3Number isEq(pinValuep, 1);
            isEq.opEq(varNum, hierOptParamp->num());
            return isEq.isNeqZero();
        }
    }
};

//######################################################################
// Remove parameters from cells and build new modules

class ParamProcessor final {
    // NODE STATE - Local
    //   AstVar::user4()        // int    Global parameter number (for naming new module)
    //                          //        (0=not processed, 1=iterated, but no number,
    //                          //         65+ parameter numbered)
    // NODE STATE - Shared with ParamVisitor
    //   AstNodeModule::user5() // bool   True if processed
    //   AstGenFor::user5()     // bool   True if processed
    //   AstVar::user5()        // bool   True if constant propagated
    //   AstCell::user5p()      // string* Generate portion of hierarchical name
    const VNUser4InUse m_inuser4;
    const VNUser5InUse m_inuser5;
    // User1/2/3 used by constant function simulations

    // TYPES
    // Note may have duplicate entries
    using IfaceRefRefs = std::deque<std::pair<AstIfaceRefDType*, AstIfaceRefDType*>>;

    // STATE
    using CloneMap = std::unordered_map<const AstNode*, AstNode*>;
    struct ModInfo {
        AstNodeModule* const m_modp;  // Module with specified name
        CloneMap m_cloneMap;  // Map of old-varp -> new cloned varp
        explicit ModInfo(AstNodeModule* modp)
            : m_modp{modp} {}
    };
    std::map<const std::string, ModInfo> m_modNameMap;  // Hash of created module flavors by name

    std::map<const std::string, std::string>
        m_longMap;  // Hash of very long names to unique identity number
    int m_longId = 0;

    // All module names that are loaded from source code
    // Generated modules by this visitor is not included
    V3StringSet m_allModuleNames;

    using ValueMapValue = std::pair<int, std::string>;
    std::map<const V3Hash, ValueMapValue> m_valueMap;  // Hash of node hash to (param value, name)
    int m_nextValue = 1;  // Next value to use in m_valueMap

    const AstNodeModule* m_modp = nullptr;  // Current module being processed

    // Database to get lib-create wrapper that matches parameters in hierarchical Verilation
    ParameterizedHierBlocks m_hierBlocks;
    // Default parameter values key:parameter name, value:default value (can be nullptr)
    using DefaultValueMap = std::map<std::string, AstConst*>;
    // Default parameter values of hierarchical blocks
    std::map<AstNodeModule*, DefaultValueMap> m_defaultParameterValues;

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    static void makeSmallNames(AstNodeModule* modp) {
        std::vector<int> usedLetter;
        usedLetter.resize(256);
        // Pass 1, assign first letter to each gparam's name
        for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                if (varp->isGParam() || varp->isIfaceRef()) {
                    char ch = varp->name()[0];
                    ch = std::toupper(ch);
                    if (ch < 'A' || ch > 'Z') ch = 'Z';
                    varp->user4(usedLetter[static_cast<int>(ch)] * 256 + ch);
                    usedLetter[static_cast<int>(ch)]++;
                }
            } else if (AstParamTypeDType* const typep = VN_CAST(stmtp, ParamTypeDType)) {
                const char ch = 'T';
                typep->user4(usedLetter[static_cast<int>(ch)] * 256 + ch);
                usedLetter[static_cast<int>(ch)]++;
            }
        }
    }
    static string paramSmallName(AstNodeModule* modp, AstNode* varp) {
        if (varp->user4() <= 1) makeSmallNames(modp);
        int index = varp->user4() / 256;
        const char ch = varp->user4() & 255;
        string st = cvtToStr(ch);
        while (index) {
            st += cvtToStr(char((index % 25) + 'A'));
            index /= 26;
        }
        return st;
    }

    static string paramValueKey(const AstNode* nodep) {
        if (const AstRefDType* const refp = VN_CAST(nodep, RefDType)) { nodep = refp->skipRefp(); }
        string key = nodep->name();
        if (const AstIfaceRefDType* const ifrtp = VN_CAST(nodep, IfaceRefDType)) {
            if (ifrtp->cellp() && ifrtp->cellp()->modp()) {
                key = ifrtp->cellp()->modp()->name();
            } else if (ifrtp->ifacep()) {
                key = ifrtp->ifacep()->name();
            } else {
                nodep->v3fatalSrc("Can't parameterize interface without module name");
            }
        } else if (const AstNodeUOrStructDType* const dtypep
                   = VN_CAST(nodep, NodeUOrStructDType)) {
            key += " ";
            key += dtypep->verilogKwd();
            key += " {";
            for (const AstNode* memberp = dtypep->membersp(); memberp;
                 memberp = memberp->nextp()) {
                key += paramValueKey(memberp);
                key += ";";
            }
            key += "}";
        } else if (const AstMemberDType* const dtypep = VN_CAST(nodep, MemberDType)) {
            key += " ";
            key += paramValueKey(dtypep->subDTypep());
        } else if (const AstBasicDType* const dtypep = VN_CAST(nodep, BasicDType)) {
            if (dtypep->isRanged()) {
                key += "[" + cvtToStr(dtypep->left()) + ":" + cvtToStr(dtypep->right()) + "]";
            }
        }
        return key;
    }

    string paramValueNumber(AstNode* nodep) {
        // TODO: This parameter value number lookup via a constructed key string is not
        //       particularly robust for type parameters. We should really have a type
        //       equivalence predicate function.
        const string key = paramValueKey(nodep);
        V3Hash hash = V3Hasher::uncachedHash(nodep);
        // Force hash collisions -- for testing only
        if (VL_UNLIKELY(v3Global.opt.debugCollision())) hash = V3Hash();
        int num;
        const auto it = m_valueMap.find(hash);
        if (it != m_valueMap.end() && it->second.second == key) {
            num = it->second.first;
        } else {
            num = m_nextValue++;
            m_valueMap[hash] = std::make_pair(num, key);
        }
        return std::string{"z"} + cvtToStr(num);
    }
    string moduleCalcName(const AstNodeModule* srcModp, const string& longname) {
        string newname = longname;
        if (longname.length() > 30) {
            const auto iter = m_longMap.find(longname);
            if (iter != m_longMap.end()) {
                newname = iter->second;
            } else {
                newname = srcModp->name();
                // We use all upper case above, so lower here can't conflict
                newname += "__pi" + cvtToStr(++m_longId);
                m_longMap.emplace(longname, newname);
            }
        }
        UINFO(4, "Name: " << srcModp->name() << "->" << longname << "->" << newname << endl);
        return newname;
    }
    AstNodeDType* arraySubDTypep(AstNodeDType* nodep) {
        // If an unpacked array, return the subDTypep under it
        if (const AstUnpackArrayDType* const adtypep = VN_CAST(nodep, UnpackArrayDType)) {
            return adtypep->subDTypep();
        }
        // We have not resolved parameter of the child yet, so still
        // have BracketArrayDType's. We'll presume it'll end up as assignment
        // compatible (or V3Width will complain).
        if (const AstBracketArrayDType* const adtypep = VN_CAST(nodep, BracketArrayDType)) {
            return adtypep->subDTypep();
        }
        return nullptr;
    }
    void collectPins(CloneMap* clonemapp, AstNodeModule* modp) {
        // Grab all I/O so we can remap our pins later
        for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                if (varp->isIO() || varp->isGParam() || varp->isIfaceRef()) {
                    // Cloning saved a pointer to the new node for us, so just follow that link.
                    const AstVar* const oldvarp = varp->clonep();
                    // UINFO(8,"Clone list 0x"<<hex<<(uint32_t)oldvarp
                    // <<" -> 0x"<<(uint32_t)varp<<endl);
                    clonemapp->emplace(oldvarp, varp);
                }
            } else if (AstParamTypeDType* const ptp = VN_CAST(stmtp, ParamTypeDType)) {
                if (ptp->isGParam()) {
                    const AstParamTypeDType* const oldptp = ptp->clonep();
                    clonemapp->emplace(oldptp, ptp);
                }
            }
        }
    }
    void relinkPins(const CloneMap* clonemapp, AstPin* startpinp) {
        for (AstPin* pinp = startpinp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            if (pinp->modVarp()) {
                // Find it in the clone structure
                // UINFO(8,"Clone find 0x"<<hex<<(uint32_t)pinp->modVarp()<<endl);
                const auto cloneiter = clonemapp->find(pinp->modVarp());
                UASSERT_OBJ(cloneiter != clonemapp->end(), pinp,
                            "Couldn't find pin in clone list");
                pinp->modVarp(VN_AS(cloneiter->second, Var));
            } else if (pinp->modPTypep()) {
                const auto cloneiter = clonemapp->find(pinp->modPTypep());
                UASSERT_OBJ(cloneiter != clonemapp->end(), pinp,
                            "Couldn't find pin in clone list");
                pinp->modPTypep(VN_AS(cloneiter->second, ParamTypeDType));
            } else {
                pinp->v3fatalSrc("Not linked?");
            }
        }
    }
    void relinkPinsByName(AstPin* startpinp, AstNodeModule* modp) {
        std::map<const string, AstVar*> nameToPin;
        for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                if (varp->isIO() || varp->isGParam() || varp->isIfaceRef()) {
                    nameToPin.emplace(varp->name(), varp);
                }
            }
        }
        for (AstPin* pinp = startpinp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            if (const AstVar* const varp = pinp->modVarp()) {
                const auto varIt = vlstd::as_const(nameToPin).find(varp->name());
                UASSERT_OBJ(varIt != nameToPin.end(), varp,
                            "Not found in " << modp->prettyNameQ());
                pinp->modVarp(varIt->second);
            }
        }
    }
    // Check if parameter setting during instantiation is simple enough for hierarchical verilation
    void checkSupportedParam(AstNodeModule* modp, AstPin* pinp) const {
        // InitArray and AstParamTypeDType are not supported because that can not be set via -G
        // option.
        if (pinp->modVarp()) {
            bool supported = false;
            if (const AstConst* const constp = VN_CAST(pinp->exprp(), Const)) {
                supported = !constp->isOpaque();
            }
            if (!supported) {
                pinp->v3error(AstNode::prettyNameQ(modp->origName())
                              << " has hier_block metacomment, hierarchical verilation"
                              << " supports only integer/floating point/string parameters");
            }
        } else {
            pinp->v3error(AstNode::prettyNameQ(modp->origName())
                          << " has hier_block metacomment, but 'parameter type' is not supported");
        }
    }
    bool moduleExists(const string& modName) const {
        if (m_allModuleNames.find(modName) != m_allModuleNames.end()) return true;
        if (m_modNameMap.find(modName) != m_modNameMap.end()) return true;
        return false;
    }

    string parameterizedHierBlockName(AstNodeModule* modp, AstPin* paramPinsp) {
        // Create a unique name in the following steps
        //  - Make a long name that includes all parameters, that appear
        //    in the alphabetical order.
        //  - Hash the long name to get valid Verilog symbol
        UASSERT_OBJ(modp->hierBlock(), modp, "should be used for hierarchical block");

        std::map<string, AstConst*> pins;
        for (AstPin* pinp = paramPinsp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            checkSupportedParam(modp, pinp);
            if (const AstVar* const varp = pinp->modVarp()) {
                if (!pinp->exprp()) continue;
                if (varp->isGParam()) {
                    AstConst* const constp = VN_CAST(pinp->exprp(), Const);
                    pins.emplace(varp->name(), constp);
                }
            }
        }

        auto paramsIt = m_defaultParameterValues.find(modp);
        if (paramsIt == m_defaultParameterValues.end()) {  // Not cached yet, so check parameters
            // Using map with key=string so that we can scan it in deterministic order
            DefaultValueMap params;
            for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                if (const AstVar* const varp = VN_CAST(stmtp, Var)) {
                    if (varp->isGParam()) {
                        AstConst* const constp = VN_CAST(varp->valuep(), Const);
                        // constp can be nullptr if the parameter is not used to instantiate sub
                        // module. varp->valuep() is not contified yet in the case.
                        // nullptr means that the parameter is using some default value.
                        params.emplace(varp->name(), constp);
                    }
                }
            }
            paramsIt = m_defaultParameterValues.emplace(modp, std::move(params)).first;
        }
        if (paramsIt->second.empty()) return modp->name();  // modp has no parameter

        string longname = modp->name();
        for (auto&& defaultValue : paramsIt->second) {
            const auto pinIt = pins.find(defaultValue.first);
            const AstConst* const constp
                = pinIt == pins.end() ? defaultValue.second : pinIt->second;
            // This longname is not valid as verilog symbol, but ok, because it will be hashed
            longname += "_" + defaultValue.first + "=";
            // constp can be nullptr
            if (constp) longname += constp->num().ascii(false);
        }

        const auto iter = m_longMap.find(longname);
        if (iter != m_longMap.end()) return iter->second;  // Already calculated

        VHashSha256 hash;
        // Calculate hash using longname
        // The hash is used as the module suffix to find a module name that is unique in the design
        hash.insert(longname);
        while (true) {
            // Copy VHashSha256 just in case of hash collision
            VHashSha256 hashStrGen = hash;
            // Hex string must be a safe suffix for any symbol
            const string hashStr = hashStrGen.digestHex();
            for (string::size_type i = 1; i < hashStr.size(); ++i) {
                string newName = modp->name();
                // Don't use '__' not to be encoded when this module is loaded later by Verilator
                if (newName.at(newName.size() - 1) != '_') newName += '_';
                newName += hashStr.substr(0, i);
                if (!moduleExists(newName)) {
                    m_longMap.emplace(longname, newName);
                    return newName;
                }
            }
            // Hash collision. maybe just v3error is practically enough
            hash.insert(V3Os::trueRandom(64));
        }
    }
    void deepCloneModule(AstNodeModule* srcModp, AstNode* cellp, AstPin* paramsp,
                         const string& newname, const IfaceRefRefs& ifaceRefRefs) {
        // Deep clone of new module
        // Note all module internal variables will be re-linked to the new modules by clone
        // However links outside the module (like on the upper cells) will not.
        AstNodeModule* const newmodp = srcModp->cloneTree(false);
        newmodp->name(newname);
        newmodp->user5(false);  // We need to re-recurse this module once changed
        newmodp->recursive(false);
        newmodp->recursiveClone(false);
        // Only the first generation of clone holds this property
        newmodp->hierBlock(srcModp->hierBlock() && !srcModp->recursiveClone());
        // Recursion may need level cleanups
        if (newmodp->level() <= m_modp->level()) newmodp->level(m_modp->level() + 1);
        if ((newmodp->level() - srcModp->level()) >= (v3Global.opt.moduleRecursionDepth() - 2)) {
            cellp->v3error("Exceeded maximum --module-recursion-depth of "
                           << v3Global.opt.moduleRecursionDepth());
            return;
        }
        // Keep tree sorted by level. Note: Different parametrizations of the same recursive module
        // end up with the same level, which we will need to fix up at the end, as we do not know
        // up front how recursive modules are expanded, and a later expansion might re-use an
        // earlier expansion (see t_recursive_module_bug_2).
        AstNode* insertp = srcModp;
        while (VN_IS(insertp->nextp(), NodeModule)
               && VN_AS(insertp->nextp(), NodeModule)->level() <= newmodp->level()) {
            insertp = insertp->nextp();
        }
        insertp->addNextHere(newmodp);

        m_modNameMap.emplace(newmodp->name(), ModInfo(newmodp));
        const auto iter = m_modNameMap.find(newname);
        CloneMap* const clonemapp = &(iter->second.m_cloneMap);
        UINFO(4, "     De-parameterize to new: " << newmodp << endl);

        // Grab all I/O so we can remap our pins later
        // Note we allow multiple users of a parameterized model,
        // thus we need to stash this info.
        collectPins(clonemapp, newmodp);
        // Relink parameter vars to the new module
        relinkPins(clonemapp, paramsp);
        // Fix any interface references
        for (auto it = ifaceRefRefs.cbegin(); it != ifaceRefRefs.cend(); ++it) {
            const AstIfaceRefDType* const portIrefp = it->first;
            const AstIfaceRefDType* const pinIrefp = it->second;
            AstIfaceRefDType* const cloneIrefp = portIrefp->clonep();
            UINFO(8, "     IfaceOld " << portIrefp << endl);
            UINFO(8, "     IfaceTo  " << pinIrefp << endl);
            UASSERT_OBJ(cloneIrefp, portIrefp, "parameter clone didn't hit AstIfaceRefDType");
            UINFO(8, "     IfaceClo " << cloneIrefp << endl);
            cloneIrefp->ifacep(pinIrefp->ifaceViaCellp());
            UINFO(8, "     IfaceNew " << cloneIrefp << endl);
        }
        // Assign parameters to the constants specified
        // DOES clone() so must be finished with module clonep() before here
        for (AstPin* pinp = paramsp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            if (pinp->exprp()) {
                if (AstVar* const modvarp = pinp->modVarp()) {
                    AstNode* const newp = pinp->exprp();  // Const or InitArray
                    AstConst* const exprp = VN_CAST(newp, Const);
                    AstConst* const origp = VN_CAST(modvarp->valuep(), Const);
                    const bool overridden
                        = !(origp && ParameterizedHierBlocks::areSame(exprp, origp));
                    // Remove any existing parameter
                    if (modvarp->valuep()) modvarp->valuep()->unlinkFrBack()->deleteTree();
                    // Set this parameter to value requested by cell
                    UINFO(9, "       set param " << modvarp << " = " << newp << endl);
                    modvarp->valuep(newp->cloneTree(false));
                    modvarp->overriddenParam(overridden);
                } else if (AstParamTypeDType* const modptp = pinp->modPTypep()) {
                    AstNodeDType* const dtypep = VN_AS(pinp->exprp(), NodeDType);
                    UASSERT_OBJ(dtypep, pinp, "unlinked param dtype");
                    if (modptp->childDTypep()) modptp->childDTypep()->unlinkFrBack()->deleteTree();
                    // Set this parameter to value requested by cell
                    modptp->childDTypep(dtypep->cloneTree(false));
                    // Later V3LinkDot will convert the ParamDType to a Typedef
                    // Not done here as may be localparams, etc, that also need conversion
                }
            }
        }
    }
    const ModInfo* moduleFindOrClone(AstNodeModule* srcModp, AstNode* cellp, AstPin* paramsp,
                                     const string& newname, const IfaceRefRefs& ifaceRefRefs) {
        // Already made this flavor?
        auto it = m_modNameMap.find(newname);
        if (it != m_modNameMap.end()) {
            UINFO(4, "     De-parameterize to old: " << it->second.m_modp << endl);
        } else {
            deepCloneModule(srcModp, cellp, paramsp, newname, ifaceRefRefs);
            it = m_modNameMap.find(newname);
            UASSERT(it != m_modNameMap.end(), "should find just-made module");
        }
        const ModInfo* const modInfop = &(it->second);
        return modInfop;
    }

    void cellPinCleanup(AstNode* nodep, AstPin* pinp, AstNodeModule* srcModp, string& longnamer,
                        bool& any_overridesr) {
        if (!pinp->exprp()) return;  // No-connect
        if (AstVar* const modvarp = pinp->modVarp()) {
            if (!modvarp->isGParam()) {
                pinp->v3error("Attempted parameter setting of non-parameter: Param "
                              << pinp->prettyNameQ() << " of " << nodep->prettyNameQ());
            } else if (VN_IS(pinp->exprp(), InitArray) && arraySubDTypep(modvarp->subDTypep())) {
                // Array assigned to array
                AstNode* const exprp = pinp->exprp();
                longnamer += "_" + paramSmallName(srcModp, modvarp) + paramValueNumber(exprp);
                any_overridesr = true;
            } else {
                V3Const::constifyParamsEdit(pinp->exprp());
                AstConst* const exprp = VN_CAST(pinp->exprp(), Const);
                const AstConst* const origp = VN_CAST(modvarp->valuep(), Const);
                if (!exprp) {
                    if (debug()) pinp->dumpTree(cout, "-nodes: ");
                    pinp->v3error("Can't convert defparam value to constant: Param "
                                  << pinp->prettyNameQ() << " of " << nodep->prettyNameQ());
                    pinp->exprp()->replaceWith(new AstConst(
                        pinp->fileline(), AstConst::WidthedValue(), modvarp->width(), 0));
                } else if (origp && exprp->sameTree(origp)) {
                    // Setting parameter to its default value.  Just ignore it.
                    // This prevents making additional modules, and makes coverage more
                    // obvious as it won't show up under a unique module page name.
                } else if (exprp->num().isDouble() || exprp->num().isString()
                           || exprp->num().isFourState() || exprp->num().width() != 32) {
                    longnamer
                        += ("_" + paramSmallName(srcModp, modvarp) + paramValueNumber(exprp));
                    any_overridesr = true;
                } else {
                    longnamer
                        += ("_" + paramSmallName(srcModp, modvarp) + exprp->num().ascii(false));
                    any_overridesr = true;
                }
            }
        } else if (AstParamTypeDType* const modvarp = pinp->modPTypep()) {
            AstNodeDType* const exprp = VN_CAST(pinp->exprp(), NodeDType);
            const AstNodeDType* const origp = modvarp->subDTypep();
            if (!exprp) {
                pinp->v3error("Parameter type pin value isn't a type: Param "
                              << pinp->prettyNameQ() << " of " << nodep->prettyNameQ());
            } else if (!origp) {
                pinp->v3error("Parameter type variable isn't a type: Param "
                              << modvarp->prettyNameQ());
            } else {
                UINFO(9, "Parameter type assignment expr=" << exprp << " to " << origp << endl);
                if (exprp->sameTree(origp)) {
                    // Setting parameter to its default value.  Just ignore it.
                    // This prevents making additional modules, and makes coverage more
                    // obvious as it won't show up under a unique module page name.
                } else {
                    V3Const::constifyParamsEdit(exprp);
                    longnamer += "_" + paramSmallName(srcModp, modvarp) + paramValueNumber(exprp);
                    any_overridesr = true;
                }
            }
        } else {
            pinp->v3error("Parameter not found in sub-module: Param "
                          << pinp->prettyNameQ() << " of " << nodep->prettyNameQ());
        }
    }

    void cellInterfaceCleanup(AstPin* pinsp, AstNodeModule* srcModp, string& longnamer,
                              bool& any_overridesr, IfaceRefRefs& ifaceRefRefs) {
        for (AstPin* pinp = pinsp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            const AstVar* const modvarp = pinp->modVarp();
            if (modvarp->isIfaceRef()) {
                AstIfaceRefDType* portIrefp = VN_CAST(modvarp->subDTypep(), IfaceRefDType);
                if (!portIrefp && arraySubDTypep(modvarp->subDTypep())) {
                    portIrefp = VN_CAST(arraySubDTypep(modvarp->subDTypep()), IfaceRefDType);
                }
                AstIfaceRefDType* pinIrefp = nullptr;
                const AstNode* const exprp = pinp->exprp();
                const AstVar* const varp
                    = (exprp && VN_IS(exprp, VarRef)) ? VN_AS(exprp, VarRef)->varp() : nullptr;
                if (varp && varp->subDTypep() && VN_IS(varp->subDTypep(), IfaceRefDType)) {
                    pinIrefp = VN_AS(varp->subDTypep(), IfaceRefDType);
                } else if (varp && varp->subDTypep() && arraySubDTypep(varp->subDTypep())
                           && VN_CAST(arraySubDTypep(varp->subDTypep()), IfaceRefDType)) {
                    pinIrefp = VN_CAST(arraySubDTypep(varp->subDTypep()), IfaceRefDType);
                } else if (exprp && exprp->op1p() && VN_IS(exprp->op1p(), VarRef)
                           && VN_CAST(exprp->op1p(), VarRef)->varp()
                           && VN_CAST(exprp->op1p(), VarRef)->varp()->subDTypep()
                           && arraySubDTypep(VN_CAST(exprp->op1p(), VarRef)->varp()->subDTypep())
                           && VN_CAST(
                               arraySubDTypep(VN_CAST(exprp->op1p(), VarRef)->varp()->subDTypep()),
                               IfaceRefDType)) {
                    pinIrefp
                        = VN_AS(arraySubDTypep(VN_AS(exprp->op1p(), VarRef)->varp()->subDTypep()),
                                IfaceRefDType);
                }

                UINFO(9, "     portIfaceRef " << portIrefp << endl);

                if (!portIrefp) {
                    pinp->v3error("Interface port " << modvarp->prettyNameQ()
                                                    << " is not an interface " << modvarp);
                } else if (!pinIrefp) {
                    pinp->v3error("Interface port "
                                  << modvarp->prettyNameQ()
                                  << " is not connected to interface/modport pin expression");
                } else {
                    UINFO(9, "     pinIfaceRef " << pinIrefp << endl);
                    if (portIrefp->ifaceViaCellp() != pinIrefp->ifaceViaCellp()) {
                        UINFO(9, "     IfaceRefDType needs reconnect  " << pinIrefp << endl);
                        longnamer += ("_" + paramSmallName(srcModp, pinp->modVarp())
                                      + paramValueNumber(pinIrefp));
                        any_overridesr = true;
                        ifaceRefRefs.push_back(std::make_pair(portIrefp, pinIrefp));
                        if (portIrefp->ifacep() != pinIrefp->ifacep()
                            // Might be different only due to param cloning, so check names too
                            && portIrefp->ifaceName() != pinIrefp->ifaceName()) {
                            pinp->v3error("Port " << pinp->prettyNameQ() << " expects "
                                                  << AstNode::prettyNameQ(portIrefp->ifaceName())
                                                  << " interface but pin connects "
                                                  << AstNode::prettyNameQ(pinIrefp->ifaceName())
                                                  << " interface");
                        }
                    }
                }
            }
        }
    }

    bool nodeDeparamCommon(AstNode* nodep, AstNodeModule*& srcModpr, AstPin* paramsp,
                           AstPin* pinsp, bool any_overrides) {
        // Make sure constification worked
        // Must be a separate loop, as constant conversion may have changed some pointers.
        // if (debug()) nodep->dumpTree(cout, "-cel2: ");
        string longname = srcModpr->name() + "_";
        if (debug() > 8 && paramsp) paramsp->dumpTreeAndNext(cout, "-cellparams: ");

        if (srcModpr->hierBlock()) {
            longname = parameterizedHierBlockName(srcModpr, paramsp);
            any_overrides = longname != srcModpr->name();
        } else {
            for (AstPin* pinp = paramsp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
                cellPinCleanup(nodep, pinp, srcModpr, longname /*ref*/, any_overrides /*ref*/);
            }
        }
        IfaceRefRefs ifaceRefRefs;
        cellInterfaceCleanup(pinsp, srcModpr, longname /*ref*/, any_overrides /*ref*/,
                             ifaceRefRefs /*ref*/);

        if (!any_overrides) {
            UINFO(8, "Cell parameters all match original values, skipping expansion.\n");
        } else if (AstNodeModule* const paramedModp
                   = m_hierBlocks.findByParams(srcModpr->name(), paramsp, m_modp)) {
            paramedModp->dead(false);
            // We need to relink the pins to the new module
            relinkPinsByName(pinsp, paramedModp);
            srcModpr = paramedModp;
        } else {
            const string newname
                = srcModpr->hierBlock() ? longname : moduleCalcName(srcModpr, longname);
            const ModInfo* const modInfop
                = moduleFindOrClone(srcModpr, nodep, paramsp, newname, ifaceRefRefs);
            // We need to relink the pins to the new module
            relinkPinsByName(pinsp, modInfop->m_modp);
            UINFO(8, "     Done with " << modInfop->m_modp << endl);
            srcModpr = modInfop->m_modp;
        }

        // Delete the parameters from the cell; they're not relevant any longer.
        if (paramsp) paramsp->unlinkFrBackWithNext()->deleteTree();
        return any_overrides;
    }

    void cellDeparam(AstCell* nodep, AstNodeModule*& srcModpr) {
        // Must always clone __Vrcm (recursive modules)
        if (nodeDeparamCommon(nodep, srcModpr, nodep->paramsp(), nodep->pinsp(),
                              nodep->recursive())) {
            nodep->modp(srcModpr);
            nodep->modName(srcModpr->name());
        }
        nodep->recursive(false);
    }

    void classRefDeparam(AstClassOrPackageRef* nodep, AstNodeModule*& srcModpr) {
        if (nodeDeparamCommon(nodep, srcModpr, nodep->paramsp(), nullptr, false))
            nodep->classOrPackagep(srcModpr);
    }

    void classRefDeparam(AstClassRefDType* nodep, AstNodeModule*& srcModpr) {
        if (nodeDeparamCommon(nodep, srcModpr, nodep->paramsp(), nullptr, false))
            nodep->classp(VN_AS(srcModpr, Class));
    }

public:
    void nodeDeparam(AstNode* nodep, AstNodeModule*& srcModpr, AstNodeModule* modp,
                     const string& someInstanceName) {
        m_modp = modp;
        // Cell: Check for parameters in the instantiation.
        // We always run this, even if no parameters, as need to look for interfaces,
        // and remove any recursive references
        UINFO(4, "De-parameterize: " << nodep << endl);
        // Create new module name with _'s between the constants
        if (debug() >= 10) nodep->dumpTree(cout, "-cell: ");
        // Evaluate all module constants
        V3Const::constifyParamsEdit(nodep);
        srcModpr->someInstanceName(someInstanceName + "." + nodep->name());

        if (auto* cellp = VN_CAST(nodep, Cell)) {
            cellDeparam(cellp, srcModpr);
        } else if (auto* classRefp = VN_CAST(nodep, ClassRefDType)) {
            classRefDeparam(classRefp, srcModpr);
        } else if (auto* classRefp = VN_CAST(nodep, ClassOrPackageRef)) {
            classRefDeparam(classRefp, srcModpr);
        } else {
            nodep->v3fatalSrc("Expected module parametrization");
        }

        UINFO(8, "     Done with " << nodep << endl);
        // if (debug() >= 10)
        // v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("param-out.tree"));
    }

    // CONSTRUCTORS
    explicit ParamProcessor(AstNetlist* nodep)
        : m_hierBlocks{v3Global.opt.hierBlocks(), nodep} {
        for (AstNodeModule* modp = nodep->modulesp(); modp;
             modp = VN_AS(modp->nextp(), NodeModule)) {
            m_allModuleNames.insert(modp->name());
        }
    }
    ~ParamProcessor() = default;
    VL_UNCOPYABLE(ParamProcessor);
};

//######################################################################
// Process parameter visitor

class ParamVisitor final : public VNVisitor {
    // NODE STATE
    // AstNodeModule::user1 -> bool: already fixed level

    // STATE
    ParamProcessor m_processor;  // De-parameterize a cell, build modules
    UnrollStateful m_unroller;  // Loop unroller

    bool m_iterateModule = false;  // Iterating module body
    string m_generateHierName;  // Generate portion of hierarchy name
    string m_unlinkedTxt;  // Text for AstUnlinkedRef
    std::multimap<bool, AstNode*> m_cellps;  // Cells left to process (in current module)
    std::multimap<int, AstNodeModule*> m_workQueue;  // Modules left to process

    // Map from AstNodeModule to set of all AstNodeModules that instantiates it.
    std::unordered_map<AstNodeModule*, std::unordered_set<AstNodeModule*>> m_parentps;

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    void visitCells(AstNodeModule* nodep) {
        UASSERT_OBJ(!m_iterateModule, nodep, "Should not nest");
        std::multimap<int, AstNodeModule*> workQueue;
        workQueue.emplace(nodep->level(), nodep);
        m_generateHierName = "";
        m_iterateModule = true;

        // Visit all cells under module, recursively
        do {
            const auto itm = workQueue.cbegin();
            AstNodeModule* const modp = itm->second;
            workQueue.erase(itm);

            // Process once; note user5 will be cleared on specialization, so we will do the
            // specialized module if needed
            if (modp->user5SetOnce()) continue;

            // TODO: this really should be an assert, but classes and hier_blocks are special...
            if (modp->someInstanceName().empty()) modp->someInstanceName(modp->origName());

            // Iterate the body
            iterateChildren(modp);

            // Process interface cells, then non-interface cells, which may reference an interface
            // cell.
            while (!m_cellps.empty()) {
                const auto itm = m_cellps.cbegin();
                AstNode* const cellp = itm->second;
                m_cellps.erase(itm);

                AstNodeModule* srcModp = nullptr;
                if (const auto* modCellp = VN_CAST(cellp, Cell)) {
                    srcModp = modCellp->modp();
                } else if (const auto* classRefp = VN_CAST(cellp, ClassOrPackageRef)) {
                    srcModp = classRefp->classOrPackagep();
                } else if (const auto* classRefp = VN_CAST(cellp, ClassRefDType)) {
                    srcModp = classRefp->classp();
                } else {
                    cellp->v3fatalSrc("Expected module parametrization");
                }

                // Update path
                string someInstanceName(modp->someInstanceName());
                if (const string* const genHierNamep = cellp->user5u().to<string*>()) {
                    someInstanceName += *genHierNamep;
                    cellp->user5p(nullptr);
                    VL_DO_DANGLING(delete genHierNamep, genHierNamep);
                }

                // Apply parameter specialization
                m_processor.nodeDeparam(cellp, srcModp /* ref */, modp, someInstanceName);

                // Add the (now potentially specialized) child module to the work queue
                workQueue.emplace(srcModp->level(), srcModp);

                // Add to the hierarchy registry
                m_parentps[srcModp].insert(modp);
            }
            if (workQueue.empty()) std::swap(workQueue, m_workQueue);
        } while (!workQueue.empty());

        m_iterateModule = false;
    }

    // Fix up level of module, based on who instantiates it
    void fixLevel(AstNodeModule* modp) {
        if (modp->user1SetOnce()) return;  // Already fixed
        if (m_parentps[modp].empty()) return;  // Leave top levels alone
        int maxParentLevel = 0;
        for (AstNodeModule* parentp : m_parentps[modp]) {
            fixLevel(parentp);  // Ensure parent level is correct
            maxParentLevel = std::max(maxParentLevel, parentp->level());
        }
        if (modp->level() <= maxParentLevel) modp->level(maxParentLevel + 1);
    }

    // A generic visitor for cells and class refs
    void visitCellOrClassRef(AstNode* nodep, bool isIface) {
        // Must do ifaces first, so push to list and do in proper order
        string* const genHierNamep = new std::string{m_generateHierName};
        nodep->user5p(genHierNamep);
        // Visit parameters in the instantiation.
        iterateChildren(nodep);
        m_cellps.emplace(!isIface, nodep);
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep) override {
        if (nodep->recursiveClone()) nodep->dead(true);  // Fake, made for recursive elimination
        if (nodep->dead()) return;  // Marked by LinkDot (and above)

        if (m_iterateModule) {  // Iterating body
            UINFO(4, " MOD-under-MOD.  " << nodep << endl);
            m_workQueue.emplace(nodep->level(), nodep);  // Delay until current module is done
            return;
        }

        // Start traversal at root-like things
        if (nodep->level() <= 2  // Haven't added top yet, so level 2 is the top
            || VN_IS(nodep, Class)  // Nor moved classes
            || VN_IS(nodep, Package)) {  // Likewise haven't done wrapTopPackages yet
            visitCells(nodep);
        }
    }

    virtual void visit(AstCell* nodep) override {
        visitCellOrClassRef(nodep, VN_IS(nodep->modp(), Iface));
    }
    virtual void visit(AstClassRefDType* nodep) override { visitCellOrClassRef(nodep, false); }
    virtual void visit(AstClassOrPackageRef* nodep) override { visitCellOrClassRef(nodep, false); }

    // Make sure all parameters are constantified
    virtual void visit(AstVar* nodep) override {
        if (nodep->user5SetOnce()) return;  // Process once
        iterateChildren(nodep);
        if (nodep->isParam()) {
            if (!nodep->valuep()) {
                nodep->v3error("Parameter without initial value is never given value"
                               << " (IEEE 1800-2017 6.20.1): " << nodep->prettyNameQ());
            } else {
                V3Const::constifyParamsEdit(nodep);  // The variable, not just the var->init()
            }
        }
    }
    // Make sure varrefs cause vars to constify before things above
    virtual void visit(AstVarRef* nodep) override {
        // Might jump across functions, so beware if ever add a m_funcp
        if (nodep->varp()) iterate(nodep->varp());
    }
    bool ifaceParamReplace(AstVarXRef* nodep, AstNode* candp) {
        for (; candp; candp = candp->nextp()) {
            if (nodep->name() == candp->name()) {
                if (AstVar* const varp = VN_CAST(candp, Var)) {
                    UINFO(9, "Found interface parameter: " << varp << endl);
                    nodep->varp(varp);
                    return true;
                } else if (const AstPin* const pinp = VN_CAST(candp, Pin)) {
                    UINFO(9, "Found interface parameter: " << pinp << endl);
                    UASSERT_OBJ(pinp->exprp(), pinp, "Interface parameter pin missing expression");
                    VL_DO_DANGLING(nodep->replaceWith(pinp->exprp()->cloneTree(false)), nodep);
                    return true;
                }
            }
        }
        return false;
    }
    virtual void visit(AstVarXRef* nodep) override {
        // Check to see if the scope is just an interface because interfaces are special
        const string dotted = nodep->dotted();
        if (!dotted.empty() && nodep->varp() && nodep->varp()->isParam()) {
            const AstNode* backp = nodep;
            while ((backp = backp->backp())) {
                if (VN_IS(backp, NodeModule)) {
                    UINFO(9, "Hit module boundary, done looking for interface" << endl);
                    break;
                }
                if (VN_IS(backp, Var) && VN_AS(backp, Var)->isIfaceRef()
                    && VN_AS(backp, Var)->childDTypep()
                    && (VN_CAST(VN_CAST(backp, Var)->childDTypep(), IfaceRefDType)
                        || (VN_CAST(VN_CAST(backp, Var)->childDTypep(), UnpackArrayDType)
                            && VN_CAST(VN_CAST(backp, Var)->childDTypep()->getChildDTypep(),
                                       IfaceRefDType)))) {
                    const AstIfaceRefDType* ifacerefp
                        = VN_CAST(VN_CAST(backp, Var)->childDTypep(), IfaceRefDType);
                    if (!ifacerefp) {
                        ifacerefp = VN_CAST(VN_CAST(backp, Var)->childDTypep()->getChildDTypep(),
                                            IfaceRefDType);
                    }
                    // Interfaces passed in on the port map have ifaces
                    if (const AstIface* const ifacep = ifacerefp->ifacep()) {
                        if (dotted == backp->name()) {
                            UINFO(9, "Iface matching scope:  " << ifacep << endl);
                            if (ifaceParamReplace(nodep, ifacep->stmtsp())) {  //
                                return;
                            }
                        }
                    }
                    // Interfaces declared in this module have cells
                    else if (const AstCell* const cellp = ifacerefp->cellp()) {
                        if (dotted == cellp->name()) {
                            UINFO(9, "Iface matching scope:  " << cellp << endl);
                            if (ifaceParamReplace(nodep, cellp->paramsp())) {  //
                                return;
                            }
                        }
                    }
                }
            }
        }
        nodep->varp(nullptr);  // Needs relink, as may remove pointed-to var
    }

    virtual void visit(AstUnlinkedRef* nodep) override {
        AstVarXRef* const varxrefp = VN_CAST(nodep->op1p(), VarXRef);
        AstNodeFTaskRef* const taskrefp = VN_CAST(nodep->op1p(), NodeFTaskRef);
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
    virtual void visit(AstCellArrayRef* nodep) override {
        V3Const::constifyParamsEdit(nodep->selp());
        if (const AstConst* const constp = VN_CAST(nodep->selp(), Const)) {
            const string index = AstNode::encodeNumber(constp->toSInt());
            const string replacestr = nodep->name() + "__BRA__??__KET__";
            const size_t pos = m_unlinkedTxt.find(replacestr);
            UASSERT_OBJ(pos != string::npos, nodep,
                        "Could not find array index in unlinked text: '"
                            << m_unlinkedTxt << "' for node: " << nodep);
            m_unlinkedTxt.replace(pos, replacestr.length(),
                                  nodep->name() + "__BRA__" + index + "__KET__");
        } else {
            nodep->v3error("Could not expand constant selection inside dotted reference: "
                           << nodep->selp()->prettyNameQ());
            return;
        }
    }

    // Generate Statements
    virtual void visit(AstGenIf* nodep) override {
        UINFO(9, "  GENIF " << nodep << endl);
        iterateAndNextNull(nodep->condp());
        // We suppress errors when widthing params since short-circuiting in
        // the conditional evaluation may mean these error can never occur. We
        // then make sure that short-circuiting is used by constifyParamsEdit.
        V3Width::widthGenerateParamsEdit(nodep);  // Param typed widthing will
                                                  // NOT recurse the body.
        V3Const::constifyGenerateParamsEdit(nodep->condp());  // condp may change
        if (const AstConst* const constp = VN_CAST(nodep->condp(), Const)) {
            if (AstNode* const keepp = (constp->isZero() ? nodep->elsesp() : nodep->ifsp())) {
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
    virtual void visit(AstBegin* nodep) override {
        if (nodep->genforp()) {
            AstGenFor* const forp = VN_AS(nodep->genforp(), GenFor);
            UASSERT_OBJ(forp, nodep, "Non-GENFOR under generate-for BEGIN");
            // We should have a GENFOR under here.  We will be replacing the begin,
            // so process here rather than at the generate to avoid iteration problems
            UINFO(9, "  BEGIN " << nodep << endl);
            UINFO(9, "  GENFOR " << forp << endl);
            V3Width::widthParamsEdit(forp);  // Param typed widthing will NOT recurse the body
            // Outer wrapper around generate used to hold genvar, and to ensure genvar
            // doesn't conflict in V3LinkDot resolution with other genvars
            // Now though we need to change BEGIN("zzz", GENFOR(...)) to
            // a BEGIN("zzz__BRA__{loop#}__KET__")
            const string beginName = nodep->name();
            // Leave the original Begin, as need a container for the (possible) GENVAR
            // Note V3Unroll will replace some AstVarRef's to the loop variable with constants
            // Don't remove any deleted nodes in m_unroller until whole process finishes,
            // (are held in m_unroller), as some AstXRefs may still point to old nodes.
            VL_DO_DANGLING(m_unroller.unrollGen(forp, beginName), forp);
            // Blocks were constructed under the special begin, move them up
            // Note forp is null, so grab statements again
            if (AstNode* const stmtsp = nodep->genforp()) {
                stmtsp->unlinkFrBackWithNext();
                nodep->addNextHere(stmtsp);
                // Note this clears nodep->genforp(), so begin is no longer special
            }
        } else {
            VL_RESTORER(m_generateHierName);
            m_generateHierName += "." + nodep->prettyName();
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstGenFor* nodep) override {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc("GENFOR should have been wrapped in BEGIN");
    }
    virtual void visit(AstGenCase* nodep) override {
        UINFO(9, "  GENCASE " << nodep << endl);
        AstNode* keepp = nullptr;
        iterateAndNextNull(nodep->exprp());
        V3Case::caseLint(nodep);
        V3Width::widthParamsEdit(nodep);  // Param typed widthing will NOT recurse the body,
                                          // don't trigger errors yet.
        V3Const::constifyParamsEdit(nodep->exprp());  // exprp may change
        const AstConst* const exprp = VN_AS(nodep->exprp(), Const);
        // Constify
        for (AstCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), CaseItem)) {
            for (AstNode* ep = itemp->condsp(); ep;) {
                AstNode* const nextp = ep->nextp();  // May edit list
                iterateAndNextNull(ep);
                VL_DO_DANGLING(V3Const::constifyParamsEdit(ep), ep);  // ep may change
                ep = nextp;
            }
        }
        // Item match
        for (AstCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), CaseItem)) {
            if (!itemp->isDefault()) {
                for (AstNode* ep = itemp->condsp(); ep; ep = ep->nextp()) {
                    if (const AstConst* const ccondp = VN_CAST(ep, Const)) {
                        V3Number match(nodep, 1);
                        match.opEq(ccondp->num(), exprp->num());
                        if (!keepp && match.isNeqZero()) keepp = itemp->bodysp();
                    } else {
                        itemp->v3error("Generate Case item does not evaluate to constant");
                    }
                }
            }
        }
        // Else default match
        for (AstCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), CaseItem)) {
            if (itemp->isDefault()) {
                if (!keepp) keepp = itemp->bodysp();
            }
        }
        // Replace
        if (keepp) {
            keepp->unlinkFrBackWithNext();
            nodep->replaceWith(keepp);
        } else {
            nodep->unlinkFrBack();
        }
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }

    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ParamVisitor(AstNetlist* netlistp)
        : m_processor{netlistp} {
        // Relies on modules already being in top-down-order
        iterate(netlistp);

        // Re-sort module list to be in topological order and fix-up incorrect levels. We need to
        // do this globally at the end due to the presence of recursive modules, which might be
        // expanded in orders that reuse earlier specializations later at a lower level.
        {
            // Gather modules
            std::vector<AstNodeModule*> modps;
            for (AstNodeModule *modp = netlistp->modulesp(), *nextp; modp; modp = nextp) {
                nextp = VN_AS(modp->nextp(), NodeModule);
                modp->unlinkFrBack();
                modps.push_back(modp);
            }

            // Fix-up levels
            {
                const VNUser1InUse user1InUse;
                for (AstNodeModule* const modp : modps) fixLevel(modp);
            }

            // Sort by level
            std::stable_sort(modps.begin(), modps.end(),
                             [](const AstNodeModule* ap, const AstNodeModule* bp) {
                                 return ap->level() < bp->level();
                             });

            // Re-insert modules
            for (AstNodeModule* const modp : modps) netlistp->addModulep(modp);
        }
    }
    virtual ~ParamVisitor() override = default;
    VL_UNCOPYABLE(ParamVisitor);
};

//######################################################################
// Param class functions

void V3Param::param(AstNetlist* rootp) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { ParamVisitor{rootp}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("param", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
