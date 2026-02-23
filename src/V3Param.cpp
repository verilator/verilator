//*************************************************************************
// DESCRIPTION: Verilator: Replicate modules for parameterization
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
// PARAM TRANSFORMATIONS:
//   Top down traversal:
//      For each cell:
//          If parameterized,
//              Determine all parameter widths, constant values.
//              (Interfaces also matter, as if a module is parameterized
//              this effectively changes the width behavior of all that
//              reference the iface.)
//
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

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Param.h"

#include "V3Case.h"
#include "V3Const.h"
#include "V3EmitV.h"
#include "V3Hasher.h"
#include "V3LinkDotIfaceCapture.h"
#include "V3MemberMap.h"
#include "V3Os.h"
#include "V3Parse.h"
#include "V3Simulate.h"
#include "V3Stats.h"
#include "V3Unroll.h"
#include "V3Width.h"

#include <cctype>
#include <cstdlib>
#include <deque>
#include <map>
#include <memory>
#include <unordered_map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Hierarchical block and parameter db (modules without parameters are also handled)

class ParameterizedHierBlocks final {
    using HierBlockOptsByOrigName = std::multimap<std::string, const V3HierarchicalBlockOption*>;
    using HierMapIt = HierBlockOptsByOrigName::const_iterator;
    using HierBlockModMap = std::map<const std::string, AstNodeModule*>;
    using ParamConstMap = std::map<const std::string, std::unique_ptr<AstConst>>;
    using GParamsMap = std::map<const std::string, AstVar*>;  // key:parameter name value:parameter

    // MEMBERS
    const bool m_hierSubRun;  // Is in sub-run for hierarchical verilation
    // key:Original module name, value:HiearchyBlockOption*
    // If a module is parameterized, the module is uniquified to overridden parameters.
    // This is why HierBlockOptsByOrigName is multimap.
    HierBlockOptsByOrigName m_hierBlockOptsByOrigName;
    // key:mangled module name, value:AstNodeModule*
    HierBlockModMap m_hierBlockMod;
    // Overridden parameters of the hierarchical block
    std::map<const V3HierarchicalBlockOption*, ParamConstMap> m_hierParams;
    // Parameter variables of hierarchical blocks
    std::map<const std::string, GParamsMap> m_modParams;

    // METHODS

public:
    ParameterizedHierBlocks(const V3HierBlockOptSet& hierOpts, AstNetlist* nodep)
        : m_hierSubRun{(!v3Global.opt.hierBlocks().empty() || v3Global.opt.hierChild())
                       // Exclude consolidation
                       && !v3Global.opt.hierParamFile().empty()} {
        for (const auto& hierOpt : hierOpts) {
            m_hierBlockOptsByOrigName.emplace(hierOpt.second.origName(), &hierOpt.second);
            const V3HierarchicalBlockOption::ParamStrMap& params = hierOpt.second.params();
            ParamConstMap& consts = m_hierParams[&hierOpt.second];
            for (V3HierarchicalBlockOption::ParamStrMap::const_iterator pIt = params.begin();
                 pIt != params.end(); ++pIt) {
                std::unique_ptr<AstConst> constp{AstConst::parseParamLiteral(
                    new FileLine{FileLine::builtInFilename()}, pIt->second)};
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
            // Recursive hierarchical module may change its name, so we have to match its origName.
            // Collect values from recursive cloned module as parameters in the top module could be
            // overridden.
            const string actualModName = modp->recursiveClone() ? modp->origName() : modp->name();
            const auto defParamIt = m_modParams.find(actualModName);
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
    bool hierSubRun() const { return m_hierSubRun; }
    bool isHierBlock(const string& origName) const {
        return m_hierBlockOptsByOrigName.find(origName) != m_hierBlockOptsByOrigName.end();
    }
    AstNodeModule* findByParams(const string& origName, AstPin* firstPinp,
                                const AstNodeModule* modp) {
        UASSERT(isHierBlock(origName), origName << " is not hierarchical block");
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
                if (const AstVar* const modvarp = pinp->modVarp()) {
                    AstConst* const constp = VN_AS(pinp->exprp(), Const);
                    UASSERT_OBJ(constp, pinp,
                                "parameter for a hierarchical block must have been constified");
                    const auto paramIt = paramsIt->second.find(modvarp->name());
                    UASSERT_OBJ(paramIt != paramsIt->second.end(), modvarp, "must be registered");
                    AstConst* const defValuep = VN_CAST(paramIt->second->valuep(), Const);
                    if (defValuep && areSame(constp, defValuep)) {
                        UINFO(5, "Setting default value of " << constp << " to " << modvarp);
                        continue;  // Skip this parameter because setting the same value
                    }
                    const auto pIt = vlstd::as_const(params).find(modvarp->name());
                    UINFO(5, "Comparing " << modvarp->name() << " " << constp);
                    if (pIt == params.end() || paramIdx >= params.size()
                        || !areSame(constp, pIt->second.get())) {
                        found = false;
                        break;
                    }
                    UINFO(5, "Matched " << modvarp->name() << " " << constp << " and "
                                        << pIt->second.get());
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
                V3Number varNum{pinValuep, V3Number::Double{}, 0.0};
                varNum.opIToRD(pinValuep->num());
                var = varNum.toDouble();
            }
            return V3Number::epsilonEqual(var, hierOptParamp->num().toDouble());
        } else {  // Now integer type is assumed
            // Bitwidth of hierOptParamp is accurate because V3Width already calculated in the
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
            V3Number isEq{pinValuep, 1};
            isEq.opEq(varNum, hierOptParamp->num());
            return isEq.isNeqZero();
        }
    }
};

//######################################################################
// Remove parameters from cells and build new modules

class ParamProcessor final {
    // NODE STATE - Local
    //   AstVar::user3()        // int    Global parameter number (for naming new module)
    //                          //        (0=not processed, 1=iterated, but no number,
    //                          //         65+ parameter numbered)
    // NODE STATE - Shared with ParamVisitor
    //   AstNodeModule::user3p()  // AstNodeModule* Unaltered copy of the parameterized module.
    //                               The module/class node may be modified according to parameter
    //                               values and an unchanged copy is needed to instantiate
    //                               modules/classes with different parameters.
    //   AstNodeModule::user2() // bool   True if processed
    //   AstGenFor::user2()     // bool   True if processed
    //   AstVar::user2()        // bool   True if constant propagated
    //   AstCell::user2p()      // string* Generate portion of hierarchical name
    //   AstNodeModule:user4p() // AstNodeModule* Parametrized copy with default parameters
    const VNUser2InUse m_inuser2;
    const VNUser3InUse m_inuser3;
    const VNUser4InUse m_inuser4;
    // User1 used by constant function simulations

    // TYPES
    // Note may have duplicate entries
    using IfaceRefRefs = std::deque<std::pair<AstIfaceRefDType*, AstIfaceRefDType*>>;

    // STATE
    using CloneMap = std::unordered_map<const AstNode*, AstNode*>;
    struct ModInfo final {
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
    VStringSet m_allModuleNames;

    CloneMap m_originalParams;  // Map between parameters of copied parameteized classes and their
                                // original nodes

    std::map<const V3Hash, int> m_valueMap;  // Hash of node hash to param value
    int m_nextValue = 1;  // Next value to use in m_valueMap

    const AstNodeModule* m_modp = nullptr;  // Current module being processed

    // Database to get lib-create wrapper that matches parameters in hierarchical Verilation
    ParameterizedHierBlocks m_hierBlocks;
    // Default parameter values key:parameter name, value:default value (can be nullptr)
    using DefaultValueMap = std::map<std::string, AstNode*>;
    // Default parameter values of hierarchical blocks
    std::map<AstNodeModule*, DefaultValueMap> m_defaultParameterValues;
    VNDeleter m_deleter;  // Used to delay deletion of nodes
    // Class default paramater dependencies
    std::vector<std::pair<AstParamTypeDType*, int>> m_classParams;
    std::unordered_map<AstParamTypeDType*, int> m_paramIndex;

    // member names cached for fast lookup
    VMemberMap m_memberMap;

    // METHODS

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
                    varp->user3(usedLetter[static_cast<int>(ch)] * 256 + ch);
                    usedLetter[static_cast<int>(ch)]++;
                }
            } else if (AstParamTypeDType* const typep = VN_CAST(stmtp, ParamTypeDType)) {
                const char ch = 'T';
                typep->user3(usedLetter[static_cast<int>(ch)] * 256 + ch);
                usedLetter[static_cast<int>(ch)]++;
            }
        }
    }
    static string paramSmallName(AstNodeModule* modp, AstNode* varp) {
        if (varp->user3() <= 1) makeSmallNames(modp);
        int index = varp->user3() / 256;
        const char ch = varp->user3() & 255;
        string st = cvtToStr(ch);
        while (index) {
            st += cvtToStr(char((index % 25) + 'A'));
            index /= 26;
        }
        return st;
    }

    static string paramValueString(const AstNode* nodep) {
        if (const AstRefDType* const refp = VN_CAST(nodep, RefDType)) {
            nodep = refp->skipRefToNonRefp();
        }
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
                key += paramValueString(memberp);
                key += ";";
            }
            key += "}";
        } else if (const AstMemberDType* const dtypep = VN_CAST(nodep, MemberDType)) {
            key += " ";
            key += paramValueString(dtypep->subDTypep());
        } else if (const AstBasicDType* const dtypep = VN_CAST(nodep, BasicDType)) {
            if (dtypep->isSigned()) key += " signed";
            if (dtypep->isRanged()) {
                key += "[" + cvtToStr(dtypep->left()) + ":" + cvtToStr(dtypep->right()) + "]";
            }
        } else if (const AstPackArrayDType* const dtypep = VN_CAST(nodep, PackArrayDType)) {
            key += "[";
            key += cvtToStr(dtypep->left());
            key += ":";
            key += cvtToStr(dtypep->right());
            key += "] ";
            key += paramValueString(dtypep->subDTypep());
        } else if (const AstInitArray* const initp = VN_CAST(nodep, InitArray)) {
            key += "{";
            for (auto it : initp->map()) {
                key += paramValueString(it.second->valuep());
                key += ",";
            }
            key += "}";
        } else if (const AstClassRefDType* const classRefp = VN_CAST(nodep, ClassRefDType)) {
            // For parameterized class types, use the original class name (without specialization
            // suffix) plus the actual type parameter values. This ensures equivalent class types
            // get the same string representation regardless of which AST node is used.
            if (classRefp->classp()) {
                const string& className = classRefp->classp()->name();
                const string& origName = classRefp->classp()->origName();
                const bool isSpecialized = (className != origName);
                UINFO(9, "paramValueString ClassRefDType: name="
                             << className << " origName=" << origName
                             << " isSpecialized=" << isSpecialized
                             << " hasParams=" << (classRefp->paramsp() ? "Y" : "N")
                             << " classHasGParam=" << classRefp->classp()->hasGParam() << endl);

                if (classRefp->paramsp()) {
                    // Has explicit type parameters - use origName + params
                    key = origName;
                    key += "#(";
                    for (AstPin* pinp = classRefp->paramsp(); pinp;
                         pinp = VN_AS(pinp->nextp(), Pin)) {
                        if (pinp != classRefp->paramsp()) key += ",";
                        if (pinp->exprp()) { key += paramValueString(pinp->exprp()); }
                    }
                    key += ")";
                } else if (isSpecialized) {
                    // Already specialized class (e.g., c1__Tz1_TBz1) - use full name
                    // This ensures different specializations are distinguished
                    key = className;
                } else {
                    // Unspecialized class with no params - use origName
                    key = origName;
                }
            } else {
                key += classRefp->prettyDTypeName(true);
            }
        } else if (const AstNodeDType* const dtypep = VN_CAST(nodep, NodeDType)) {
            key += dtypep->prettyDTypeName(true);
        }
        UASSERT_OBJ(!key.empty(), nodep, "Parameter yielded no value string");
        return key;
    }

    string paramValueNumber(AstNode* nodep) {
        // For type parameters (NodeDType), use only the string representation for hashing.
        // Using V3Hasher::uncachedHash includes AST node pointer which differs for equivalent
        // types represented by different AST nodes (e.g., parameterized class specializations).
        // For value parameters, we can still use the AST hash for better collision resistance.
        if (AstRefDType* const refp = VN_CAST(nodep, RefDType)) {
            nodep = refp->skipRefToNonRefp();
        }
        const string paramStr = paramValueString(nodep);
        V3Hash hash;
        if (VN_IS(nodep, NodeDType)) {
            // Type parameter: use only string-based hash for type equivalence
            hash = V3Hash{paramStr};
        } else {
            // Value parameter: use AST hash + string for better collision resistance
            hash = V3Hasher::uncachedHash(nodep) + paramStr;
        }
        // Force hash collisions -- for testing only
        // cppcheck-suppress unreadVariable
        if (VL_UNLIKELY(v3Global.opt.debugCollision())) hash = V3Hash{paramStr};
        int num;
        const auto pair = m_valueMap.emplace(hash, 0);
        if (pair.second) pair.first->second = m_nextValue++;
        num = pair.first->second;
        return "z"s + cvtToStr(num);
    }
    string moduleCalcName(const AstNodeModule* srcModp, const string& longname) {
        string newname = longname;
        if (longname.length() > 30) {
            const auto pair = m_longMap.emplace(longname, "");
            if (pair.second) {
                newname = srcModp->name();
                // We use all upper case above, so lower here can't conflict
                newname += "__pi" + cvtToStr(++m_longId);
                pair.first->second = newname;
            }
            newname = pair.first->second;
        }
        UINFO(4, "Name: " << srcModp->name() << "->" << longname << "->" << newname);
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
    bool isString(AstNodeDType* nodep) {
        if (AstBasicDType* const basicp = VN_CAST(nodep->skipRefToNonRefp(), BasicDType))
            return basicp->isString();
        return false;
    }
    void collectPins(CloneMap* clonemapp, AstNodeModule* modp, bool originalIsCopy) {
        // Grab all I/O so we can remap our pins later
        for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            const AstNode* originalParamp = nullptr;
            if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                if (varp->isIO() || varp->isGParam() || varp->isIfaceRef()) {
                    // Cloning saved a pointer to the new node for us, so just follow that link.
                    originalParamp = varp->clonep();
                }
            } else if (AstParamTypeDType* const ptp = VN_CAST(stmtp, ParamTypeDType)) {
                if (ptp->isGParam()) originalParamp = ptp->clonep();
            }
            if (originalIsCopy) originalParamp = m_originalParams[originalParamp];
            if (originalParamp) clonemapp->emplace(originalParamp, stmtp);
        }
    }
    void relinkPins(const CloneMap* clonemapp, AstPin* startpinp) {
        for (AstPin* pinp = startpinp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            if (pinp->modVarp()) {
                // Find it in the clone structure
                // UINFO(8,"Clone find 0x"<<hex<<(uint32_t)pinp->modVarp());
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
    // Check if parameter setting during instantiation is simple enough for hierarchical Verilation
    void checkSupportedParam(AstNodeModule* modp, AstPin* pinp) const {
        // InitArray is not supported because that can not be set via -G
        // option.
        if (pinp->modVarp()) {
            bool supported = false;
            if (const AstConst* const constp = VN_CAST(pinp->exprp(), Const)) {
                supported = !constp->isOpaque();
            }
            if (!supported) {
                pinp->v3error(
                    AstNode::prettyNameQ(modp->origName())
                    << " has hier_block metacomment, hierarchical Verilation"
                    << " supports only integer/floating point/string and type param parameters");
            }
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

        std::map<string, AstNode*> pins;

        AstPin* pinp = paramPinsp;
        while (pinp) {
            checkSupportedParam(modp, pinp);
            if (const AstVar* const varp = pinp->modVarp()) {
                if (!pinp->exprp()) continue;
                if (varp->isGParam()) pins.emplace(varp->name(), pinp->exprp());
            } else if (VN_IS(pinp->exprp(), BasicDType) || VN_IS(pinp->exprp(), NodeDType)) {
                pins.emplace(pinp->name(), pinp->exprp());
            }
            pinp = VN_AS(pinp->nextp(), Pin);
        }

        const auto pair = m_defaultParameterValues.emplace(
            std::piecewise_construct, std::forward_as_tuple(modp), std::forward_as_tuple());
        if (pair.second) {  // Not cached yet, so check parameters
            // Using map with key=string so that we can scan it in deterministic order
            DefaultValueMap params;
            for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                    if (varp->isGParam()) {
                        AstConst* const constp = VN_CAST(varp->valuep(), Const);
                        // constp can be nullptr if the parameter is not used to instantiate sub
                        // module. varp->valuep() is not constified yet in the case.
                        // nullptr means that the parameter is using some default value.
                        params.emplace(varp->name(), constp);
                    }
                } else if (AstParamTypeDType* const p = VN_CAST(stmtp, ParamTypeDType)) {
                    AstNode* const dtypep = static_cast<AstNode*>(p->skipRefp());
                    params.emplace(p->name(), dtypep);
                }
            }
            pair.first->second = std::move(params);
        }
        const auto paramsIt = pair.first;
        if (paramsIt->second.empty()) return modp->origName();  // modp has no parameter

        string longname = modp->origName();
        for (auto&& defaultValue : paramsIt->second) {
            const auto pinIt = pins.find(defaultValue.first);
            // If the pin does not have a value assigned, use the default one.
            const AstNode* const nodep = pinIt == pins.end() ? defaultValue.second : pinIt->second;
            // This longname is not valid as verilog symbol, but ok, because it will be hashed
            longname += "_" + defaultValue.first + "=";
            // constp can be nullptr

            if (const AstConst* const p = VN_CAST(nodep, Const)) {
                // Treat modules parameterized with the same values but with different type as the
                // same.
                longname += p->num().ascii(false);
            } else if (nodep) {
                std::stringstream type;
                V3EmitV::verilogForTree(nodep, type);
                longname += type.str();
            }
        }
        UINFO(9, "       module params longname: " << longname);

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
                string newName = modp->origName();
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
    void replaceRefsRecurse(AstNode* const nodep, const AstClass* const oldClassp,
                            AstClass* const newClassp) {
        // Self references linked in the first pass of V3LinkDot.cpp should point to the default
        // instance.
        if (AstClassRefDType* const classRefp = VN_CAST(nodep, ClassRefDType)) {
            if (classRefp->classp() == oldClassp) classRefp->classp(newClassp);
        } else if (AstClassOrPackageRef* const classRefp = VN_CAST(nodep, ClassOrPackageRef)) {
            if (classRefp->classOrPackageSkipp() == oldClassp)
                classRefp->classOrPackagep(newClassp);
        } else if (AstTypedef* const typedefp = VN_CAST(nodep, Typedef)) {
            // Update typedefs that refer to the old class to point to the new class
            if (typedefp->subDTypep()) {
                if (AstClassRefDType* const classRefp
                    = VN_CAST(typedefp->subDTypep(), ClassRefDType)) {
                    if (classRefp->classp() == oldClassp) { classRefp->classp(newClassp); }
                }
            }
        } else if (AstNodeFTaskRef* const ftaskRefp = VN_CAST(nodep, NodeFTaskRef)) {
            // Also update FuncRef/TaskRef packagep to point to new class
            // This fixes static method calls through typedefs in parameterized classes
            if (ftaskRefp->classOrPackagep() == oldClassp) ftaskRefp->classOrPackagep(newClassp);
            // Also update taskp if it points to a function in the old class
            if (AstNodeFTask* const oldTaskp = ftaskRefp->taskp()) {
                if (oldTaskp->classOrPackagep() == oldClassp) {
                    // Find the corresponding function in the new class
                    if (AstNodeFTask* const newTaskp = VN_CAST(
                            m_memberMap.findMember(newClassp, oldTaskp->name()), NodeFTask)) {
                        ftaskRefp->taskp(newTaskp);
                    }
                }
            }
        }

        if (nodep->op1p()) replaceRefsRecurse(nodep->op1p(), oldClassp, newClassp);
        if (nodep->op2p()) replaceRefsRecurse(nodep->op2p(), oldClassp, newClassp);
        if (nodep->op3p()) replaceRefsRecurse(nodep->op3p(), oldClassp, newClassp);
        if (nodep->op4p()) replaceRefsRecurse(nodep->op4p(), oldClassp, newClassp);
        if (nodep->nextp()) replaceRefsRecurse(nodep->nextp(), oldClassp, newClassp);
    }

    // Helper visitor to update VarXRefs to use variables from specialized interfaces.
    // When a module with interface ports is cloned and the port's interface is remapped
    // to a specialized version, VarXRefs that access members of the old interface need
    // to be updated to reference the corresponding members in the new interface.
    class VarXRefRelinkVisitor final : public VNVisitor {
        AstNodeModule* m_modp;  // The cloned module we're updating
        std::unordered_map<AstVar*, AstNodeModule*> m_varModuleMap;  // Cache var->module lookups

    public:
        explicit VarXRefRelinkVisitor(AstNodeModule* newModp)
            : m_modp{newModp} {
            iterate(newModp);
        }

    private:
        // Find which module a variable belongs to, using cache to avoid repeated backp() walks
        AstNodeModule* findVarModule(AstVar* varp) {
            const auto it = m_varModuleMap.find(varp);
            if (it != m_varModuleMap.end()) return it->second;
            AstNodeModule* varModp = nullptr;
            for (AstNode* np = varp; np; np = np->backp()) {
                if (AstNodeModule* const modp = VN_CAST(np, NodeModule)) {
                    varModp = modp;
                    break;
                }
            }
            m_varModuleMap[varp] = varModp;
            return varModp;
        }

        void visit(AstVarXRef* nodep) override {
            AstVar* const varp = nodep->varp();
            if (!varp) {
                iterateChildren(nodep);
                return;
            }

            // Get the dotted prefix (port name) from the VarXRef
            // dotted() format: "portname" or "portname.subpath" or empty
            const string& dotted = nodep->dotted();
            if (dotted.empty()) {
                iterateChildren(nodep);
                return;
            }

            const size_t dotPos = dotted.find('.');
            const string portName = (dotPos == string::npos) ? dotted : dotted.substr(0, dotPos);
            if (portName.empty()) {
                iterateChildren(nodep);
                return;
            }

            // Find the interface port variable in the cloned module
            AstVar* portVarp = nullptr;
            for (AstNode* stmtp = m_modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                if (AstVar* const varChkp = VN_CAST(stmtp, Var)) {
                    if (varChkp->name() == portName && varChkp->isIfaceRef()) {
                        portVarp = varChkp;
                        break;
                    }
                }
            }
            if (!portVarp) {
                iterateChildren(nodep);
                return;
            }

            // Get the interface module from the port's dtype
            AstIfaceRefDType* const irefp = VN_CAST(portVarp->subDTypep(), IfaceRefDType);
            if (!irefp) {
                iterateChildren(nodep);
                return;
            }

            AstNodeModule* const newIfacep = irefp->ifaceViaCellp();
            if (!newIfacep) {
                iterateChildren(nodep);
                return;
            }

            // Find which module the variable currently belongs to (cached)
            AstNodeModule* const varModp = findVarModule(varp);

            // If variable is in a different module than the port's interface, remap it
            if (varModp && varModp != newIfacep) {
                for (AstNode* stmtp = newIfacep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                    if (AstVar* const newVarp = VN_CAST(stmtp, Var)) {
                        if (newVarp->name() == varp->name()) {
                            UINFO(9, "VarXRef relink " << varp->name() << " in " << varModp->name()
                                                       << " -> " << newIfacep->name() << endl);
                            nodep->varp(newVarp);
                            break;
                        }
                    }
                }
            }
            iterateChildren(nodep);
        }
        void visit(AstNode* nodep) override { iterateChildren(nodep); }
    };

    // Return true on success, false on error
    bool deepCloneModule(AstNodeModule* srcModp, AstNode* ifErrorp, AstPin* paramsp,
                         const string& newname, const IfaceRefRefs& ifaceRefRefs) {
        // Deep clone of new module
        // Note all module internal variables will be re-linked to the new modules by clone
        // However links outside the module (like on the upper cells) will not.
        AstNodeModule* newModp;
        if (srcModp->user3p()) {
            newModp = VN_CAST(srcModp->user3p()->cloneTree(false), NodeModule);
        } else {
            newModp = srcModp->cloneTree(false);
        }

        // cloneTree(false) temporarily populates origNode->clonep() for every node under
        // srcModp.  The capture list still stores those orig AstRefDType* pointers, so walking
        // it lets us follow clonep() into newModp and scrub each clone with the saved
        // interface context before newModp is re-linked.  we have pointers to the same nodes saved
        // in the capture map, so we can use them to scrub the new module.

        if (V3LinkDotIfaceCapture::enabled()) {
            AstCell* const cloneCellp = VN_CAST(ifErrorp, Cell);
            UINFO(9, "iface capture clone: srcModp="
                         << srcModp->name() << " newModp=" << newModp->name()
                         << " cloneCellp=" << (cloneCellp ? cloneCellp->name() : "<null>")
                         << " ifaceRefRefs.size=" << ifaceRefRefs.size() << endl);
            V3LinkDotIfaceCapture::forEachOwned(
                srcModp, [&](const V3LinkDotIfaceCapture::CapturedEntry& entry) {
                    if (!entry.refp) return;

                    UINFO(9, "iface capture entry: refp="
                                 << entry.refp->name() << " cellPath='" << entry.cellPath << "'"
                                 << " typedefp="
                                 << (entry.typedefp ? entry.typedefp->name() : "<null>")
                                 << " paramTypep="
                                 << (entry.paramTypep ? entry.paramTypep->name() : "<null>")
                                 << " ownerModp="
                                 << (entry.ownerModp ? entry.ownerModp->name() : "<null>")
                                 << " typedefOwnerModName='" << entry.typedefOwnerModName << "'"
                                 << " ifacePortVarp="
                                 << (entry.ifacePortVarp ? entry.ifacePortVarp->name() : "<null>")
                                 << endl);

                    // When cloning the interface that owns the typedef (matched via
                    // typedefOwnerModName), disambiguate using the FULL cellPath.
                    // Walk cellPath-minus-last-component from entry.ownerModp and
                    // verify it resolves to m_modp (the parent module containing
                    // the cell being cloned).  This prevents the same entry from
                    // being processed by multiple clones of the same template.
                    if (cloneCellp && entry.ownerModp != srcModp
                        && entry.typedefOwnerModName == srcModp->name()) {
                        UASSERT_OBJ(!entry.cellPath.empty(), entry.refp,
                                    "cellPath is empty in entry matched via typedefOwnerModName");
                        // Split cellPath into parent portion and last component
                        const string& cp = entry.cellPath;
                        const size_t lastDot = cp.rfind('.');
                        const string parentPath
                            = (lastDot == string::npos) ? "" : cp.substr(0, lastDot);
                        const string lastComp
                            = (lastDot == string::npos) ? cp : cp.substr(lastDot + 1);
                        const size_t lastBraPos = lastComp.find("__BRA__");
                        const string lastCompBase = (lastBraPos == string::npos)
                                                        ? lastComp
                                                        : lastComp.substr(0, lastBraPos);
                        // Last component must match the cell name being cloned
                        if (lastComp != cloneCellp->name() && lastCompBase != cloneCellp->name()) {
                            UINFO(9, "iface capture skipping (lastComp mismatch): cellPath='"
                                         << cp << "' cloneCellPath='" << entry.cloneCellPath
                                         << "' lastComp='" << lastComp << "' != cloneCellp='"
                                         << cloneCellp->name() << "'" << endl);
                            return;
                        }
                        // If there's a parent portion, walk it from ownerModp
                        // and verify it resolves to m_modp
                        if (!parentPath.empty()) {
                            AstNodeModule* resolvedParentp = entry.ownerModp;
                            string remaining = parentPath;
                            while (!remaining.empty() && resolvedParentp) {
                                string comp;
                                const size_t dot = remaining.find('.');
                                if (dot == string::npos) {
                                    comp = remaining;
                                    remaining.clear();
                                } else {
                                    comp = remaining.substr(0, dot);
                                    remaining = remaining.substr(dot + 1);
                                }
                                const size_t braPos = comp.find("__BRA__");
                                const string compBase
                                    = (braPos == string::npos) ? comp : comp.substr(0, braPos);
                                AstNodeModule* nextModp = nullptr;
                                for (AstNode* sp = resolvedParentp->stmtsp(); sp;
                                     sp = sp->nextp()) {
                                    // Check cells (e.g. "tlb_io" cell)
                                    if (AstCell* const cp2 = VN_CAST(sp, Cell)) {
                                        if ((cp2->name() == comp || cp2->name() == compBase)
                                            && cp2->modp()) {
                                            nextModp = cp2->modp();
                                            break;
                                        }
                                    }
                                    // Check interface port variables (e.g. "cca_io" port)
                                    if (AstVar* const vp = VN_CAST(sp, Var)) {
                                        string varBaseName = vp->name();
                                        const size_t viftopPos = varBaseName.find("__Viftop");
                                        if (viftopPos != string::npos)
                                            varBaseName = varBaseName.substr(0, viftopPos);
                                        if ((varBaseName == comp || varBaseName == compBase)
                                            && vp->isIfaceRef()) {
                                            // Unwrap array types to find IfaceRefDType
                                            // (handles both scalar and array-of-interfaces)
                                            AstIfaceRefDType* irefp = nullptr;
                                            for (AstNodeDType* curDtp = vp->subDTypep(); curDtp;) {
                                                if (AstIfaceRefDType* const ir
                                                    = VN_CAST(curDtp, IfaceRefDType)) {
                                                    irefp = ir;
                                                    break;
                                                }
                                                if (AstBracketArrayDType* const bp
                                                    = VN_CAST(curDtp, BracketArrayDType)) {
                                                    curDtp = bp->subDTypep();
                                                    continue;
                                                }
                                                if (AstUnpackArrayDType* const up
                                                    = VN_CAST(curDtp, UnpackArrayDType)) {
                                                    curDtp = up->subDTypep();
                                                    continue;
                                                }
                                                break;
                                            }
                                            if (irefp && irefp->ifaceViaCellp()) {
                                                nextModp = irefp->ifaceViaCellp();
                                                break;
                                            }
                                        }
                                    }
                                }
                                resolvedParentp = nextModp;
                            }
                            // Path must resolve - null means broken cellPath
                            if (!resolvedParentp) {
                                // Diagnostic: dump all cells and vars in the
                                // module where the walk got stuck
                                AstNodeModule* stuckModp = entry.ownerModp;
                                // Re-walk to find where we got stuck
                                string rewalk = parentPath;
                                AstNodeModule* prevModp = entry.ownerModp;
                                while (!rewalk.empty() && prevModp) {
                                    string rc;
                                    const size_t rd = rewalk.find('.');
                                    if (rd == string::npos) {
                                        rc = rewalk;
                                        rewalk.clear();
                                    } else {
                                        rc = rewalk.substr(0, rd);
                                        rewalk = rewalk.substr(rd + 1);
                                    }
                                    const size_t rb = rc.find("__BRA__");
                                    const string rcBase
                                        = (rb == string::npos) ? rc : rc.substr(0, rb);
                                    AstNodeModule* nxt = nullptr;
                                    for (AstNode* sp = prevModp->stmtsp(); sp; sp = sp->nextp()) {
                                        if (AstCell* const c2 = VN_CAST(sp, Cell)) {
                                            if ((c2->name() == rc || c2->name() == rcBase)
                                                && c2->modp()) {
                                                nxt = c2->modp();
                                                break;
                                            }
                                        }
                                        if (AstVar* const v2 = VN_CAST(sp, Var)) {
                                            if ((v2->name() == rc || v2->name() == rcBase)
                                                && v2->isIfaceRef()) {
                                                AstIfaceRefDType* ir
                                                    = VN_CAST(v2->subDTypep(), IfaceRefDType);
                                                if (!ir) {
                                                    if (AstUnpackArrayDType* const a2 = VN_CAST(
                                                            v2->subDTypep(), UnpackArrayDType))
                                                        ir = VN_CAST(a2->subDTypep()->skipRefp(),
                                                                     IfaceRefDType);
                                                }
                                                if (ir && ir->ifaceViaCellp()) {
                                                    nxt = ir->ifaceViaCellp();
                                                    break;
                                                }
                                            }
                                        }
                                    }
                                    if (!nxt) {
                                        stuckModp = prevModp;
                                        break;
                                    }
                                    prevModp = nxt;
                                }
                                UINFO(0, "cellPath walk STUCK in module '" << stuckModp->name()
                                                                           << "' stmts:" << endl);
                                for (AstNode* sp = stuckModp->stmtsp(); sp; sp = sp->nextp()) {
                                    if (AstCell* const c2 = VN_CAST(sp, Cell)) {
                                        UINFO(0, "  CELL: '" << c2->name() << "' modp="
                                                             << (c2->modp() ? c2->modp()->name()
                                                                            : "<null>")
                                                             << endl);
                                    }
                                    if (AstVar* const v2 = VN_CAST(sp, Var)) {
                                        if (v2->isIfaceRef()) {
                                            UINFO(0, "  VAR(iface): '"
                                                         << v2->name() << "' subDType="
                                                         << v2->subDTypep()->typeName()
                                                         << " dtypeName="
                                                         << v2->subDTypep()->name() << endl);
                                        }
                                    }
                                }
                            }
                            UASSERT_OBJ(resolvedParentp, entry.refp,
                                        "cellPath parent walk failed: cellPath='"
                                            << cp << "' parentPath='" << parentPath
                                            << "' owner=" << entry.ownerModp->name()
                                            << " - path component not found");
                            if (resolvedParentp != m_modp) {
                                UINFO(9, "iface capture skipping (parent mismatch): cellPath='"
                                             << cp << "' cloneCellPath='" << entry.cloneCellPath
                                             << "' parentPath='" << parentPath << "' resolved to "
                                             << resolvedParentp->name()
                                             << " but m_modp=" << m_modp->name() << endl);
                                return;
                            }
                        }
                        UINFO(9, "iface capture matched: cellPath='"
                                     << cp << "' cloneCellPath='" << entry.cloneCellPath
                                     << "' parentPath='" << parentPath
                                     << "' -> m_modp=" << m_modp->name() << endl);
                    }

                    // Phase 2: register clone entry in the IfaceCapture ledger.
                    // Ledger-only - no target lookup or AST mutation here.
                    // Cell pointers in newModp are still stale (pointing to
                    // template interfaces).  Target resolution happens later
                    // in finalizeIfaceCapture (Phase 3) after all clones are
                    // wired up.  See V3LinkDotIfaceCapture.h ARCHITECTURE.
                    if (AstRefDType* const clonedRefp = entry.refp->clonep()) {
                        const string cloneCP = cloneCellp ? cloneCellp->name() : string{};
                        const V3LinkDotIfaceCapture::TemplateKey tkey{
                            entry.ownerModp ? entry.ownerModp->name() : "", entry.refp->name(),
                            entry.cellPath};
                        V3LinkDotIfaceCapture::propagateClone(tkey, clonedRefp, cloneCP);
                    } else if (entry.ownerModp != srcModp) {
                        // The REFDTYPE lives in a parent module (not inside the
                        // cloned class/iface), so clonep() is null.
                        // Check the ACTUAL owner (via backp() chain) - the stored
                        // ownerModp may be stale (pointing to the template even
                        // though the REFDTYPE now lives in a clone).
                        AstNodeModule* const actualOwnerp
                            = V3LinkDotIfaceCapture::findOwnerModule(entry.refp);
                        UINFO(9, "iface capture direct retarget check: refp="
                                     << entry.refp->name() << " ownerModp="
                                     << entry.ownerModp->name() << " actualOwnerp="
                                     << (actualOwnerp ? actualOwnerp->name() : "<null>")
                                     << " actualHasGParam="
                                     << (actualOwnerp ? actualOwnerp->hasGParam() : false)
                                     << " srcModp=" << srcModp->name() << " clonep="
                                     << (entry.refp->clonep() ? "set" : "null") << endl);
                        if (actualOwnerp && actualOwnerp->hasGParam()) {
                            // Owner will be cloned later; propagateClone handles it
                            UINFO(9, "iface capture direct retarget SKIP (actualOwner hasGParam): "
                                         << actualOwnerp->name() << endl);
                            return;
                        }
                        // Owner won't be cloned - directly retarget now.
                        if (entry.refp->typedefp()) {
                            const string& tdName = entry.refp->typedefp()->name();
                            for (AstNode* sp = newModp->stmtsp(); sp; sp = sp->nextp()) {
                                if (AstTypedef* const tdp = VN_CAST(sp, Typedef)) {
                                    if (tdp->name() == tdName) {
                                        UINFO(9, "iface capture direct retarget typedefp: "
                                                     << entry.refp->name() << " in "
                                                     << entry.ownerModp->name() << " -> "
                                                     << newModp->name() << " (+"
                                                     << entry.extraRefps.size() << " extras)"
                                                     << endl);
                                        entry.refp->typedefp(tdp);
                                        if (tdp->subDTypep()) {
                                            entry.refp->refDTypep(tdp->subDTypep());
                                            entry.refp->dtypep(tdp->subDTypep());
                                        }
                                        for (AstRefDType* const xrefp : entry.extraRefps) {
                                            xrefp->typedefp(tdp);
                                            if (tdp->subDTypep()) {
                                                xrefp->refDTypep(tdp->subDTypep());
                                                xrefp->dtypep(tdp->subDTypep());
                                            }
                                        }
                                        break;
                                    }
                                }
                            }
                        } else if (entry.paramTypep) {
                            // PARAMTYPEDTYPE-based reference (e.g. $bits(wrap1.data_t))
                            // Find the matching PARAMTYPEDTYPE in the clone by name.
                            const string& ptName = entry.paramTypep->name();
                            for (AstNode* sp = newModp->stmtsp(); sp; sp = sp->nextp()) {
                                if (AstParamTypeDType* const ptp = VN_CAST(sp, ParamTypeDType)) {
                                    if (ptp->name() == ptName) {
                                        UINFO(9, "iface capture direct retarget paramTypep: "
                                                     << entry.refp->name() << " in "
                                                     << (actualOwnerp ? actualOwnerp->name()
                                                                      : "<null>")
                                                     << " -> " << newModp->name() << " cellPath='"
                                                     << entry.cellPath << "'" << " (+"
                                                     << entry.extraRefps.size() << " extras)"
                                                     << endl);
                                        entry.refp->refDTypep(ptp);
                                        entry.refp->dtypep(ptp);
                                        for (AstRefDType* const xrefp : entry.extraRefps) {
                                            xrefp->refDTypep(ptp);
                                            xrefp->dtypep(ptp);
                                        }
                                        break;
                                    }
                                }
                            }
                        }
                    }
                });

            // Second pass: retarget clone entries whose typedef owner
            // matches the module being cloned.  Clone entries (non-empty
            // cloneCellPath) are skipped by forEachOwned above, but their
            // refp lives in a clone module that won't be cloned again.
            // They need direct retargeting NOW.
            //
            // IMPORTANT: use the same cellPath matching as the first pass
            // to make this targeted rather than broadcast.  Only retarget
            // entries whose cellPath's last component matches cloneCellp
            // and whose parent path resolves to m_modp.
            const string srcName = srcModp->name();
            V3LinkDotIfaceCapture::forEach([&](const V3LinkDotIfaceCapture::CapturedEntry& entry) {
                if (!entry.refp) return;
                if (entry.cloneCellPath.empty()) return;  // template entry, handled above
                if (entry.typedefOwnerModName != srcName) return;
                // Verify the actual owner won't be cloned later
                AstNodeModule* const actualOwnerp
                    = V3LinkDotIfaceCapture::findOwnerModule(entry.refp);
                if (!actualOwnerp || actualOwnerp->hasGParam()) return;
                // Match cellPath to the specific clone being created,
                // mirroring the first pass logic.
                if (cloneCellp && !entry.cellPath.empty()) {
                    const string& cp = entry.cellPath;
                    const size_t lastDot = cp.rfind('.');
                    const string lastComp
                        = (lastDot == string::npos) ? cp : cp.substr(lastDot + 1);
                    const size_t braPos = lastComp.find("__BRA__");
                    const string lastCompBase
                        = (braPos == string::npos) ? lastComp : lastComp.substr(0, braPos);
                    if (lastComp != cloneCellp->name() && lastCompBase != cloneCellp->name()) {
                        return;  // cellPath doesn't end with the cell being cloned
                    }
                    // If there's a parent portion, walk it from the
                    // entry's owner module and verify it resolves to
                    // m_modp (the parent module containing the cell).
                    if (lastDot != string::npos) {
                        const string parentPath = cp.substr(0, lastDot);
                        AstNodeModule* resolvedp = actualOwnerp;
                        string remaining = parentPath;
                        while (!remaining.empty() && resolvedp) {
                            string comp;
                            const size_t dot = remaining.find('.');
                            if (dot == string::npos) {
                                comp = remaining;
                                remaining.clear();
                            } else {
                                comp = remaining.substr(0, dot);
                                remaining = remaining.substr(dot + 1);
                            }
                            const size_t bp = comp.find("__BRA__");
                            const string compBase
                                = (bp == string::npos) ? comp : comp.substr(0, bp);
                            AstNodeModule* nextModp = nullptr;
                            for (AstNode* sp = resolvedp->stmtsp(); sp; sp = sp->nextp()) {
                                if (AstCell* const cp2 = VN_CAST(sp, Cell)) {
                                    if ((cp2->name() == comp || cp2->name() == compBase)
                                        && cp2->modp()) {
                                        nextModp = cp2->modp();
                                        break;
                                    }
                                }
                                if (AstVar* const vp = VN_CAST(sp, Var)) {
                                    string varBaseName = vp->name();
                                    const size_t vfp = varBaseName.find("__Viftop");
                                    if (vfp != string::npos)
                                        varBaseName = varBaseName.substr(0, vfp);
                                    if ((varBaseName == comp || varBaseName == compBase)
                                        && vp->isIfaceRef()) {
                                        AstIfaceRefDType* irefp = nullptr;
                                        for (AstNodeDType* curDtp = vp->subDTypep(); curDtp;) {
                                            if (AstIfaceRefDType* const ir
                                                = VN_CAST(curDtp, IfaceRefDType)) {
                                                irefp = ir;
                                                break;
                                            }
                                            if (AstBracketArrayDType* const bap
                                                = VN_CAST(curDtp, BracketArrayDType)) {
                                                curDtp = bap->subDTypep();
                                                continue;
                                            }
                                            if (AstUnpackArrayDType* const uap
                                                = VN_CAST(curDtp, UnpackArrayDType)) {
                                                curDtp = uap->subDTypep();
                                                continue;
                                            }
                                            break;
                                        }
                                        if (irefp && irefp->ifaceViaCellp()) {
                                            nextModp = irefp->ifaceViaCellp();
                                            break;
                                        }
                                    }
                                }
                            }
                            resolvedp = nextModp;
                        }
                        if (resolvedp != m_modp) {
                            UINFO(5, "iface capture clone-entry retarget SKIP (parent mismatch): "
                                         << entry.refp->name() << " cellPath=" << entry.cellPath
                                         << " cloneCP=" << entry.cloneCellPath << " resolved="
                                         << (resolvedp ? resolvedp->name() : "<null>")
                                         << " m_modp=" << m_modp->name() << endl);
                            return;
                        }
                    }
                }
                if (entry.refp->typedefp()) {
                    const string& tdName = entry.refp->typedefp()->name();
                    for (AstNode* sp = newModp->stmtsp(); sp; sp = sp->nextp()) {
                        if (AstTypedef* const tdp = VN_CAST(sp, Typedef)) {
                            if (tdp->name() == tdName) {
                                UINFO(9, "iface capture clone-entry retarget: "
                                             << entry.refp->name() << " cloneCellPath='"
                                             << entry.cloneCellPath
                                             << "' actualOwner=" << actualOwnerp->name() << " -> "
                                             << newModp->name() << endl);
                                entry.refp->typedefp(tdp);
                                if (tdp->subDTypep()) {
                                    entry.refp->refDTypep(tdp->subDTypep());
                                    entry.refp->dtypep(tdp->subDTypep());
                                }
                                break;
                            }
                        }
                    }
                }
            });
        }

        newModp->name(newname);
        newModp->user2(false);  // We need to re-recurse this module once changed
        newModp->recursive(false);
        newModp->recursiveClone(false);
        newModp->hasGParam(false);
        // Recursion may need level cleanups
        if (newModp->level() <= m_modp->level()) newModp->level(m_modp->level() + 1);
        if ((newModp->level() - srcModp->level()) >= (v3Global.opt.moduleRecursionDepth() - 2)) {
            ifErrorp->v3error("Exceeded maximum --module-recursion-depth of "
                              << v3Global.opt.moduleRecursionDepth());
            VL_DO_DANGLING(newModp->deleteTree(), newModp);
            return false;
        }

        if (AstClass* const newClassp = VN_CAST(newModp, Class)) {
            replaceRefsRecurse(newModp->stmtsp(), newClassp, VN_AS(srcModp, Class));
        }

        // Keep tree sorted by level. Note: Different parameterizations of the same recursive
        // module end up with the same level, which we will need to fix up at the end, as we do not
        // know up front how recursive modules are expanded, and a later expansion might re-use an
        // earlier expansion (see t_recursive_module_bug_2).
        AstNode* insertp = srcModp;
        while (VN_IS(insertp->nextp(), NodeModule)
               && VN_AS(insertp->nextp(), NodeModule)->level() <= newModp->level()) {
            insertp = insertp->nextp();
        }
        insertp->addNextHere(newModp);

        m_modNameMap.emplace(newModp->name(), ModInfo{newModp});
        const auto iter = m_modNameMap.find(newname);
        CloneMap* const clonemapp = &(iter->second.m_cloneMap);
        UINFO(4, "     De-parameterize to new: " << newModp);

        // Grab all I/O so we can remap our pins later
        // Note we allow multiple users of a parameterized model,
        // thus we need to stash this info.
        collectPins(clonemapp, newModp, srcModp->user3p());
        // Relink parameter vars to the new module
        // For interface ports (e.g., l3_if #(W, L0A_W) l3), the parameter pins may
        // reference variables from the enclosing module rather than from the interface
        // being cloned. In such cases, use relinkPinsByName to match by variable name.
        // Check if any parameter pins reference variables outside the cloned interface.
        // This is O(n) but acceptable since parameter pin lists are typically small (<10 pins).
        bool needRelinkByName = false;
        if (paramsp) {
            for (AstPin* pinp = paramsp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
                if (pinp->modVarp() && clonemapp->find(pinp->modVarp()) == clonemapp->end()) {
                    needRelinkByName = true;
                    break;
                }
            }
        }
        if (needRelinkByName) {
            relinkPinsByName(paramsp, newModp);
        } else {
            relinkPins(clonemapp, paramsp);
        }

        // Fix any interface references
        for (auto it = ifaceRefRefs.cbegin(); it != ifaceRefRefs.cend(); ++it) {
            const AstIfaceRefDType* const portIrefp = it->first;
            const AstIfaceRefDType* const pinIrefp = it->second;
            AstIfaceRefDType* const cloneIrefp = portIrefp->clonep();
            UINFO(8, "     IfaceOld " << portIrefp);
            UINFO(8, "     IfaceTo  " << pinIrefp);
            UASSERT_OBJ(cloneIrefp, portIrefp, "parameter clone didn't hit AstIfaceRefDType");
            UINFO(8, "     IfaceClo " << cloneIrefp);
            cloneIrefp->ifacep(pinIrefp->ifaceViaCellp());
            UINFO(8, "     IfaceNew " << cloneIrefp);
        }

        // Fix VarXRefs that reference variables in old interfaces.
        // Now that interface port dtypes have been updated above, we can use them
        // to find the correct interface for each VarXRef.
        if (!ifaceRefRefs.empty()) { VarXRefRelinkVisitor{newModp}; }

        // Fix cross-module REFDTYPE pointers in newModp.
        //
        // After cloneTree, some REFDTYPEs in newModp may have typedefp/refDTypep
        // pointing to a template module (dead) or a wrong sibling clone (live).
        // This happens because clonep() is last-writer-wins: the second clone of
        // an interface overwrites clonep() set by the first clone.
        //
        // Two-phase approach:
        //   Phase A (path-based): For REFDTYPEs tracked in the IfaceCapture
        //     ledger with a cellPath, use followCellPath to resolve to the
        //     correct interface clone.  This disambiguates e.g. "tgt_io.req_t"
        //     vs "mst_io.req_t" when both come from the same interface template.
        //   Phase B (reachable-set fallback): For ALL remaining REFDTYPEs in
        //     newModp whose targets point outside the reachable module set,
        //     find the correct target by origName matching.  This handles
        //     struct member types, nested dtypes, and other cross-module
        //     references not tracked by the ledger.
        UASSERT_OBJ(newModp, srcModp, "newModp null before hierarchy fixup");
        if (V3LinkDotIfaceCapture::enabled()) {
            // Phase A: path-based fixup using ledger entries
            std::set<AstRefDType*> ledgerFixed;  // track which REFDTYPEs we fix via ledger
            {
                const string cloneCP
                    = VN_CAST(ifErrorp, Cell) ? VN_AS(ifErrorp, Cell)->name() : "";
                const string srcName = srcModp->name();

                UINFO(9, "iface capture FIXUP-A: srcName=" << srcName << " cloneCP='" << cloneCP
                                                           << "' newModp=" << newModp->name()
                                                           << endl);

                V3LinkDotIfaceCapture::forEach(
                    [&](const V3LinkDotIfaceCapture::CapturedEntry& entry) {
                        if (!entry.refp) return;
                        if (entry.cloneCellPath != cloneCP) return;
                        if (!entry.ownerModp || entry.ownerModp->name() != srcName) return;
                        if (entry.cellPath.empty()) return;

                        AstRefDType* const refp = entry.refp;
                        AstNodeModule* const correctModp
                            = V3LinkDotIfaceCapture::followCellPath(newModp, entry.cellPath);
                        UINFO(9, "iface capture path fixup: "
                                     << newModp->name() << " refp=" << refp->name()
                                     << " cellPath='" << entry.cellPath << "' -> "
                                     << (correctModp ? correctModp->name() : "<null>") << endl);
                        if (!correctModp || correctModp->dead()) return;

                        bool fixed = false;
                        if (refp->typedefp()) {
                            const string& tdName = refp->typedefp()->name();
                            for (AstNode* sp = correctModp->stmtsp(); sp; sp = sp->nextp()) {
                                if (AstTypedef* const newTdp = VN_CAST(sp, Typedef)) {
                                    if (newTdp->name() == tdName) {
                                        UINFO(9, "  typedefp -> " << correctModp->name() << endl);
                                        refp->typedefp(newTdp);
                                        fixed = true;
                                        break;
                                    }
                                }
                            }
                        }
                        if (refp->refDTypep()) {
                            const string& rdName = refp->refDTypep()->name();
                            const VNType rdType = refp->refDTypep()->type();
                            for (AstNode* sp = correctModp->stmtsp(); sp; sp = sp->nextp()) {
                                if (AstNodeDType* const newDtp = VN_CAST(sp, NodeDType)) {
                                    if (newDtp->name() == rdName && newDtp->type() == rdType) {
                                        UINFO(9, "  refDTypep -> " << correctModp->name() << endl);
                                        refp->refDTypep(newDtp);
                                        fixed = true;
                                        break;
                                    }
                                }
                            }
                        }
                        if (fixed) ledgerFixed.insert(refp);
                    });
            }

            // Phase B: reachable-set fallback for REFDTYPEs not handled by ledger
            std::set<AstNodeModule*> reachable;
            reachable.insert(newModp);
            std::function<void(AstNodeModule*)> collectReachable;
            collectReachable = [&](AstNodeModule* modp) {
                for (AstNode* sp = modp->stmtsp(); sp; sp = sp->nextp()) {
                    if (AstCell* const cellp = VN_CAST(sp, Cell)) {
                        AstNodeModule* const cellModp = cellp->modp();
                        if (cellModp && reachable.insert(cellModp).second) {
                            collectReachable(cellModp);
                        }
                    }
                }
            };
            for (const auto& pair : ifaceRefRefs) {
                AstIface* const pinIfacep = pair.second->ifaceViaCellp();
                if (pinIfacep && reachable.insert(pinIfacep).second) {
                    collectReachable(pinIfacep);
                }
            }
            collectReachable(newModp);

            UINFO(9,
                  "iface capture hierarchy fixup: newModp=" << newModp->name() << " reachable={");
            for (AstNodeModule* const rModp : reachable) { UINFO(9, " " << rModp->name()); }
            UINFO(9, " }" << endl);

            // Walk only direct statement-level REFDTYPEs in newModp.
            // Do NOT use newModp->foreach which recurses into nested type
            // subtrees (struct members, union members, etc.) - rewriting
            // pointers inside those can create dangling dtypep links that
            // trigger V3Broken.
            for (AstNode* stmtp = newModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                AstRefDType* const refp = VN_CAST(stmtp, RefDType);
                if (!refp) continue;
                // Skip REFDTYPEs already fixed by path-based Phase A
                if (ledgerFixed.count(refp)) continue;

                // Fix typedefp pointing outside reachable set
                if (refp->typedefp()) {
                    AstNodeModule* const tdOwnerp
                        = V3LinkDotIfaceCapture::findOwnerModule(refp->typedefp());
                    if (tdOwnerp && tdOwnerp != newModp && !VN_IS(tdOwnerp, Package)
                        && reachable.find(tdOwnerp) == reachable.end()) {
                        const string& tdName = refp->typedefp()->name();
                        const string& wrongOrigName = tdOwnerp->origName().empty()
                                                          ? tdOwnerp->name()
                                                          : tdOwnerp->origName();
                        bool found = false;
                        for (AstNodeModule* const rModp : reachable) {
                            if (rModp == newModp) continue;
                            const string& rOrigName
                                = rModp->origName().empty() ? rModp->name() : rModp->origName();
                            if (rOrigName != wrongOrigName) continue;
                            for (AstNode* sp = rModp->stmtsp(); sp; sp = sp->nextp()) {
                                if (AstTypedef* const newTdp = VN_CAST(sp, Typedef)) {
                                    if (newTdp->name() == tdName) {
                                        UINFO(9, "iface capture reachable fixup: "
                                                     << newModp->name() << " refp=" << refp->name()
                                                     << " typedefp " << tdOwnerp->name() << " -> "
                                                     << rModp->name() << endl);
                                        refp->typedefp(newTdp);
                                        found = true;
                                        break;
                                    }
                                }
                            }
                            if (found) break;
                        }
                        if (!found) {
                            UINFO(4, "iface capture hierarchy fixup WARNING: "
                                         << newModp->name() << " refp=" << refp->name()
                                         << " typedefp owner=" << tdOwnerp->name()
                                         << (tdOwnerp->dead() ? " (dead)" : " (live)") << " name='"
                                         << tdName << "' not found in reachable set"
                                         << " (reachable.size=" << reachable.size() << ")"
                                         << endl);
                        }
                    }
                }
                // Fix refDTypep pointing outside reachable set
                if (refp->refDTypep()) {
                    AstNodeModule* const rdOwnerp
                        = V3LinkDotIfaceCapture::findOwnerModule(refp->refDTypep());
                    if (rdOwnerp && rdOwnerp != newModp && !VN_IS(rdOwnerp, Package)
                        && reachable.find(rdOwnerp) == reachable.end()) {
                        const string& rdName = refp->refDTypep()->name();
                        const VNType rdType = refp->refDTypep()->type();
                        const string& wrongOrigName = rdOwnerp->origName().empty()
                                                          ? rdOwnerp->name()
                                                          : rdOwnerp->origName();
                        bool found = false;
                        for (AstNodeModule* const rModp : reachable) {
                            if (rModp == newModp) continue;
                            const string& rOrigName
                                = rModp->origName().empty() ? rModp->name() : rModp->origName();
                            if (rOrigName != wrongOrigName) continue;
                            for (AstNode* sp = rModp->stmtsp(); sp; sp = sp->nextp()) {
                                if (AstNodeDType* const newDtp = VN_CAST(sp, NodeDType)) {
                                    if (newDtp->name() == rdName && newDtp->type() == rdType) {
                                        UINFO(9, "iface capture reachable fixup: "
                                                     << newModp->name() << " refp=" << refp->name()
                                                     << " refDTypep " << rdOwnerp->name() << " -> "
                                                     << rModp->name() << endl);
                                        refp->refDTypep(newDtp);
                                        found = true;
                                        break;
                                    }
                                }
                            }
                            if (found) break;
                        }
                        if (!found) {
                            UINFO(4, "iface capture hierarchy fixup WARNING: "
                                         << newModp->name() << " refp=" << refp->name()
                                         << " refDTypep owner=" << rdOwnerp->name()
                                         << (rdOwnerp->dead() ? " (dead)" : " (live)") << " name='"
                                         << rdName << "' not found in reachable set"
                                         << " (reachable.size=" << reachable.size() << ")"
                                         << endl);
                        }
                    }
                }
            }
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
                        = !(origp && exprp && ParameterizedHierBlocks::areSame(exprp, origp));
                    // Remove any existing parameter
                    if (modvarp->valuep()) modvarp->valuep()->unlinkFrBack()->deleteTree();
                    // Set this parameter to value requested by cell
                    UINFO(9, "       set param " << modvarp << " = " << newp);
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

        return true;
    }
    const ModInfo* moduleFindOrClone(AstNodeModule* srcModp, AstNode* ifErrorp, AstPin* paramsp,
                                     const string& newname, const IfaceRefRefs& ifaceRefRefs) {
        // Already made this flavor?
        auto it = m_modNameMap.find(newname);
        if (it != m_modNameMap.end()) {
            UINFO(4, "     De-parameterize to prev: " << it->second.m_modp);
        } else {
            if (!deepCloneModule(srcModp, ifErrorp, paramsp, newname, ifaceRefRefs)) {
                return nullptr;
            }
            it = m_modNameMap.find(newname);
            UASSERT(it != m_modNameMap.end(), "should find just-made module");
        }
        const ModInfo* const modInfop = &(it->second);
        return modInfop;
    }

    void convertToStringp(AstNode* nodep) {
        // Should be called on values of parameters of type string to convert them
        // to properly typed string constants.
        // Has no effect if the value is not a string constant.
        AstConst* const constp = VN_CAST(nodep, Const);
        // Check if it wasn't already converted
        if (constp && !constp->num().isString()) {
            constp->replaceWith(
                new AstConst{constp->fileline(), AstConst::String{}, constp->num().toString()});
            constp->deleteTree();
        }
    }

    // Helper to resolve DOT to RefDType for class type references.
    // If the class is parameterized and not yet specialized, specialize it first.
    // This handles cases like: iface #(param_class#(value)::typedef_name)
    void resolveDotToTypedef(AstNode* exprp) {
        AstDot* const dotp = VN_CAST(exprp, Dot);
        if (!dotp) return;
        AstClassOrPackageRef* const classRefp = VN_CAST(dotp->lhsp(), ClassOrPackageRef);
        if (!classRefp) return;
        AstParseRef* const parseRefp = VN_CAST(dotp->rhsp(), ParseRef);
        if (!parseRefp) return;

        const AstClass* lhsClassp = VN_CAST(classRefp->classOrPackageSkipp(), Class);
        if (classRefp->paramsp()) {
            // ClassOrPackageRef has parameters - may need to specialize the class
            AstClass* const srcClassp = VN_CAST(classRefp->classOrPackageNodep(), Class);
            if (srcClassp && srcClassp->hasGParam()) {
                // Specialize if the reference still points to the generic class
                if (lhsClassp == srcClassp || !lhsClassp) {
                    UINFO(9, "resolveDotToTypedef: specializing " << srcClassp->name() << endl);
                    classRefDeparam(classRefp, srcClassp);
                    lhsClassp = VN_CAST(classRefp->classOrPackageSkipp(), Class);
                }
            }
        }
        if (!lhsClassp) return;

        AstTypedef* const tdefp
            = VN_CAST(m_memberMap.findMember(lhsClassp, parseRefp->name()), Typedef);
        if (tdefp) {
            AstRefDType* const refp = new AstRefDType{dotp->fileline(), tdefp->name()};
            refp->typedefp(tdefp);
            dotp->replaceWith(refp);
            VL_DO_DANGLING(dotp->deleteTree(), dotp);
        }
    }

    void cellPinCleanup(AstNode* nodep, AstPin* pinp, AstNodeModule* srcModp, string& longnamer,
                        bool& any_overridesr) {
        if (!pinp->exprp()) return;  // No-connect
        if (AstVar* const modvarp = pinp->modVarp()) {
            if (!modvarp->isGParam()) {
                pinp->v3fatalSrc("Attempted parameter setting of non-parameter: Param "
                                 << pinp->prettyNameQ() << " of " << nodep->prettyNameQ());
            } else if (VN_IS(pinp->exprp(), InitArray) && arraySubDTypep(modvarp->subDTypep())) {
                // Array assigned to array
                AstNode* const exprp = pinp->exprp();
                longnamer += "_" + paramSmallName(srcModp, modvarp) + paramValueNumber(exprp);
                any_overridesr = true;
            } else if (VN_IS(pinp->exprp(), InitArray)) {
                // Array assigned to scalar parameter.  Treat the InitArray as a constant
                // integer array and include it in the module name.  Constantify nested
                // expressions before mangling the value number.
                V3Const::constifyParamsEdit(pinp->exprp());
                longnamer
                    += "_" + paramSmallName(srcModp, modvarp) + paramValueNumber(pinp->exprp());
                any_overridesr = true;
            } else {
                UINFO(9, "iface capture cellPinCleanup: before constify pin='"
                             << pinp->name() << "' mod='" << srcModp->name()
                             << "' exprType=" << pinp->exprp()->typeName() << " modvar='"
                             << modvarp->name() << "'" << " modval="
                             << (modvarp->valuep() ? modvarp->valuep()->typeName() : "null")
                             << (modvarp->valuep() && VN_IS(modvarp->valuep(), Const)
                                     ? string(" modvalNum=")
                                           + VN_AS(modvarp->valuep(), Const)->num().ascii(false)
                                     : string(""))
                             << " w=" << modvarp->width() << endl);
                V3Const::constifyParamsEdit(pinp->exprp());
                UINFO(9, "iface capture cellPinCleanup: after constify pin='"
                             << pinp->name() << "' exprType=" << pinp->exprp()->typeName()
                             << " isConst=" << VN_IS(pinp->exprp(), Const)
                             << (VN_IS(pinp->exprp(), Const)
                                     ? string(" val=")
                                           + VN_AS(pinp->exprp(), Const)->num().ascii(false)
                                     : string(""))
                             << " w=" << pinp->exprp()->width() << endl);
                // String constants are parsed as logic arrays and converted to strings in V3Const.
                // At this moment, some constants may have been already converted.
                // To correctly compare constants, both should be of the same type,
                // so they need to be converted.
                if (isString(modvarp->subDTypep())) {
                    convertToStringp(pinp->exprp());
                    convertToStringp(modvarp->valuep());
                }
                AstConst* const exprp = VN_CAST(pinp->exprp(), Const);
                AstConst* const origp = VN_CAST(modvarp->valuep(), Const);
                if (!exprp) {
                    // With DepGraph architecture, all expressions should be constants
                    // by the time V3Param runs. If not, it's an error.
                    UINFO(9, "iface capture cellPinCleanup: NOT CONST after constify pin='"
                                 << pinp->name() << "' mod='" << srcModp->name()
                                 << "' exprType=" << pinp->exprp()->typeName() << endl);
                    UINFOTREE(1, pinp, "", "errnode");
                    pinp->v3error("Can't convert defparam value to constant: Param "
                                  << pinp->prettyNameQ() << " of " << nodep->prettyNameQ());
                    AstNode* const pinExprp = pinp->exprp();
                    pinExprp->replaceWith(new AstConst{pinp->fileline(), AstConst::WidthedValue{},
                                                       modvarp->width(), 0});
                    VL_DO_DANGLING(pinExprp->deleteTree(), pinExprp);
                } else if (origp
                           && (exprp->sameTree(origp)
                               || (exprp->num().width() == origp->num().width()
                                   && ParameterizedHierBlocks::areSame(exprp, origp)))) {
                    // Setting parameter to its default value.  Just ignore it.
                    // This prevents making additional modules, and makes coverage more
                    // obvious as it won't show up under a unique module page name.
                    UINFO(9, "iface capture cellPinCleanup: SAME AS DEFAULT pin='"
                                 << pinp->name() << "' mod='" << srcModp->name()
                                 << "' val=" << exprp->num().ascii(false) << endl);
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
            // Handle DOT with ParseRef RHS (e.g., p_class#(8)::p_type)
            // by this point ClassOrPackageRef should be updated to point to the specialized class.
            resolveDotToTypedef(pinp->exprp());

            AstNodeDType* rawTypep = VN_CAST(pinp->exprp(), NodeDType);
            // widthParamsEdit is destructive: it evaluates range expressions,
            // sets didWidth=1, and removes Range nodes. When the REFDTYPE chain
            // reaches into a template interface (e.g., struct types derived from
            // parameterized interfaces), this mutates the template's BASICDTYPEs,
            // corrupting all subsequent clones. Only skip widthing when the
            // resolved type is a struct/union owned by a template interface.
            // Local structs with parameter-dependent widths still need widthing.
            bool skipWidthForTemplateStruct = false;
            {
                // Use non-asserting skip: before widthParamsEdit, type(expr)
                // constructs may contain unlinked REFDTYPEs (e.g. type(x-y))
                AstNodeDType* const resolvedp = rawTypep ? rawTypep->skipRefOrNullp() : nullptr;
                if (resolvedp && (VN_IS(resolvedp, StructDType) || VN_IS(resolvedp, UnionDType))) {
                    AstNodeModule* const ownerModp
                        = V3LinkDotIfaceCapture::findOwnerModule(resolvedp);
                    // Skip if owned by a template (hasGParam, not yet specialized)
                    if (ownerModp && ownerModp->hasGParam()
                        && ownerModp->name().find("__") == string::npos) {
                        skipWidthForTemplateStruct = true;
                    }
                }
                if (rawTypep && !skipWidthForTemplateStruct) V3Width::widthParamsEdit(rawTypep);
            }
            AstNodeDType* exprp = rawTypep ? rawTypep->skipRefToNonRefp() : nullptr;
            const AstNodeDType* origp = modvarp->skipRefToNonRefp();
            if (!exprp) {
                pinp->v3error("Parameter type pin value isn't a type: Param "
                              << pinp->prettyNameQ() << " of " << nodep->prettyNameQ());
            } else if (!origp) {
                pinp->v3error("Parameter type variable isn't a type: Param "
                              << modvarp->prettyNameQ());
            } else {
                UINFO(9, "Parameter type assignment expr=" << exprp << " to " << origp);
                if (!skipWidthForTemplateStruct) {
                    V3Const::constifyParamsEdit(pinp->exprp());  // Reconcile typedefs
                    // Constify may have caused pinp->exprp to change
                    rawTypep = VN_AS(pinp->exprp(), NodeDType);
                    exprp = rawTypep->skipRefToNonRefp();
                }
                if (!modvarp->fwdType().isNodeCompatible(exprp)) {
                    pinp->v3error("Parameter type expression type "
                                  << exprp->prettyDTypeNameQ()
                                  << " violates parameter's forwarding type '"
                                  << modvarp->fwdType().ascii() << "'");
                }
                if (exprp->similarDType(origp)) {
                    // Setting parameter to its default value.  Just ignore it.
                    // This prevents making additional modules, and makes coverage more
                    // obvious as it won't show up under a unique module page name.
                } else {
                    if (!skipWidthForTemplateStruct) {
                        VL_DO_DANGLING(V3Const::constifyParamsEdit(exprp), exprp);
                        rawTypep = VN_CAST(pinp->exprp(), NodeDType);
                        exprp = rawTypep ? rawTypep->skipRefToNonRefp() : nullptr;
                    }
                    longnamer += "_" + paramSmallName(srcModp, modvarp) + paramValueNumber(exprp);
                    any_overridesr = true;
                }
            }
        } else {
            pinp->v3fatalSrc("Parameter not found in sub-module: Param "
                             << pinp->prettyNameQ() << " of " << nodep->prettyNameQ());
        }
    }

    void cellInterfaceCleanup(AstPin* pinsp, AstNodeModule* srcModp, string& longnamer,
                              bool& any_overridesr, IfaceRefRefs& ifaceRefRefs) {
        for (AstPin* pinp = pinsp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            const AstVar* const modvarp = pinp->modVarp();
            if (modvarp && VN_IS(modvarp->subDTypep(), IfaceGenericDType)) continue;
            if (modvarp->isIfaceRef()) {
                AstIfaceRefDType* portIrefp = VN_CAST(modvarp->subDTypep(), IfaceRefDType);
                if (!portIrefp && arraySubDTypep(modvarp->subDTypep())) {
                    portIrefp = VN_CAST(arraySubDTypep(modvarp->subDTypep()), IfaceRefDType);
                }
                AstIfaceRefDType* pinIrefp = nullptr;
                const AstNode* const exprp = pinp->exprp();
                const AstVar* const varp = (exprp && VN_IS(exprp, NodeVarRef))
                                               ? VN_AS(exprp, NodeVarRef)->varp()
                                               : nullptr;
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
                } else if (VN_IS(exprp, CellArrayRef)) {
                    // Interface array element selection (e.g., l1(l2.l1[0]) for nested iface
                    // array) The CellArrayRef is not yet fully linked to an interface type. Skip
                    // interface cleanup for this pin - V3LinkDot will resolve this later. Just
                    // continue to the next pin without error.
                    UINFO(9, "Skipping interface cleanup for CellArrayRef pin: " << pinp << endl);
                    continue;
                }

                UINFO(9, "     portIfaceRef " << portIrefp);

                if (!portIrefp) {
                    pinp->v3error("Interface port " << modvarp->prettyNameQ()
                                                    << " is not an interface " << modvarp);
                } else if (!pinIrefp) {
                    pinp->v3error("Interface port "
                                  << modvarp->prettyNameQ()
                                  << " is not connected to interface/modport pin expression");
                } else {
                    UINFO(9, "     pinIfaceRef " << pinIrefp);
                    if (portIrefp->ifaceViaCellp() != pinIrefp->ifaceViaCellp()) {
                        UINFO(9, "     IfaceRefDType needs reconnect  " << pinIrefp);
                        longnamer += ("_" + paramSmallName(srcModp, pinp->modVarp())
                                      + paramValueNumber(pinIrefp));
                        any_overridesr = true;
                        ifaceRefRefs.emplace_back(portIrefp, pinIrefp);
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

    void storeOriginalParams(AstNodeModule* const classp) {
        for (AstNode* stmtp = classp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            AstNode* originalParamp = nullptr;
            if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                if (varp->isGParam()) originalParamp = varp->clonep();
            } else if (AstParamTypeDType* const ptp = VN_CAST(stmtp, ParamTypeDType)) {
                if (ptp->isGParam()) originalParamp = ptp->clonep();
            }
            if (originalParamp) m_originalParams[stmtp] = originalParamp;
        }
    }

    // Set interfaces types inside generic modules
    // to the corresponding values of implicit parameters
    void genericInterfaceVarSetup(const AstPin* const paramsp, const AstPin* const pinsp) {
        std::unordered_map<string, const AstPin*> paramspMap;
        for (const AstPin* pinp = paramsp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            if (VString::startsWith(pinp->name(), "__VGIfaceParam")) {
                paramspMap.insert({pinp->name().substr(std::strlen("__VGIfaceParam")), pinp});
            }
        }

        if (paramspMap.empty()) return;

        for (const AstNode* nodep = pinsp; nodep; nodep = nodep->nextp()) {
            if (const AstPin* const pinp = VN_CAST(nodep, Pin)) {
                if (AstVar* const varp = pinp->modVarp()) {
                    if (AstIfaceGenericDType* const ifaceGDTypep
                        = VN_CAST(varp->childDTypep(), IfaceGenericDType)) {
                        const auto iter = paramspMap.find(varp->name());
                        if (iter == paramspMap.end()) continue;
                        ifaceGDTypep->unlinkFrBack();
                        const AstPin* const paramp = iter->second;
                        paramspMap.erase(iter);
                        const AstIfaceRefDType* const ifacerefp
                            = VN_AS(paramp->exprp(), IfaceRefDType);
                        AstIfaceRefDType* const newIfacerefp = new AstIfaceRefDType{
                            ifaceGDTypep->fileline(), ifaceGDTypep->modportFileline(),
                            ifaceGDTypep->name(), ifacerefp->ifaceName(),
                            ifaceGDTypep->modportName()};
                        newIfacerefp->ifacep(ifacerefp->ifacep());
                        varp->childDTypep(newIfacerefp);
                        VL_DO_DANGLING(m_deleter.pushDeletep(ifaceGDTypep), ifaceGDTypep);
                        if (paramspMap.empty()) return;
                    }
                }
            }
        }

        UASSERT(paramspMap.empty(), "Not every generic interface implicit param is used");
    }

    void resolveDefaultParams(AstNode* nodep) {
        AstClassOrPackageRef* classOrPackageRef = VN_CAST(nodep, ClassOrPackageRef);
        AstClassRefDType* classRefDType = VN_CAST(nodep, ClassRefDType);
        AstClass* classp = nullptr;
        AstPin* paramsp = nullptr;

        if (classOrPackageRef) {
            classp = VN_CAST(classOrPackageRef->classOrPackageSkipp(), Class);
            if (!classp) return;  // No parameters in packages
            paramsp = classOrPackageRef->paramsp();
        } else if (classRefDType) {
            classp = classRefDType->classp();
            paramsp = classRefDType->paramsp();
        } else {
            nodep->v3fatalSrc("resolveDefaultParams called on node which is not a Class ref");
        }

        UASSERT_OBJ(classp, nodep, "Class or interface ref has no classp/ifacep");

        // Get the parameter list for this class
        m_classParams.clear();
        m_paramIndex.clear();
        for (AstNode* stmtp = classp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstParamTypeDType* paramTypep = VN_CAST(stmtp, ParamTypeDType)) {
                // Only consider formal class type parameters (generic parameters),
                // not localparam type declarations inside the class body.
                if (!paramTypep->isGParam()) continue;
                m_paramIndex.emplace(paramTypep, static_cast<int>(m_classParams.size()));
                m_classParams.emplace_back(paramTypep, -1);
            }
        }

        // For each parameter, detect either a dependent default (copy from previous param)
        // or a direct type default (for ex. int). Store dependency index in
        // m_classParams[i].second, default type in defaultTypeNodes[i].
        std::vector<AstNodeDType*> defaultTypeNodes(m_classParams.size(), nullptr);
        for (size_t i = 0; i < m_classParams.size(); ++i) {
            AstParamTypeDType* const paramTypep = m_classParams[i].first;
            // Parser places defaults/constraints under childDTypep as AstRequireDType
            AstRequireDType* const reqDtp = VN_CAST(paramTypep->getChildDTypep(), RequireDType);
            if (!reqDtp) continue;

            // If default is a reference to another param type, record dependency
            if (AstRefDType* const refDtp = VN_CAST(reqDtp->subDTypep(), RefDType)) {
                if (AstParamTypeDType* const sourceParamp
                    = VN_CAST(refDtp->refDTypep(), ParamTypeDType)) {
                    auto it = m_paramIndex.find(sourceParamp);
                    if (it != m_paramIndex.end()) { m_classParams[i].second = it->second; }
                    continue;  // dependency handled
                }
            }

            // If default is a direct type (for ex. int)
            // also record dependency
            if (AstNodeDType* const dtp = VN_CAST(reqDtp->lhsp(), NodeDType)) {
                defaultTypeNodes[i] = dtp;
            }
        }

        // Count existing pins and capture them by index for easy lookup
        std::vector<AstPin*> pinsByIndex;
        for (AstPin* pinp = paramsp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            pinsByIndex.push_back(pinp);
        }

        // For each missing parameter, get its pin from dependency or direct default
        for (size_t paramIdx = pinsByIndex.size(); paramIdx < m_classParams.size(); paramIdx++) {
            const int sourceParamIdx = m_classParams[paramIdx].second;

            AstPin* newPinp = nullptr;

            // Case 1: Dependent default -> clone the source pin's type
            if (sourceParamIdx >= 0) newPinp = pinsByIndex[sourceParamIdx]->cloneTree(false);

            // Case 2: Direct default type (e.g., int), create a new pin with that dtype
            if (!newPinp && defaultTypeNodes[paramIdx]) {
                AstNodeDType* const dtypep = defaultTypeNodes[paramIdx];
                newPinp = new AstPin{dtypep->fileline(), static_cast<int>(paramIdx) + 1,
                                     "__paramNumber" + cvtToStr(paramIdx + 1),
                                     dtypep->cloneTree(false)};
            }

            if (newPinp) {
                newPinp->name("__paramNumber" + cvtToStr(paramIdx + 1));
                newPinp->param(true);
                newPinp->modPTypep(m_classParams[paramIdx].first);
                if (classOrPackageRef) {
                    classOrPackageRef->addParamsp(newPinp);
                } else if (classRefDType) {
                    classRefDType->addParamsp(newPinp);
                }
                // Update local tracking so future dependent defaults can find it
                pinsByIndex.resize(paramIdx + 1, nullptr);
                pinsByIndex[paramIdx] = newPinp;
                if (!paramsp) paramsp = newPinp;
            }
        }
    }

    AstNodeModule* nodeDeparamCommon(AstNode* nodep, AstNodeModule* srcModp, AstPin* paramsp,
                                     AstPin* pinsp, bool any_overrides) {
        // Returns new or reused module
        // Make sure constification worked
        // Must be a separate loop, as constant conversion may have changed some pointers.
        string longname = srcModp->name() + "_";
        if (debug() >= 9 && paramsp) paramsp->dumpTreeAndNext(cout, "-  cellparams: ");

        if (srcModp->hierBlock()) {
            longname = parameterizedHierBlockName(srcModp, paramsp);
            any_overrides = longname != srcModp->name();
        } else {
            for (AstPin* pinp = paramsp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
                cellPinCleanup(nodep, pinp, srcModp, longname /*ref*/, any_overrides /*ref*/);
            }
        }
        IfaceRefRefs ifaceRefRefs;
        cellInterfaceCleanup(pinsp, srcModp, longname /*ref*/, any_overrides /*ref*/,
                             ifaceRefRefs /*ref*/);

        // Classes/modules with type parameters need specialization even when types match defaults.
        // This is required for UVM parameterized classes. However, interfaces should NOT
        // be specialized when type params match defaults (needed for nested interface ports).
        bool defaultsResolved = false;
        if (!any_overrides && !VN_IS(srcModp, Iface)) {
            for (AstPin* pinp = paramsp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
                if (pinp->modPTypep()) {
                    any_overrides = true;
                    defaultsResolved = true;
                    break;
                }
            }
        }

        UINFO(9, "iface capture nodeDeparamCommon: src='"
                     << srcModp->name() << "' longname='" << longname << "' any_overrides="
                     << any_overrides << " cell='" << nodep->name() << "'" << endl);

        AstNodeModule* newModp = nullptr;
        if (m_hierBlocks.hierSubRun() && m_hierBlocks.isHierBlock(srcModp->origName())) {
            AstNodeModule* const paramedModp
                = m_hierBlocks.findByParams(srcModp->origName(), paramsp, m_modp);
            UASSERT_OBJ(paramedModp, nodep, "Failed to find sub-module for hierarchical block");
            paramedModp->dead(false);
            // We need to relink the pins to the new module
            relinkPinsByName(pinsp, paramedModp);
            newModp = paramedModp;
            // any_overrides = true;  // Unused later, so not needed
        } else if (!any_overrides) {
            UINFO(9, "iface capture nodeDeparamCommon: NO OVERRIDES for '"
                         << srcModp->name() << "' cell='" << nodep->name() << "'" << endl);
            UINFO(9, "nodeDeparamCommon default-reuse: srcMod='"
                         << srcModp->name() << "' someInstanceName='"
                         << srcModp->someInstanceName()
                         << "' hasGParam=" << (srcModp->hasGParam() ? "yes" : "no")
                         << " dead=" << (srcModp->dead() ? "yes" : "no")
                         << " user3p=" << (srcModp->user3p() ? "set" : "null") << endl);
            UINFO(8, "Cell parameters all match original values, skipping expansion.");
            // If it's the first use of the default instance, create a copy and store it in user3p.
            // user3p will also be used to check if the default instance is used.
            if (!srcModp->user3p() && (VN_IS(srcModp, Class) || VN_IS(srcModp, Iface))) {
                AstNodeModule* nodeCopyp = srcModp->cloneTree(false);
                // It is a temporary copy of the original class node, stored in order to create
                // another instances. It is needed only during class instantiation.
                UINFO(8, "    Created clone " << nodeCopyp);
                m_deleter.pushDeletep(nodeCopyp);
                srcModp->user3p(nodeCopyp);
                storeOriginalParams(nodeCopyp);
            }
            newModp = srcModp;
        } else {
            const string newname
                = srcModp->hierBlock() ? longname : moduleCalcName(srcModp, longname);
            const ModInfo* const modInfop
                = moduleFindOrClone(srcModp, nodep, paramsp, newname, ifaceRefRefs);
            if (!modInfop) return nullptr;
            // We need to relink the pins to the new module
            relinkPinsByName(pinsp, modInfop->m_modp);
            UINFO(8, "     Done with " << modInfop->m_modp);
            newModp = modInfop->m_modp;
        }

        const bool cloned = (newModp != srcModp);
        UINFO(9, "iface capture module clone src=" << srcModp << " new=" << newModp << " name="
                                                   << newModp->name() << " from cell=" << nodep
                                                   << " cellName=" << nodep->name()
                                                   << " cloned=" << cloned);

        // Link source class to its specialized version for later relinking of method references
        if (defaultsResolved) srcModp->user4p(newModp);

        for (auto* stmtp = newModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstParamTypeDType* dtypep = VN_CAST(stmtp, ParamTypeDType)) {
                if (VN_IS(dtypep->skipRefOrNullp(), VoidDType)) {
                    nodep->v3error(
                        "Class parameter type without default value is never given value"
                        << " (IEEE 1800-2023 6.20.1): " << dtypep->prettyNameQ());
                    VL_DO_DANGLING(m_deleter.pushDeletep(nodep->unlinkFrBack()), nodep);
                }
            }
            if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                if (VN_IS(newModp, Class) && varp->isParam() && !varp->valuep()) {
                    nodep->v3error("Class parameter without default value is never given value"
                                   << " (IEEE 1800-2023 6.20.1): " << varp->prettyNameQ());
                }
            }
        }

        genericInterfaceVarSetup(paramsp, pinsp);

        // Delete the parameters from the cell; they're not relevant any longer.
        if (paramsp) paramsp->unlinkFrBackWithNext()->deleteTree();
        return newModp;
    }

    AstNodeModule* cellDeparam(AstCell* nodep, AstNodeModule* srcModp) {
        // Must always clone __Vrcm (recursive modules)
        AstNodeModule* const newModp = nodeDeparamCommon(nodep, srcModp, nodep->paramsp(),
                                                         nodep->pinsp(), nodep->recursive());
        if (!newModp) return nullptr;
        nodep->modp(newModp);  // Might be unchanged if not cloned (newModp == srcModp)
        nodep->modName(newModp->name());
        nodep->recursive(false);
        return newModp;
    }
    AstNodeModule* ifaceRefDeparam(AstIfaceRefDType* const nodep, AstNodeModule* srcModp) {
        // Check for self-reference pattern: typedef iface#(T) this_type inside interface iface
        // When processing inside a specialized interface, the IfaceRefDType should point to
        // the owner interface, not create an intermediate specialization.
        if (m_modp && VN_IS(m_modp, Iface)) {
            AstIface* ownerIfacep = const_cast<AstIface*>(VN_AS(m_modp, Iface));
            const string ownerOrigName
                = ownerIfacep->origName().empty() ? ownerIfacep->name() : ownerIfacep->origName();
            const string srcOrigName
                = srcModp->origName().empty() ? srcModp->name() : srcModp->origName();
            string ownerBaseName = ownerOrigName;
            const size_t ownerPos = ownerBaseName.find("__");
            if (ownerPos != string::npos) ownerBaseName = ownerBaseName.substr(0, ownerPos);
            string srcBaseName = srcOrigName;
            const size_t srcPos = srcBaseName.find("__");
            if (srcPos != string::npos) srcBaseName = srcBaseName.substr(0, srcPos);

            if (ownerBaseName == srcBaseName) {
                bool allOwnParams = true;
                for (AstPin* pinp = nodep->paramsp(); pinp && allOwnParams;
                     pinp = VN_AS(pinp->nextp(), Pin)) {
                    if (AstRefDType* const refp = VN_CAST(pinp->exprp(), RefDType)) {
                        if (AstParamTypeDType* const ptdp
                            = VN_CAST(refp->refDTypep(), ParamTypeDType)) {
                            AstNodeModule* const ptdOwnerp
                                = V3LinkDotIfaceCapture::findOwnerModule(ptdp);
                            if (ptdOwnerp != m_modp) allOwnParams = false;
                        } else {
                            allOwnParams = false;
                        }
                    } else {
                        allOwnParams = false;
                    }
                }
                if (allOwnParams) {
                    UINFO(5, "ifaceRefDeparam: self-reference pattern detected in "
                                 << ownerIfacep->name() << ", using owner interface" << endl);
                    nodep->ifacep(ownerIfacep);
                    if (nodep->paramsp()) nodep->paramsp()->unlinkFrBackWithNext()->deleteTree();
                    return ownerIfacep;
                }
            }
        }

        AstNodeModule* const newModp
            = nodeDeparamCommon(nodep, srcModp, nodep->paramsp(), nullptr, false);
        if (!newModp) return nullptr;
        nodep->ifacep(VN_AS(newModp, Iface));
        return newModp;
    }
    AstNodeModule* classRefDeparam(AstClassOrPackageRef* nodep, AstNodeModule* srcModp) {
        resolveDefaultParams(nodep);
        AstNodeModule* const newModp
            = nodeDeparamCommon(nodep, srcModp, nodep->paramsp(), nullptr, false);
        if (!newModp) return nullptr;
        nodep->classOrPackagep(newModp);  // Might be unchanged if not cloned (newModp == srcModp)

        // If this ClassOrPackageRef is a child of a RefDType (e.g., typedef class#(T)::member_t),
        // resolve the RefDType's typedef to point to the typedef inside the specialized class
        AstRefDType* const refDTypep = VN_CAST(nodep->backp(), RefDType);
        AstClass* const newClassp = refDTypep ? VN_CAST(newModp, Class) : nullptr;
        if (newClassp && !refDTypep->typedefp() && !refDTypep->subDTypep()) {
            if (AstTypedef* const typedefp
                = VN_CAST(m_memberMap.findMember(newClassp, refDTypep->name()), Typedef)) {
                refDTypep->typedefp(typedefp);
                refDTypep->classOrPackagep(newClassp);
                UINFO(9, "Resolved parameterized class typedef: " << refDTypep->name() << " -> "
                                                                  << typedefp << " in "
                                                                  << newClassp->name());
            }
        }
        return newModp;
    }
    AstNodeModule* classRefDeparam(AstClassRefDType* nodep, AstNodeModule* srcModp) {
        resolveDefaultParams(nodep);
        AstNodeModule* const newModp
            = nodeDeparamCommon(nodep, srcModp, nodep->paramsp(), nullptr, false);
        if (!newModp) return nullptr;
        AstClass* const newClassp = VN_AS(newModp, Class);
        nodep->classp(newClassp);  // Might be unchanged if not cloned (newModp == srcModp)
        nodep->classOrPackagep(newClassp);
        return newClassp;
    }

public:
    AstNodeModule* nodeDeparam(AstNode* nodep, AstNodeModule* srcModp, AstNodeModule* modp,
                               const string& someInstanceName) {
        // Return new or reused de-parameterized module
        m_modp = modp;
        // Cell: Check for parameters in the instantiation.
        // We always run this, even if no parameters, as need to look for interfaces,
        // and remove any recursive references
        UINFO(4, "De-parameterize: " << nodep);
        UINFO(9, "nodeDeparam ENTER node=<"
                     << AstNode::nodeAddr(nodep) << ">" << " type=" << nodep->typeName()
                     << " srcMod='" << (srcModp ? srcModp->name() : string("<null>")) << "'"
                     << " srcSomeInstanceName='"
                     << (srcModp ? srcModp->someInstanceName() : string("<null>")) << "'"
                     << " parentMod='" << (modp ? modp->name() : string("<null>")) << "'"
                     << " parentSomeInstanceName='"
                     << (modp ? modp->someInstanceName() : string("<null>")) << "'"
                     << " inputSomeInstanceName='" << someInstanceName << "'" << endl);
        // Create new module name with _'s between the constants
        UINFOTREE(10, nodep, "", "cell");
        // Evaluate all module constants
        V3Const::constifyParamsEdit(nodep);
        // Set name for warnings for when we param propagate the module
        // For AstIfaceRefDType, name() returns the modport name (often empty),
        // so use cellName() which is the actual cell instance name.
        // If both are empty (interface port, not a cell), skip appending
        // to avoid double-dots in the path.
        string nodeName = nodep->name();
        if (AstIfaceRefDType* const ifaceRefp = VN_CAST(nodep, IfaceRefDType)) {
            if (nodeName.empty()) nodeName = ifaceRefp->cellName();
        }
        const string instanceName
            = nodeName.empty() ? someInstanceName : (someInstanceName + "." + nodeName);
        srcModp->someInstanceName(instanceName);
        UINFO(9, "nodeDeparam SET-SRC-INST srcMod='"
                     << srcModp->name() << "' someInstanceName='" << srcModp->someInstanceName()
                     << "'" << " node=<" << AstNode::nodeAddr(nodep) << ">"
                     << " nodeType=" << nodep->typeName() << endl);

        AstNodeModule* newModp = nullptr;
        if (AstCell* const cellp = VN_CAST(nodep, Cell)) {
            newModp = cellDeparam(cellp, srcModp);
        } else if (AstIfaceRefDType* const ifaceRefDTypep = VN_CAST(nodep, IfaceRefDType)) {
            newModp = ifaceRefDeparam(ifaceRefDTypep, srcModp);
        } else if (AstClassRefDType* const classRefp = VN_CAST(nodep, ClassRefDType)) {
            newModp = classRefDeparam(classRefp, srcModp);
        } else if (AstClassOrPackageRef* const classRefp = VN_CAST(nodep, ClassOrPackageRef)) {
            newModp = classRefDeparam(classRefp, srcModp);
        } else {
            nodep->v3fatalSrc("Expected module parameterization");
        }
        // 'newModp' might be nullptr on error
        if (!newModp) return nullptr;

        // Set name for later warnings
        newModp->someInstanceName(instanceName);

        UINFO(9, "nodeDeparam EXIT  node=<"
                     << AstNode::nodeAddr(nodep) << ">" << " type=" << nodep->typeName()
                     << " srcMod='" << (srcModp ? srcModp->name() : string("<null>")) << "'"
                     << " srcSomeInstanceName='"
                     << (srcModp ? srcModp->someInstanceName() : string("<null>")) << "'"
                     << " newMod='" << (newModp ? newModp->name() : string("<null>")) << "'"
                     << " newSomeInstanceName='"
                     << (newModp ? newModp->someInstanceName() : string("<null>")) << "'" << endl);

        UINFO(8, "     Done with orig " << nodep);
        // if (debug() >= 10)
        // v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("param-out.tree"));
        return newModp;
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
// Record classes that are referenced with parameter pins

class ClassRefUnlinkerVisitor final : public VNVisitor {

public:
    explicit ClassRefUnlinkerVisitor(AstNetlist* netlistp) { iterate(netlistp); }
    void visit(AstClassOrPackageRef* nodep) override {
        if (nodep->paramsp()) {
            if (AstClass* const classp = VN_CAST(nodep->classOrPackageSkipp(), Class)) {
                if (!classp->user3p()) {
                    // Check if this ClassOrPackageRef is the lhsp of a DOT node
                    AstDot* const dotp = VN_CAST(nodep->backp(), Dot);
                    if (dotp && dotp->lhsp() == nodep) {
                        // Replace DOT with just its rhsp to avoid leaving DOT with null lhsp
                        dotp->replaceWith(dotp->rhsp()->unlinkFrBack());
                        VL_DO_DANGLING2(pushDeletep(dotp), dotp, nodep);
                    } else {
                        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
                    }
                }
            }
        }
    }
    void visit(AstClass* nodep) override {}  // don't iterate inside classes
    void visit(AstNode* nodep) override { iterateChildren(nodep); }
};

//######################################################################
// Process parameter top state

class ParamState final {
public:
    // STATE - across all visitors
    std::vector<AstClass*> m_paramClasses;  // Parameterized classes
    std::vector<AstDot*> m_dots;  // Dot references to process
    std::multimap<int, AstNodeModule*> m_workQueueNext;  // Modules left to process
    // Map from AstNodeModule to set of all AstNodeModules that instantiates it.
    std::unordered_map<AstNodeModule*, std::unordered_set<AstNodeModule*>> m_parentps;
};

//######################################################################
// Process parameter visitor

class ParamVisitor final : public VNVisitor {
    // NODE STATE
    // AstNodeModule::user1 -> bool: already fixed level (temporary)
    // AstNodeDType::user2  -> bool: already visited from typedef

    // STATE - across all visitors
    ParamState& m_state;  // Common state
    ParamProcessor m_processor;  // De-parameterize a cell, build modules
    GenForUnroller m_unroller;  // Unroller for AstGenFor

    bool m_iterateModule = false;  // Iterating module body
    string m_unlinkedTxt;  // Text for AstUnlinkedRef
    std::multimap<bool, AstNode*> m_cellps;  // Cells left to process (in current module)
    std::deque<std::string> m_strings;  // Allocator for temporary strings
    std::map<const AstRefDType*, bool>
        m_isCircular;  // Stores information whether `AstRefDType` is circular

    // STATE - for current visit position (use VL_RESTORER)
    AstNodeModule* m_modp = nullptr;  // Module iterating
    std::unordered_set<std::string> m_ifacePortNames;  // Interface port names in current module
    std::unordered_set<std::string> m_ifaceInstNames;  // Interface decl names in current module
    string m_generateHierName;  // Generate portion of hierarchy name

    // METHODS

    void processWorkQ() {
        UASSERT(!m_iterateModule, "Should not nest");
        std::multimap<int, AstNodeModule*> workQueue;
        m_generateHierName = "";
        m_iterateModule = true;

        // Visit all cells under module, recursively
        while (true) {
            if (workQueue.empty()) std::swap(workQueue, m_state.m_workQueueNext);
            if (workQueue.empty()) break;

            const auto itm = workQueue.cbegin();
            AstNodeModule* const modp = itm->second;
            workQueue.erase(itm);

            // Process once; note user2 will be cleared on specialization, so we will do the
            // specialized module if needed
            if (!modp->user2SetOnce()) {
                UINFO(9, "processWorkQ module begin mod='"
                             << modp->name() << "' orig='" << modp->origName() << "'"
                             << " someInstanceName='" << modp->someInstanceName() << "'"
                             << " hasGParam=" << (modp->hasGParam() ? "yes" : "no")
                             << " user3p=" << (modp->user3p() ? "set" : "null")
                             << " dead=" << (modp->dead() ? "yes" : "no") << endl);

                // TODO: this really should be an assert, but classes and hier_blocks are
                // special...
                if (modp->someInstanceName().empty()) modp->someInstanceName(modp->origName());

                // Iterate the body
                {
                    VL_RESTORER(m_modp);
                    VL_RESTORER(m_ifacePortNames);
                    VL_RESTORER(m_ifaceInstNames);
                    m_modp = modp;
                    m_ifacePortNames.clear();
                    m_ifaceInstNames.clear();
                    iterateChildren(modp);
                }
            }

            // Process interface cells, then non-interface cells, which may reference an interface
            // cell.
            while (!m_cellps.empty()) {
                const auto itim = m_cellps.cbegin();
                AstNode* const cellp = itim->second;
                m_cellps.erase(itim);

                AstNodeModule* srcModp = nullptr;
                if (const AstCell* modCellp = VN_CAST(cellp, Cell)) {
                    srcModp = modCellp->modp();
                } else if (const AstClassOrPackageRef* classRefp
                           = VN_CAST(cellp, ClassOrPackageRef)) {
                    srcModp = classRefp->classOrPackageSkipp();
                    if (VN_IS(classRefp->classOrPackageNodep(), ParamTypeDType)) continue;
                } else if (const AstClassRefDType* classRefp = VN_CAST(cellp, ClassRefDType)) {
                    srcModp = classRefp->classp();
                } else if (const AstIfaceRefDType* ifaceRefp = VN_CAST(cellp, IfaceRefDType)) {
                    srcModp = ifaceRefp->ifacep();
                } else {
                    cellp->v3fatalSrc("Expected module parameterization");
                }
                if (!srcModp) continue;

                // Update path
                string someInstanceName = modp->someInstanceName();
                if (const string* const genHierNamep = cellp->user2u().to<string*>()) {
                    someInstanceName += *genHierNamep;
                    cellp->user2p(nullptr);
                }

                // Apply parameter specialization
                if (AstNodeModule* const newModp
                    = m_processor.nodeDeparam(cellp, srcModp, modp, someInstanceName)) {

                    if (VN_IS(srcModp, Iface)) {
                        logTemplateLeakRefs(modp, srcModp, "after queued nodeDeparam", cellp);
                    }

                    // Add the (now potentially specialized) child module to the work queue
                    workQueue.emplace(newModp->level(), newModp);

                    // Add to the hierarchy registry
                    m_state.m_parentps[newModp].insert(modp);
                }
            }
        }

        m_iterateModule = false;
    }

    // Extract the base reference name from a dotted VarXRef (e.g., "iface.FOO" -> "iface")
    string getRefBaseName(const AstVarXRef* refp) {
        const string dotted = refp->dotted();
        if (dotted.empty()) return "";
        return dotted.substr(0, dotted.find('.'));
    }

    void logTemplateLeakRefs(AstNodeModule* parentModp, AstNodeModule* templateModp,
                             const char* stage, AstNode* contextp) {
        if (debug() < 9 || !parentModp || !templateModp) return;
        if (!VN_IS(templateModp, Iface)) return;
        int leakCount = 0;
        const auto ancestryOf = [](const AstNode* nodep) {
            string ancestry;
            for (const AstNode* curp = nodep; curp; curp = curp->backp()) {
                if (!ancestry.empty()) ancestry += "<-";
                ancestry += curp->typeName();
                if (VN_IS(curp, NodeModule) || VN_IS(curp, Netlist) || VN_IS(curp, TypeTable)) {
                    break;
                }
            }
            return ancestry;
        };

        parentModp->foreach([&](AstRefDType* refp) {
            if (refp->typedefp()) {
                AstNodeModule* const tdOwnerp
                    = V3LinkDotIfaceCapture::findOwnerModule(refp->typedefp());
                if (tdOwnerp == templateModp) {
                    ++leakCount;
                    UINFO(9, "TEMPLATE-LEAK "
                                 << stage << " parent='" << parentModp->name() << "'"
                                 << " template='" << templateModp->name() << "'" << " contextType="
                                 << (contextp ? contextp->typeName() : string("<null>"))
                                 << " contextName='"
                                 << (contextp ? contextp->name() : string("<null>")) << "'"
                                 << " leak=REFDTYPE typedef owner" << " ref=<"
                                 << AstNode::nodeAddr(refp) << ">" << " refName='" << refp->name()
                                 << "'" << " ancestry=" << ancestryOf(refp) << endl);
                }
            }
            if (refp->refDTypep()) {
                AstNodeModule* const rdOwnerp
                    = V3LinkDotIfaceCapture::findOwnerModule(refp->refDTypep());
                if (rdOwnerp == templateModp) {
                    ++leakCount;
                    UINFO(9, "TEMPLATE-LEAK "
                                 << stage << " parent='" << parentModp->name() << "'"
                                 << " template='" << templateModp->name() << "'" << " contextType="
                                 << (contextp ? contextp->typeName() : string("<null>"))
                                 << " contextName='"
                                 << (contextp ? contextp->name() : string("<null>")) << "'"
                                 << " leak=REFDTYPE refDType owner" << " ref=<"
                                 << AstNode::nodeAddr(refp) << ">" << " refName='" << refp->name()
                                 << "'" << " ancestry=" << ancestryOf(refp) << endl);
                }
            }
        });

        parentModp->foreach([&](AstVarRef* varrefp) {
            if (!varrefp->varp()) return;
            AstNodeModule* const varOwnerp
                = V3LinkDotIfaceCapture::findOwnerModule(varrefp->varp());
            if (varOwnerp != templateModp) return;
            ++leakCount;
            UINFO(9, "TEMPLATE-LEAK "
                         << stage << " parent='" << parentModp->name() << "'" << " template='"
                         << templateModp->name() << "'"
                         << " contextType=" << (contextp ? contextp->typeName() : string("<null>"))
                         << " contextName='" << (contextp ? contextp->name() : string("<null>"))
                         << "'" << " leak=VARREF target owner" << " ref=<"
                         << AstNode::nodeAddr(varrefp) << ">" << " var='" << varrefp->name() << "'"
                         << " ancestry=" << ancestryOf(varrefp) << endl);
        });

        if (leakCount > 0) {
            UINFO(9, "TEMPLATE-LEAK summary stage='" << stage << "' parent='" << parentModp->name()
                                                     << "' template='" << templateModp->name()
                                                     << "' count=" << leakCount << endl);
        }
    }

    void checkParamNotHier(AstNode* valuep) {
        if (!valuep) return;
        valuep->foreachAndNext([&](const AstNodeExpr* exprp) {
            if (const AstVarXRef* const refp = VN_CAST(exprp, VarXRef)) {
                // Allow hierarchical ref to interface params through interface/modport ports
                // or local interface instances
                bool isIfaceRef = false;
                if (refp->varp() && refp->varp()->isIfaceParam()) {
                    const string refname = getRefBaseName(refp);
                    isIfaceRef
                        = !refname.empty()
                          && (m_ifacePortNames.count(refname) || m_ifaceInstNames.count(refname));
                }

                if (!isIfaceRef) {
                    refp->v3warn(HIERPARAM, "Parameter values cannot use hierarchical values"
                                            " (IEEE 1800-2023 6.20.2)");
                }
            } else if (const AstNodeFTaskRef* refp = VN_CAST(exprp, NodeFTaskRef)) {
                if (refp->dotted() != "") {
                    refp->v3error("Parameter values cannot call hierarchical functions"
                                  " (IEEE 1800-2023 6.20.2)");
                }
            }
        });
    }

    // Check if cell parameters reference interface ports or local interface instances
    bool cellParamsReferenceIfacePorts(AstCell* cellp) {
        if (!cellp->paramsp()) return false;

        for (AstNode* nodep = cellp->paramsp(); nodep; nodep = nodep->nextp()) {
            if (AstPin* const pinp = VN_CAST(nodep, Pin)) {
                if (AstNode* const exprp = pinp->exprp()) {
                    if (const AstVarXRef* const refp = VN_CAST(exprp, VarXRef)) {
                        const string refname = getRefBaseName(refp);
                        if (!refname.empty()
                            && (m_ifacePortNames.count(refname)
                                || m_ifaceInstNames.count(refname)))
                            return true;
                    }
                }
            }
        }
        return false;
    }

    // Recursively specialize nested interface cells within a specialized interface.
    // This handles parameter passthrough for nested interface hierarchies.
    void specializeNestedIfaceCells(AstNodeModule* ifaceModp) {
        for (AstNode* stmtp = ifaceModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            AstCell* const nestedCellp = VN_CAST(stmtp, Cell);
            if (!nestedCellp) continue;
            if (!VN_IS(nestedCellp->modp(), Iface)) continue;
            if (!nestedCellp->paramsp()) continue;
            if (cellParamsReferenceIfacePorts(nestedCellp)) continue;

            AstNodeModule* const nestedSrcModp = nestedCellp->modp();
            if (AstNodeModule* const nestedNewModp = m_processor.nodeDeparam(
                    nestedCellp, nestedSrcModp, ifaceModp, ifaceModp->someInstanceName())) {
                // Recursively process nested interfaces within this nested interface
                if (nestedNewModp != nestedSrcModp) specializeNestedIfaceCells(nestedNewModp);
            }
        }
    }

    // A generic visitor for cells and class refs
    void visitCellOrClassRef(AstNode* nodep, bool isIface) {
        // Must do ifaces first, so push to list and do in proper order
        m_strings.emplace_back(m_generateHierName);
        nodep->user2p(&m_strings.back());

        // For interface cells with parameters, specialize first before processing children
        // Only do early specialization if parameters don't reference interface ports
        if (isIface && VN_CAST(nodep, Cell) && VN_CAST(nodep, Cell)->paramsp()) {
            AstCell* const cellp = VN_CAST(nodep, Cell);
            if (!cellParamsReferenceIfacePorts(cellp)) {
                AstNodeModule* const srcModp = cellp->modp();
                // DISABLED: specializeNestedIfaceCells causes early nested
                // iface specialization where PARAMTYPEDTYPE child REFDTYPEs
                // point to template structs instead of clone structs,
                // destructively widthing the template with default (zero)
                // values. See t_interface_nested_struct_param.v.
                m_processor.nodeDeparam(cellp, srcModp, m_modp, m_modp->someInstanceName());
            }
        }

        // Visit parameters in the instantiation.
        iterateChildren(nodep);
        m_cellps.emplace(!isIface, nodep);
    }

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        if (nodep->recursiveClone()) nodep->dead(true);  // Fake, made for recursive elimination
        if (nodep->dead()) return;  // Marked by LinkDot (and above)
        UINFO(9, "V3Param: visit module name='"
                     << nodep->name() << "' orig='" << nodep->origName() << "' someInstanceName='"
                     << nodep->someInstanceName()
                     << "' hasGParam=" << (nodep->hasGParam() ? "yes" : "no")
                     << " user3p=" << (nodep->user3p() ? "set" : "null")
                     << " dead=" << (nodep->dead() ? "yes" : "no") << endl);
        if (AstClass* const classp = VN_CAST(nodep, Class)) {
            if (classp->hasGParam()) {
                // Don't enter into a definition.
                // If a class is used, it will be visited through a reference and cloned
                m_state.m_paramClasses.push_back(classp);
                return;
            }
        }

        if (m_iterateModule) {  // Iterating from processWorkQ
            UINFO(4, " MOD-under-MOD.  " << nodep);
            // Delay until current module is done.
            // processWorkQ() (which we are returning to) will process nodep later
            m_state.m_workQueueNext.emplace(nodep->level(), nodep);
            return;
        }

        // Start traversal at root-like things
        if (nodep->isTop()  // Tops
            || VN_IS(nodep, Class)  //  Moved classes
            || VN_IS(nodep, Package)) {  // Likewise haven't done wrapTopPackages yet
            m_state.m_workQueueNext.emplace(nodep->level(), nodep);
            processWorkQ();
        }
    }

    bool isCircularType(const AstRefDType* nodep) {
        const auto iter = m_isCircular.emplace(nodep, true);
        if (!iter.second) return iter.first->second;
        if (const AstRefDType* const subDTypep = VN_CAST(nodep->subDTypep(), RefDType)) {
            const bool ret = isCircularType(subDTypep);
            iter.first->second = ret;
            return ret;
        }
        iter.first->second = false;
        return false;
    }

    void visit(AstRefDType* nodep) override {
        if (isCircularType(nodep)) {
            nodep->v3error("Typedef's type is circular: " << nodep->prettyName());
        } else if (nodep->typedefp() && nodep->subDTypep()
                   && (VN_IS(nodep->subDTypep()->skipRefOrNullp(), IfaceRefDType)
                       || VN_IS(nodep->subDTypep()->skipRefOrNullp(), ClassRefDType))
                   && !nodep->skipRefp()->user2SetOnce()) {
            iterate(nodep->skipRefp());
        }
        iterateChildren(nodep);
    }
    void visit(AstCell* nodep) override {
        checkParamNotHier(nodep->paramsp());
        // Build cache of locally declared interface instance names
        if (VN_IS(nodep->modp(), Iface)) { m_ifaceInstNames.insert(nodep->name()); }
        visitCellOrClassRef(nodep, VN_IS(nodep->modp(), Iface));
    }
    void visit(AstIfaceRefDType* nodep) override {
        if (nodep->ifacep()) visitCellOrClassRef(nodep, true);
    }
    void visit(AstClassRefDType* nodep) override {
        checkParamNotHier(nodep->paramsp());
        visitCellOrClassRef(nodep, false);
    }
    void visit(AstClassOrPackageRef* nodep) override {
        // If it points to a typedef it is not really a class reference. That typedef will be
        // visited anyway (from its parent node), so even if it points to a parameterized class
        // type, the instance will be created.
        if (!VN_IS(nodep->classOrPackageNodep(), Typedef)) visitCellOrClassRef(nodep, false);
    }

    // Make sure all parameters are constantified
    void visit(AstVar* nodep) override {
        if (nodep->user2SetOnce()) return;  // Process once
        // Build cache of interface port names as we encounter them
        if (nodep->isIfaceRef()) { m_ifacePortNames.insert(nodep->name()); }
        iterateChildren(nodep);
        if (nodep->isParam()) {
            checkParamNotHier(nodep->valuep());
            if (!nodep->valuep() && !VN_IS(m_modp, Class)) {
                nodep->v3error("Parameter without default value is never given value"
                               << " (IEEE 1800-2023 6.20.1): " << nodep->prettyNameQ());
            } else if (nodep->valuep()) {
                // In visit(AstVar*) for localparams, check if expression contains VARXREF
                // to another localparam (not parameter). Parameters are already const,
                // but localparams may not be evaluated yet.
                bool hasVarXRefToLparam = false;
                nodep->valuep()->foreach([&](const AstVarXRef* xrefp) {
                    if (xrefp->varp() && xrefp->varp()->varType() == VVarType::LPARAM) {
                        hasVarXRefToLparam = true;
                    }
                });
                if (hasVarXRefToLparam) {
                    // Don't constify - let it be evaluated later
                    return;
                }

                V3Const::constifyParamsEdit(nodep);
            }
        }
    }
    void visit(AstParamTypeDType* nodep) override {
        iterateChildren(nodep);
        if (VN_IS(nodep->skipRefOrNullp(), VoidDType)) {
            nodep->v3error("Parameter type without default value is never given value"
                           << " (IEEE 1800-2023 6.20.1): " << nodep->prettyNameQ());
        }
    }
    // Make sure varrefs cause vars to constify before things above
    void visit(AstVarRef* nodep) override {
        // Might jump across functions, so beware if ever add a m_funcp
        if (nodep->varp()) iterate(nodep->varp());
    }
    bool ifaceParamReplace(AstVarXRef* nodep, AstNode* candp) {
        for (; candp; candp = candp->nextp()) {
            if (nodep->name() == candp->name()) {
                if (AstVar* const varp = VN_CAST(candp, Var)) {
                    UINFO(9, "Found interface parameter: " << varp);
                    nodep->varp(varp);
                    return true;
                } else if (const AstPin* const pinp = VN_CAST(candp, Pin)) {
                    UINFO(9, "Found interface parameter: " << pinp);
                    UASSERT_OBJ(pinp->exprp(), pinp, "Interface parameter pin missing expression");
                    nodep->replaceWith(pinp->exprp()->cloneTree(false));
                    VL_DO_DANGLING(pushDeletep(nodep), nodep);
                    return true;
                }
            }
        }
        return false;
    }
    void visit(AstVarXRef* nodep) override {
        if (nodep->containsGenBlock()) {
            // Needs relink, as may remove pointed-to var
            nodep->varp(nullptr);
            return;
        }
        // Check to see if the scope is just an interface because interfaces are special
        const string dotted = nodep->dotted();
        if (!dotted.empty() && nodep->varp() && nodep->varp()->isParam()) {
            const AstNode* backp = nodep;
            while ((backp = backp->backp())) {
                if (VN_IS(backp, NodeModule)) {
                    UINFO(9, "Hit module boundary, done looking for interface");
                    break;
                }
                if (const AstVar* const varp = VN_CAST(backp, Var)) {
                    if (!varp->isIfaceRef()) continue;
                    const AstIfaceRefDType* ifacerefp = nullptr;
                    if (const AstNodeDType* const typep = varp->childDTypep()) {
                        ifacerefp = VN_CAST(typep, IfaceRefDType);
                        if (!ifacerefp) {
                            if (VN_IS(typep, UnpackArrayDType)) {
                                ifacerefp = VN_CAST(typep->getChildDTypep(), IfaceRefDType);
                            }
                        }
                        if (!ifacerefp) {
                            if (VN_IS(typep, BracketArrayDType)) {
                                ifacerefp = VN_CAST(typep->subDTypep(), IfaceRefDType);
                            }
                        }
                    }
                    if (!ifacerefp) continue;
                    // Interfaces passed in on the port map have ifaces
                    if (const AstIface* const ifacep = ifacerefp->ifacep()) {
                        if (dotted == backp->name()) {
                            UINFO(9, "Iface matching scope:  " << ifacep);
                            if (ifaceParamReplace(nodep, ifacep->stmtsp())) {  //
                                return;
                            }
                        }
                    }
                    // Interfaces declared in this module have cells
                    else if (const AstCell* const cellp = ifacerefp->cellp()) {
                        if (dotted == cellp->name()) {
                            UINFO(9, "Iface matching scope:  " << cellp);
                            if (ifaceParamReplace(nodep, cellp->modp()->stmtsp())) {  //
                                return;
                            }
                        }
                    }
                }
            }
        }
    }

    void visit(AstDot* nodep) override {
        iterate(nodep->lhsp());
        // Check if it is a reference to a field of a parameterized class.
        // If so, the RHS should be updated, when the LHS is replaced
        // by a class with actual parameter values.
        const AstClass* lhsClassp = nullptr;
        const AstClassOrPackageRef* const classRefp = VN_CAST(nodep->lhsp(), ClassOrPackageRef);
        if (classRefp) lhsClassp = VN_CAST(classRefp->classOrPackageSkipp(), Class);
        AstNode* rhsDefp = nullptr;
        AstClassOrPackageRef* const rhsp = VN_CAST(nodep->rhsp(), ClassOrPackageRef);
        if (rhsp) rhsDefp = rhsp->classOrPackageNodep();
        if (lhsClassp && rhsDefp) {
            m_state.m_dots.push_back(nodep);
            // No need to iterate into rhsp, because there should be nothing to do
        } else {
            iterate(nodep->rhsp());
        }
    }

    void visit(AstUnlinkedRef* nodep) override {
        AstVarXRef* const varxrefp = VN_CAST(nodep->refp(), VarXRef);
        AstNodeFTaskRef* const taskrefp = VN_CAST(nodep->refp(), NodeFTaskRef);
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
        nodep->replaceWith(nodep->refp()->unlinkFrBack());
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstCellArrayRef* nodep) override {
        V3Const::constifyParamsEdit(nodep->selp());
        if (const AstConst* const constp = VN_CAST(nodep->selp(), Const)) {
            const string index = AstNode::encodeNumber(constp->toSInt());
            // For nested interface array ports, the node name may have a __Viftop suffix
            // that doesn't exist in the original unlinked text. Try without the suffix.
            const string viftopSuffix = "__Viftop";
            const string baseName
                = VString::endsWith(nodep->name(), viftopSuffix)
                      ? nodep->name().substr(0, nodep->name().size() - viftopSuffix.size())
                      : nodep->name();
            const string replacestr = baseName + "__BRA__??__KET__";
            const size_t pos = m_unlinkedTxt.find(replacestr);
            // For interface port array element selections (e.g., l1(l2.l1[0])),
            // the AstCellArrayRef may be visited outside of an AstUnlinkedRef context.
            // In such cases, m_unlinkedTxt won't contain the expected pattern.
            // Simply skip the replacement - the cell array ref will be resolved later.
            if (pos == string::npos) {
                UINFO(9, "Skipping unlinked text replacement for " << nodep << endl);
                return;
            }
            m_unlinkedTxt.replace(pos, replacestr.length(),
                                  baseName + "__BRA__" + index + "__KET__");
        } else {
            nodep->v3error("Could not expand constant selection inside dotted reference: "
                           << nodep->selp()->prettyNameQ());
            return;
        }
    }

    // Generate Statements
    void visit(AstGenIf* nodep) override {
        UINFO(9, "  GENIF " << nodep);
        iterateAndNextNull(nodep->condp());
        // We suppress errors when widthing params since short-circuiting in
        // the conditional evaluation may mean these error can never occur. We
        // then make sure that short-circuiting is used by constifyParamsEdit.
        V3Width::widthGenerateParamsEdit(nodep);  // Param typed widthing will
                                                  // NOT recurse the body.
        V3Const::constifyGenerateParamsEdit(nodep->condp());  // condp may change
        if (const AstConst* const constp = VN_CAST(nodep->condp(), Const)) {
            if (AstNode* const keepp = (constp->isZero() ? nodep->elsesp() : nodep->thensp())) {
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

    void visit(AstGenBlock* nodep) override {
        // Parameter substitution for generated for loops.
        // TODO Unlike generated IF, we don't have to worry about short-circuiting the
        // conditional expression, since this is currently restricted to simple
        // comparisons. If we ever do move to more generic constant expressions, such code
        // will be needed here.
        if (AstGenFor* const forp = VN_AS(nodep->genforp(), GenFor)) {
            // We should have a GENFOR under here.  We will be replacing the begin,
            // so process here rather than at the generate to avoid iteration problems
            UINFO(9, "  BEGIN " << nodep);
            UINFO(9, "  GENFOR " << forp);
            // Visit child nodes before unrolling
            iterateAndNextNull(forp->initsp());
            iterateAndNextNull(forp->condp());
            iterateAndNextNull(forp->incsp());
            V3Width::widthParamsEdit(forp);  // Param typed widthing will NOT recurse the body
            // Outer wrapper around generate used to hold genvar, and to ensure genvar
            // doesn't conflict in V3LinkDot resolution with other genvars
            // Now though we need to change BEGIN("zzz", GENFOR(...)) to
            // a BEGIN("zzz__BRA__{loop#}__KET__")
            const string beginName = nodep->name();
            // Leave the original Begin, as need a container for the (possible) GENVAR
            // Note m_unroller will replace some AstVarRef's to the loop variable with constants
            // Don't remove any deleted nodes in m_unroller until whole process finishes,
            // as some AstXRefs may still point to old nodes.
            VL_DO_DANGLING(m_unroller.unroll(forp, beginName), forp);
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
    void visit(AstGenFor* nodep) override {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc("GENFOR should have been wrapped in BEGIN");
    }
    void visit(AstGenCase* nodep) override {
        UINFO(9, "  GENCASE " << nodep);
        bool hit = false;
        AstNode* keepp = nullptr;
        iterateAndNextNull(nodep->exprp());
        V3Case::caseLint(nodep);
        V3Width::widthParamsEdit(nodep);  // Param typed widthing will NOT recurse the
                                          // body, don't trigger errors yet.
        V3Const::constifyParamsEdit(nodep->exprp());  // exprp may change
        const AstConst* const exprp = VN_AS(nodep->exprp(), Const);
        // Constify
        for (AstGenCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), GenCaseItem)) {
            for (AstNode* ep = itemp->condsp(); ep;) {
                AstNode* const nextp = ep->nextp();  // May edit list
                iterateAndNextNull(ep);
                VL_DO_DANGLING(V3Const::constifyParamsEdit(ep), ep);  // ep may change
                ep = nextp;
            }
        }
        // Item match
        for (AstGenCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), GenCaseItem)) {
            if (!itemp->isDefault()) {
                for (AstNode* ep = itemp->condsp(); ep; ep = ep->nextp()) {
                    if (const AstConst* const ccondp = VN_CAST(ep, Const)) {
                        V3Number match{nodep, 1};
                        match.opEq(ccondp->num(), exprp->num());
                        if (!hit && match.isNeqZero()) {
                            hit = true;
                            keepp = itemp->itemsp();
                        }
                    } else {
                        itemp->v3error("Generate Case item does not evaluate to constant");
                    }
                }
            }
        }
        // Else default match
        for (AstGenCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), GenCaseItem)) {
            if (itemp->isDefault()) {
                if (!hit) {
                    hit = true;
                    keepp = itemp->itemsp();
                }
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

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ParamVisitor(ParamState& state, AstNetlist* netlistp)
        : m_state{state}
        , m_processor{netlistp} {

        // Relies on modules already being in top-down-order
        iterate(netlistp);
    }
    ~ParamVisitor() override = default;
    VL_UNCOPYABLE(ParamVisitor);
};

//######################################################################
// Process top handler

class ParamTop final : VNDeleter {
    // NODE STATE
    // AstNodeModule::user1 -> bool: already fixed level (temporary)

    // STATE
    ParamState m_state;  // Common state

    // METHODS

    void relinkDots() {
        // RHSs of AstDots need a relink when LHS is a parameterized class reference
        for (AstDot* const dotp : m_state.m_dots) {
            const AstClassOrPackageRef* const classRefp = VN_AS(dotp->lhsp(), ClassOrPackageRef);
            const AstClass* const lhsClassp = VN_AS(classRefp->classOrPackageSkipp(), Class);
            AstClassOrPackageRef* const rhsp = VN_AS(dotp->rhsp(), ClassOrPackageRef);
            for (auto* itemp = lhsClassp->membersp(); itemp; itemp = itemp->nextp()) {
                if (itemp->name() == rhsp->name()) {
                    rhsp->classOrPackageNodep(itemp);
                    break;
                }
            }
        }
    }

    void fixLevel(AstNodeModule* modp) {
        // Fix up level of module, based on who instantiates it
        if (modp->user1SetOnce()) return;  // Already fixed
        if (m_state.m_parentps[modp].empty()) return;  // Leave top levels alone
        int maxParentLevel = 0;
        for (AstNodeModule* parentp : m_state.m_parentps[modp]) {
            fixLevel(parentp);  // Ensure parent level is correct
            maxParentLevel = std::max(maxParentLevel, parentp->level());
        }
        if (modp->level() <= maxParentLevel) modp->level(maxParentLevel + 1);
        // Not correct fixup of depth(), as it should be mininum.  But depth() is unused
        // past V3LinkParse, so just do something sane in case this code doesn't get updated
        modp->depth(modp->level());
    }

    void resortNetlistModules(AstNetlist* netlistp) {
        // Re-sort module list to be in topological order and fix-up incorrect levels. We need to
        // do this globally at the end due to the presence of recursive modules, which might be
        // expanded in orders that reuse earlier specializations later at a lower level.
        // Gather modules
        std::vector<AstNodeModule*> modps;
        for (AstNodeModule *modp = netlistp->modulesp(), *nextp; modp; modp = nextp) {
            nextp = VN_AS(modp->nextp(), NodeModule);
            modp->unlinkFrBack();
            modps.push_back(modp);
        }

        // Fix-up levels
        const VNUser1InUse user1InUse;
        for (AstNodeModule* const modp : modps) fixLevel(modp);

        // Sort by level
        std::stable_sort(modps.begin(), modps.end(),
                         [](const AstNodeModule* ap, const AstNodeModule* bp) {
                             return ap->level() < bp->level();
                         });

        // Re-insert modules
        for (AstNodeModule* const modp : modps) netlistp->addModulesp(modp);
    }

public:
    // CONSTRUCTORS
    explicit ParamTop(AstNetlist* netlistp) {
        // Relies on modules already being in top-down-order
        ParamVisitor paramVisitor{m_state /*ref*/, netlistp};

        // Mark classes which cannot be removed because they are still referenced
        ClassRefUnlinkerVisitor classUnlinkerVisitor{netlistp};

        netlistp->foreach([](AstNodeFTaskRef* ftaskrefp) {
            AstNodeFTask* ftaskp = ftaskrefp->taskp();
            if (!ftaskp || !ftaskp->classMethod()) return;
            string funcName = ftaskp->name();
            // Find the nearest containing (ancestor) class for a node.
            // backp() walks the sibling linked-list before reaching the
            // true parent, so a naive backp() walk can land on a sibling
            // class (e.g. a covergroup) instead of the enclosing class.
            // Track the previous node so we can distinguish parent links
            // (where prevp is a child of np) from sibling links (where
            // prevp is a later sibling of np).
            const auto ancestorClassOf = [](AstNode* startp) -> AstClass* {
                AstNode* prevp = startp;
                for (AstNode* np = startp->backp(); np; prevp = np, np = np->backp()) {
                    if (AstClass* const cp = VN_CAST(np, Class)) {
                        // np is a true parent of prevp when prevp is one of
                        // np's op children (not reached via nextp chain).
                        // firstAbovep() returns backp() only for list heads.
                        if (prevp->firstAbovep() == np) return cp;
                        // Otherwise prevp is a later sibling - skip this class.
                        continue;
                    }
                }
                return nullptr;
            };
            AstClass* refClassp = ancestorClassOf(ftaskrefp);
            if (refClassp == ftaskrefp->classOrPackagep())
                return;  // task is in the same class as reference
            AstClass* classp = ancestorClassOf(ftaskp);
            UASSERT_OBJ(classp, ftaskrefp, "Class method has no class above it");
            // If the FUNCREF and its task are both in the same (clone) class but
            // classOrPackagep still points to the old template, just retarget it
            if (refClassp && refClassp == classp && ftaskrefp->classOrPackagep()
                && ftaskrefp->classOrPackagep() != refClassp) {
                ftaskrefp->classOrPackagep(refClassp);
                return;
            }
            if (classp->user3p()) return;  // will not get removed, no need to relink
            AstClass* const parametrizedClassp = VN_CAST(classp->user4p(), Class);
            if (!parametrizedClassp) return;
            AstNodeFTask* newFuncp = nullptr;
            parametrizedClassp->exists([&newFuncp, funcName](AstNodeFTask* ftaskp) {
                if (ftaskp->name() == funcName) {
                    newFuncp = ftaskp;
                    return true;
                }
                return false;
            });
            if (newFuncp) {
                // v3error(ftaskp <<"->" << newFuncp);
                ftaskrefp->taskp(newFuncp);
                ftaskrefp->classOrPackagep(parametrizedClassp);
            }
        });

        relinkDots();

        resortNetlistModules(netlistp);

        // For occasional debug only; this will upset VL_LEAK_CHECKS
        // V3Global::dumpCheckGlobalTree("param-predel", 0, dumpTreeEitherLevel() >= 9);

        // Remove defaulted classes
        // Unlike modules, which we keep around and mark dead() for later V3Dead
        std::unordered_set<AstClass*> removedClassps;
        for (AstClass* const classp : m_state.m_paramClasses) {
            if (!classp->user3p()) {
                // If there was an error, don't remove classes as they might
                // have remained referenced, and  will crash in V3Broken or
                // other locations. This is fine, we will abort imminently.
                if (V3Error::errorCount()) continue;
                removedClassps.emplace(classp);
                VL_DO_DANGLING(pushDeletep(classp->unlinkFrBack()), classp);
            } else {
                // Referenced. classp became a specialized class with the default
                // values of parameters and is not a parameterized class anymore
                classp->hasGParam(false);
            }
        }
        // Remove references to defaulted classes
        // Reuse user3 to mark all nodes being deleted
        AstNode::user3ClearTree();
        for (AstClass* classp : removedClassps) {
            classp->foreach([](AstNode* const nodep) { nodep->user3(true); });
        }
        // Set all links pointing to a user3 (deleting) node as null
        netlistp->foreach([](AstNode* const nodep) {
            nodep->foreachLink([&](AstNode** const linkpp, const char* namep) {
                if (*linkpp && (*linkpp)->user3()) {
                    UINFO(9, "clear   link " << namep << " on " << nodep);
                    *linkpp = nullptr;
                    UINFO(9, "cleared link " << namep << " on " << nodep);
                }
            });
        });
    }
    ~ParamTop() = default;
    VL_UNCOPYABLE(ParamTop);
};

//######################################################################
// Param class functions

void V3Param::param(AstNetlist* rootp) {
    UINFO(2, __FUNCTION__ << ":");

    V3LinkDotIfaceCapture::dumpEntries("before V3Param");
    { ParamTop{rootp}; }
    V3LinkDotIfaceCapture::purgeStaleRefs();
    V3LinkDotIfaceCapture::dumpEntries("after V3Param");

    V3Global::dumpCheckGlobalTree("param", 0, dumpTreeEitherLevel() >= 3);
}
