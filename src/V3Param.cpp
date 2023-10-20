// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Replicate modules for parameterization
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// PARAM TRANSFORMATIONS:
//   Top down traversal:
//      For each cell/classref:
//          If linked module/class parameterizable,
//              Determine all parameter widths, constant values.
//              (Interfaces also matter, as if a module is parameterized
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

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Param.h"

#include "V3Case.h"
#include "V3Const.h"
#include "V3File.h"
#include "V3Hasher.h"
#include "V3Os.h"
#include "V3Parse.h"
#include "V3Unroll.h"
#include "V3Width.h"

#include <cctype>
#include <deque>
#include <memory>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Descriptions

struct ModParamSet {
    struct Hash {
        size_t operator()(const ModParamSet* params) const noexcept { return params->m_hashValue; }
    };
    struct Compare {
        bool operator()(const ModParamSet* x, const ModParamSet* y) const {
#if VL_DEBUG
            UASSERT(x->m_params.size() == y->m_params.size(), "vector size mismatch");
            UASSERT(x->m_typeParams.size() == y->m_typeParams.size(), "vector size mismatch");
            UASSERT(x->m_ifaces.size() == y->m_ifaces.size(), "vector size mismatch");
#endif
            const size_t paramCount = x->m_params.size();
            for (size_t i = 0; i < paramCount; i++) {
                const AstNodeExpr* const xParam = x->m_params[i];
                const AstNodeExpr* const yParam = y->m_params[i];
                if (!xParam && !yParam) {  // both null
                } else if (!xParam || !yParam) {  // null vs. non-null
                    return false;
                } else if (!xParam->sameTree(yParam)) {
                    return false;
                }
            }
            const size_t typeParamCount = x->m_typeParams.size();
            for (size_t i = 0; i < typeParamCount; i++) {
                const AstNodeDType* const xParam = x->m_typeParams[i];
                const AstNodeDType* const yParam = y->m_typeParams[i];
                if (!xParam && !yParam) {  // both null
                } else if (!xParam || !yParam) {  // null vs. non-null
                    return false;
                    // } else if (x->m_typeParams[i]->type() != y->m_typeParams[i]->type()) {
                    //     return false;
                } else if (!xParam->similarDType(yParam)) {
                    return false;
                }
            }
            const size_t ifaceCount = x->m_ifaces.size();
            for (size_t i = 0; i < ifaceCount; i++) {
                if (x->m_ifaces[i] != y->m_ifaces[i]) return false;
            }
            return true;
        }
    };

private:
    size_t m_hashValue = 0;

public:
    // TODO: merge m_params and m_typeParams
    std::vector<AstNodeExpr*> m_params;
    std::vector<AstNodeDType*> m_typeParams;
    std::vector<AstNodeModule*> m_ifaces;

    ModParamSet() = default;

    void skipTypesRef() {
        for (auto& item : m_typeParams)
            if (item) item = item->skipRefToEnump();
    }
    void rehash() {
        V3Hash m_hash;
        for (AstNodeExpr* const param : m_params) {
            m_hash += param ? V3Hasher::uncachedHash(param) : V3Hash();
        }
        for (AstNodeDType* const param : m_typeParams) {
            m_hash += param ? V3Hasher::uncachedHash(param->skipRefToEnump()) : V3Hash();
        }
        for (AstNodeModule* const iface : m_ifaces) { m_hash += reinterpret_cast<size_t>(iface); }
        m_hashValue = static_cast<size_t>(m_hash.value());
    }
};

class BaseModInfo {
public:  // error C2248: cannot access protected enumerator declared in class 'BaseModInfo' in MSVC
    enum ModType : int {
        ORIGINAL_MOD,
        DEPARAMED_MOD,
    };

protected:
    ModType m_type;
    bool m_visited = false;
    BaseModInfo(ModType type)
        : m_type(type) {}

public:
    void destroy();
    static bool isParameterizable(const void* userp) {
        return userp >= reinterpret_cast<const void*>(0x10);
    }
    static bool isVisited(const void* userp) {
        if (userp == reinterpret_cast<const void*>(0x2)) {
            // Not a parameterizable modules, visited
            return true;
        } else if (isParameterizable(userp)) {
            return static_cast<const BaseModInfo*>(userp)->visited();
        } else {
            return false;
        }
    }
    static void* setVisited(void* userp) {
        if (!isParameterizable(userp)) {
            return reinterpret_cast<void*>(0x2);  // Not a parameterizable modules, visited
        } else {
            static_cast<BaseModInfo*>(userp)->visited(true);
            return userp;
        }
    }
    bool isDeparamed() const {
        switch (m_type) {
        case DEPARAMED_MOD: return true;
        case ORIGINAL_MOD: return false;
        default: v3fatalSrc("bad case");
        }
        return false;
    }
    bool visited() const { return m_visited; }
    void visited(bool flag) { m_visited = flag; }
};

class ModInfo : public BaseModInfo {
    struct ParamMap : public std::unordered_map<const ModParamSet*, AstNodeModule*,
                                                ModParamSet::Hash, ModParamSet::Compare> {
        ~ParamMap() {
            for (auto& item : *this) delete item.first;  // delete the ModParamSet
        }
        AstNodeModule* findNode(const ModParamSet* paramSet) {
            const auto it = find(paramSet);
            return it != end() ? it->second : nullptr;
        }
    };
    /// Keep the original modules tracked, so we can delete them after everything is done
    AstNodeModule* const m_origModp;
    /// Parameter nodes of the unparameterized node.  Map the parameters to the index in the vector
    /// in the ModParamSet structure.  Note the nodes is not inordered when iterating.
    const std::map<const AstVar*, int> m_paramIndexMap;
    const std::map<const AstParamTypeDType*, int> m_typeParamIndexMap;
    const std::map<const AstVar*, int> m_ifaceIndexMap;
    /// Map full param sets to specialized instances
    ParamMap m_paramsMap;
    /// Map overridden param sets to specialized instances, used to cache overridden params from
    /// Cell/ClassRef
    ParamMap m_overriddenMap;

public:
    ModInfo(AstNodeModule* origModp, std::map<const AstVar*, int>&& paramIndexMap,
            std::map<const AstParamTypeDType*, int>&& typeParamIndexMap,
            std::map<const AstVar*, int>&& ifaceIndexMap)
        : BaseModInfo(BaseModInfo::ORIGINAL_MOD)
        , m_origModp(origModp)
        , m_paramIndexMap(std::move(paramIndexMap))
        , m_typeParamIndexMap(std::move(typeParamIndexMap))
        , m_ifaceIndexMap(std::move(ifaceIndexMap)) {}
    ~ModInfo() {
        if (VN_IS(m_origModp, Class))  // Unused modules/ifaces are removed in V3Dead
            VL_DO_DANGLING(m_origModp->unlinkFrBack()->deleteTree(), m_origModp);
    }
    const auto& paramIndexMap() const { return m_paramIndexMap; }
    const auto& typeParamIndexMap() const { return m_typeParamIndexMap; }
    const auto& ifaceIndexMap() const { return m_ifaceIndexMap; }
    AstNodeModule* findNodeWithFullParamSet(const ModParamSet* paramSet) {
        return m_paramsMap.findNode(paramSet);
    }
    AstNodeModule* findNodeWithOverriddenParamSet(const ModParamSet* paramSet) {
        return m_overriddenMap.findNode(paramSet);
    }
    void insertFullParamSet(const ModParamSet* paramSet, AstNodeModule* nodep) {
        m_paramsMap[paramSet] = nodep;
    }
    void insertOverriddenParamSet(const ModParamSet* paramSet, AstNodeModule* nodep) {
        m_overriddenMap[paramSet] = nodep;
    }
    size_t nextParamModIndex() const { return m_paramsMap.size() + 1; }
    AstNodeModule* originalModp() const { return m_origModp; }
    void dumpSelf(std::ostream& os) const {
        os << m_origModp->prettyTypeName() << " (" << m_origModp << ")\n";
        for (const auto& nodeItem : m_paramsMap) {
            // TODO: print inorder
            os << "- Parameterized node " << nodeItem.second->name() << ":  " << nodeItem.second
               << "\n";
            const ModParamSet* const paramSet = nodeItem.first;
            for (const auto& item : m_paramIndexMap) {
                string str;
                if (AstConst* const constp = VN_CAST(paramSet->m_params[item.second], Const)) {
                    str = constp->num().ascii();
                } else if (AstInitArray* const initArrp
                           = VN_CAST(paramSet->m_params[item.second], InitArray)) {
                    str = "InitArray[" + std::to_string(initArrp->map().size()) + "]";
                }
                os << "    param " << item.second << ": " << item.first->name() << " -> "
                   << (!str.empty() ? str : "(none)") << "\n";
            }
            for (const auto& item : m_typeParamIndexMap) {
                os << "    type param " << item.second << ": " << item.first->name() << " -> ";
                if (const AstNodeDType* const dtypep = paramSet->m_typeParams[item.second]) {
                    os << dtypep->prettyDTypeName() + " (" << dtypep << ")";
                } else {
                    os << "(none)";
                }
                os << "\n";
            }
            for (const auto& item : m_ifaceIndexMap) {
                os << "    interface " << item.second << ": " << item.first->name() << " -> ";
                if (const AstNodeModule* const modp = paramSet->m_ifaces[item.second])
                    os << modp;
                else
                    os << "(none)";
                os << "\n";
            }
            os << endl;
        }
    }
};

class DeparamedModInfo : public BaseModInfo {
    /// Maps pins in original to pins in cloned module, used to relink pins/params after cloning.
    /// Contains nodes for ports/parameters/localparams
    std::map<const AstNode*, AstNode*> m_pinMap;

public:
    DeparamedModInfo()
        : BaseModInfo(ModInfo::DEPARAMED_MOD) {}
    ~DeparamedModInfo() = default;
    void setPinMap(const std::map<const AstNode*, AstNode*>& pinMap) {
        m_pinMap = std::move(pinMap);
    }
    void insertPinMap(const AstNode* origNode, AstNode* nodep) { m_pinMap[origNode] = nodep; }
    AstNode* findPinMap(const AstNode* origNode) {
        const auto it = m_pinMap.find(origNode);
        return it != m_pinMap.end() ? it->second : nullptr;
    }
};

void BaseModInfo::destroy() {
    switch (m_type) {
    case ORIGINAL_MOD:  //
        delete static_cast<ModInfo*>(this);
        return;
    case DEPARAMED_MOD:  //
        delete static_cast<DeparamedModInfo*>(this);
        return;
    default: v3fatalSrc("bad case");
    }
}

//######################################################################
// Remove parameters from cells and build new modules

class ParamProcessor final {
    // NODE STATE - Shared with ParamVisitor
    //   User1/2/3 used by constant function simulations
    //   User4 shared with V3Hasher
    //   AstNodeModule::user5p() // BaseModInfo* 0x1: Not a parameterizable modules, nor visited
    //                                           0x2: Not a parameterizable modules, visited
    //                                           0x3: Module probing. Used to detect circular
    //                                               referencing
    //                                           Other non-null values: BaseModInfo for
    //                                               parameterizable modules
    //   AstGenFor::user5()      // bool         True if processed
    //   AstVar::user5()         // bool         True if constant propagated
    //   AstCell::user5p()       // string*      Generate portion of hierarchical name
    const VNUser5InUse m_inuser5;

    // STATE
    AstNodeModule* m_modp = nullptr;  // Current module being processed
    AstNode* m_cellNodep = nullptr;  // Current cell/classref/... being processed
    std::map<const AstNode*, AstNode*> m_clonedModPinMap;
    std::vector<BaseModInfo*> m_allocatedModInfo;
    VNDeleter m_deleter;  // Used to delay deletion of nodes

    // METHODS
    static AstNodeDType* arraySubDTypep(AstNodeDType* nodep) {
        // If an unpacked array, return the subDTypep under it
        if (const AstUnpackArrayDType* const adtypep = VN_CAST(nodep, UnpackArrayDType)) {
            return adtypep->subDTypep();
        }
        // We have not resolved parameter of the child yet, so still have BracketArrayDType's.
        // We'll presume it'll end up as assignment compatible (or V3Width will complain).
        if (const AstBracketArrayDType* const adtypep = VN_CAST(nodep, BracketArrayDType)) {
            return adtypep->subDTypep();
        }
        return nullptr;
    }
    static bool isString(AstNodeDType* nodep) {
        if (AstBasicDType* const basicp = VN_CAST(nodep->skipRefToEnump(), BasicDType))
            return basicp->isString();
        return false;
    }
    static void replaceRefsRecurse(AstNode* const nodep, const AstClass* const oldClassp,
                                   AstClass* const newClassp) {
        // Self references linked in the first pass of V3LinkDot.cpp should point to the default
        // instance.
        if (AstClassRefDType* const classRefp = VN_CAST(nodep, ClassRefDType)) {
            if (classRefp->classp() == oldClassp) classRefp->classp(newClassp);
        } else if (AstClassOrPackageRef* const classPkgRefp = VN_CAST(nodep, ClassOrPackageRef)) {
            if (classPkgRefp->classOrPackagep() == oldClassp)
                classPkgRefp->classOrPackagep(newClassp);
        }

        if (nodep->op1p()) replaceRefsRecurse(nodep->op1p(), oldClassp, newClassp);
        if (nodep->op2p()) replaceRefsRecurse(nodep->op2p(), oldClassp, newClassp);
        if (nodep->op3p()) replaceRefsRecurse(nodep->op3p(), oldClassp, newClassp);
        if (nodep->op4p()) replaceRefsRecurse(nodep->op4p(), oldClassp, newClassp);
        if (nodep->nextp()) replaceRefsRecurse(nodep->nextp(), oldClassp, newClassp);
    }
    static AstConst* convertToStringp(AstNode* nodep) {
        // Should be called on values of parameters of type string to convert them to properly
        // typed string constants. Has no effect if the value is not a string constant.
        AstConst* const constp = VN_CAST(nodep, Const);
        AstConst* newConstp = constp;
        // Check if it wasn't already converted
        if (constp && !constp->num().isString()) {
            newConstp
                = new AstConst{constp->fileline(), AstConst::String{}, constp->num().toString()};
            constp->replaceWith(newConstp);
            constp->deleteTree();
        }
        return newConstp;
    }
    static AstIfaceRefDType* getIfaceDtypeFromVar(const AstVar* varp) {
        AstNodeDType* const varDtypep = varp->subDTypep();
        AstIfaceRefDType* ifDtypep = VN_CAST(varDtypep, IfaceRefDType);
        if (!ifDtypep) ifDtypep = VN_CAST(arraySubDTypep(varDtypep), IfaceRefDType);
        return ifDtypep;
    }
    static AstIface* getIfaceFromVar(const AstVar* varp) {
        AstIfaceRefDType* ifDtypep = getIfaceDtypeFromVar(varp);
        UASSERT_OBJ(ifDtypep, varp, "Interface port is not linked");
        return ifDtypep->ifaceViaCellp();
    }
    //! Check if the module/class can be parameterized (has parameter, or for modules, has
    //! interface port that can be parameterized), and collect the parameters and parameterizable
    //! interfaces for further uses.  Not for cloned modules.
    void probeModule(AstNodeModule* modp) {
        if (modp->user5p()) return;  // Already processed
        modp->user5p(reinterpret_cast<void*>(0x3));  // Avoid circular reference
        // Collect all parameters and parameterizable interface ports inside source module
        std::map<const AstVar*, int> paramIndexMap;
        std::map<const AstParamTypeDType*, int> typeParamIndexMap;
        std::map<const AstVar*, int> ifaceIndexMap;
        for (auto* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (const AstVar* const varp = VN_CAST(stmtp, Var)) {
                if (varp->isGParam()) {
                    paramIndexMap[varp] = paramIndexMap.size();
                } else if (varp->isIfaceRef()) {
                    AstIface* const ifacep = getIfaceFromVar(varp);
                    probeModule(ifacep);
                    BaseModInfo* ifaceModInfop = ifacep->user5u().to<BaseModInfo*>();
                    if (ifaceModInfop == reinterpret_cast<BaseModInfo*>(0x3)) {
                        m_cellNodep->v3error("Circular reference on interface ports");
                    } else if (BaseModInfo::isParameterizable(ifaceModInfop)) {
                        ifaceIndexMap[varp] = ifaceIndexMap.size();
                    }
                }
            } else if (AstParamTypeDType* const dtypep = VN_CAST(stmtp, ParamTypeDType)) {
                if (dtypep->isGParam()) typeParamIndexMap[dtypep] = typeParamIndexMap.size();
            }
        }
        UINFO(6, "  probeModule: " << modp << endl);
        UINFO(6, "    " << paramIndexMap.size() << " params, " << typeParamIndexMap.size()
                        << " type params, " << ifaceIndexMap.size() << " param ifaces" << endl);
        const bool hasGParam = !paramIndexMap.empty() || !typeParamIndexMap.empty();
        const bool isParameterizable = hasGParam || !ifaceIndexMap.empty();
        UASSERT(hasGParam == modp->hasGParam(), "modp->hasGParam() is not consistent");
        ModInfo* modInfop;
        if (isParameterizable) {
            modInfop = new ModInfo(modp, std::move(paramIndexMap), std::move(typeParamIndexMap),
                                   std::move(ifaceIndexMap));
            m_allocatedModInfo.push_back(modInfop);
        } else {
            // 0x1: Not a parameterizable modules, nor visited
            modInfop = reinterpret_cast<ModInfo*>(0x1);
        }
        modp->user5p(modInfop);
    }
    template <typename T_KEY, typename T_VAL>
    void insertOverriddenParamSet(T_KEY* key, const std::map<const T_KEY*, int>& paramIndexMap,
                                  std::vector<T_VAL*>& paramList, T_VAL* paramVal,
                                  const AstPin* errp) {
        const auto it = paramIndexMap.find(key);
        UASSERT_OBJ(it != paramIndexMap.end(), errp, "Invalid pin connection");
        int index = it->second;
        UASSERT_OBJ(index < static_cast<int>(paramList.size()), errp, "Pin list corrupted");
        paramList[index] = paramVal;
    }
    //! Collect overridden parameters from Cell/ClassRef
    ModParamSet* collectOverriddenParamSet(const ModInfo* modInfop, const AstPin* paramsp,
                                           const AstPin* pinsp) {
        auto& paramIndexMap = modInfop->paramIndexMap();
        auto& typeParamIndexMap = modInfop->typeParamIndexMap();
        auto& ifaceIndexMap = modInfop->ifaceIndexMap();
        std::vector<AstNodeExpr*> params{paramIndexMap.size(), nullptr};
        std::vector<AstNodeDType*> typeParams{typeParamIndexMap.size(), nullptr};
        std::vector<AstNodeModule*> ifaces{ifaceIndexMap.size(), nullptr};
        for (auto* pinp = paramsp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            if (!pinp->exprp()) continue;
            if (AstVar* const modVarp = pinp->modVarp()) {
                if (!modVarp->isGParam()) continue;
                AstNodeExpr* exprp = VN_CAST(pinp->exprp(), NodeExpr);
                if (!exprp) continue;
                if (!VN_IS(exprp, InitArray)) exprp = V3Const::constifyParamsEdit(exprp);
                if (AstConst* constp = VN_CAST(exprp, Const)) {
                    // Some constants not under AstVar are not converted to string automatically,
                    // so we need to convert them here.
                    if (isString(modVarp->subDTypep())) exprp = convertToStringp(constp);
                } else if (modInfop->originalModp()->hierBlock()) {
                    continue;  // hierarchical blocks only support using Const
                } else if (VN_IS(exprp, InitArray) && arraySubDTypep(modVarp->subDTypep())) {
                    // Array assigned to array
                } else {
                    pinp->v3error("Can't convert parameter value to constant: Param "
                                  << pinp->prettyNameQ() << " of " << m_cellNodep->prettyNameQ());
                    continue;
                }
                insertOverriddenParamSet(modVarp, paramIndexMap, params, exprp, pinp);
            } else if (AstParamTypeDType* const paramDTypep = pinp->modPTypep()) {
                AstNodeDType* dtypep = VN_CAST(pinp->exprp(), NodeDType);
                insertOverriddenParamSet(paramDTypep, typeParamIndexMap, typeParams, dtypep, pinp);
            }
        }
        for (auto* pinp = pinsp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            if (AstVar* const modVarp = pinp->modVarp()) {
                if (!modVarp->isIfaceRef()) continue;
                const AstNode* const exprp = pinp->exprp();
                const AstVarRef* varrefp = VN_CAST(exprp, VarRef);
                if (!varrefp) {
                    if (const AstNodePreSel* const preselp = VN_CAST(exprp, NodePreSel)) {
                        varrefp = VN_CAST(preselp->fromp(), VarRef);
                    }
                }
                const AstVar* const ifaceVarp = varrefp->varp();
                AstNodeModule* ifacep = getIfaceFromVar(ifaceVarp);
                UASSERT_OBJ(ifacep, varrefp, "Ifaceref not linked to module");
                probeModule(ifacep);
                if (!BaseModInfo::isParameterizable(ifacep->user5p())) continue;
                insertOverriddenParamSet(modVarp, ifaceIndexMap, ifaces, ifacep, pinp);
            }
        }
        auto* paramSetp = new ModParamSet;
        paramSetp->m_params = std::move(params);
        paramSetp->m_typeParams = std::move(typeParams);
        paramSetp->m_ifaces = std::move(ifaces);
        paramSetp->rehash();
        return paramSetp;
    }
    void replaceVarValue(AstVar* clonedNodep, AstNode* valuep) {
        if (auto* const nodep = clonedNodep->valuep()) nodep->unlinkFrBack()->deleteTree();
        clonedNodep->valuep(valuep);
    }
    void replaceVarValue(AstParamTypeDType* clonedNodep, AstNodeDType* valuep) {
        if (auto* const dtypep = clonedNodep->childDTypep()) dtypep->unlinkFrBack()->deleteTree();
        clonedNodep->childDTypep(valuep);
    }
    template <typename T_KEY, typename T_VAL>
    void assignParamsToClonedModule(const std::map<const T_KEY*, int>& paramIndexMap,
                                    const std::vector<T_VAL*>& params) {
        for (const auto& item : paramIndexMap) {
            if (T_VAL* const val = params[item.second]) {
                replaceVarValue(item.first->clonep(), val);
            }
        }
    }
    template <typename T_KEY>
    void assignParamsToClonedModule(const std::map<const T_KEY*, int>& paramIndexMap,
                                    const std::vector<AstNodeModule*>& params) {
        for (const auto& item : paramIndexMap) {
            AstIfaceRefDType* dtypep = getIfaceDtypeFromVar(item.first->clonep());
            if (AstNodeModule* const modp = params[item.second]) {
                dtypep->ifacep(VN_AS(modp, Iface));
            }
        }
    }
    /// Deep clone original module, assign parameters to it, and check if they're valid.
    /// Note all module internal variables will be re-linked to the new modules by clone. However,
    /// links outside the module (like on the upper cells) will not.
    AstNodeModule* deepCloneModule(AstNodeModule* srcModp, ModInfo* modInfop,
                                   ModParamSet* paramsp) {
        // Clone parameters before the tree, so it won't make clonep inaccessible
        std::vector<AstNodeExpr*> paramCopies{paramsp->m_params};
        std::vector<AstNodeDType*> typeParamCopies{paramsp->m_typeParams};
        for (AstNodeExpr*& paramp : paramCopies)
            if (paramp) paramp = paramp->cloneTree(false);
        for (AstNodeDType*& typep : typeParamCopies)
            if (typep) typep = typep->cloneTree(false);

        // Deep clone the module
        AstNodeModule* const newModp = srcModp->cloneTree(false);
        UINFO(6, "  Clone module: " << srcModp << endl);
        UINFO(6, "        result: " << newModp << endl);

        if (AstClass* const newClassp = VN_CAST(newModp, Class)) {
            replaceRefsRecurse(newModp->stmtsp(), newClassp, VN_AS(srcModp, Class));
        }
        // Assign params to the cloned module
        assignParamsToClonedModule(modInfop->paramIndexMap(), paramCopies);
        assignParamsToClonedModule(modInfop->typeParamIndexMap(), typeParamCopies);
        assignParamsToClonedModule(modInfop->ifaceIndexMap(), paramsp->m_ifaces);
        // Collect all parameters and I/O pins, so we can remap them for other referencing cells or
        // XRefs later.
        // Since V3Const::constifyParamsEdit used in evaluateModParams may also clone some nodes
        // and make clonep of the pins inaccessible, so we have to collect them here
        collectPins(newModp);
        return newModp;
    }
    //! Evaluate parameters not overridden by the referencing cells, in a newly-cloned module, and
    //! collect values of these parameters.
    //! @return the cloned module, with parameters propagated
    AstNodeModule* evaluateModParams(AstNodeModule* srcModp, ModInfo* modInfop,
                                     ModParamSet* paramsp) {
        AstNodeModule* const newModp = deepCloneModule(srcModp, modInfop, paramsp);
        // Propagate constant through the parameters in the new module
        for (const auto& item : modInfop->paramIndexMap()) {  // TODO: this is not inordered
            AstVar* clonedVarp = VN_AS(m_clonedModPinMap[item.first], Var);
            if (!VN_IS(clonedVarp->valuep(), Const)) V3Const::constifyParamsEdit(clonedVarp);
        }
        for (const auto& item : modInfop->typeParamIndexMap()) {
            AstParamTypeDType* clonedVarp = VN_AS(m_clonedModPinMap[item.first], ParamTypeDType);
            // Don't width clonedVarp directly as it may remove it's subDTypep
            V3Const::constifyParamsEdit(clonedVarp->subDTypep());
        }
        // Collect evaluated parameters
        for (const auto& item : modInfop->paramIndexMap()) {
            AstVar* clonedVarp = VN_AS(m_clonedModPinMap[item.first], Var);
            // clonedVarp->varType(VVarType::LPARAM);
            if (paramsp->m_params[item.second]) continue;
            paramsp->m_params[item.second] = VN_CAST(clonedVarp->valuep(), NodeExpr);
            // TODO: add test for this / already warned in V3Width?
            // if (AstConst* constp = VN_CAST(clonedVarp->valuep(), Const)) {
            // } else {
            //     clonedVarp->v3error("failed to evaluate\n"
            //                         << clonedVarp->warnMore() << clonedVarp->valuep());
            // }
        }
        for (const auto& item : modInfop->typeParamIndexMap()) {
            AstParamTypeDType* clonedVarp = VN_AS(m_clonedModPinMap[item.first], ParamTypeDType);
            if (paramsp->m_typeParams[item.second]) continue;
            paramsp->m_typeParams[item.second] = clonedVarp->childDTypep();
        }
        return newModp;
    }
    //! Grab all I/O, so we can remap our pins later
    void collectPins(AstNodeModule* clonedModp) {
        m_clonedModPinMap.clear();
        for (AstNode* stmtp = clonedModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            const AstNode* origNodep = nullptr;
            bool isPin = false;
            if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                if (varp->isIO() || varp->isIfaceRef()) isPin = true;
                if (isPin || varp->isParam()) {
                    // Cloning saved a pointer to the new node for us, so just follow that link.
                    origNodep = varp->clonep();
                }
            } else if (AstParamTypeDType* const ptp = VN_CAST(stmtp, ParamTypeDType)) {
                if (ptp->isGParam()) origNodep = ptp->clonep();
            }
            if (origNodep) { m_clonedModPinMap[origNodep] = stmtp; }
        }
    }
    void relinkPins(DeparamedModInfo* modInfo, AstPin* pinsp) {
        for (AstPin* pinp = pinsp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            if (AstVar* const varp = pinp->modVarp()) {
                const auto newVarp = modInfo->findPinMap(varp);
                UASSERT_OBJ(newVarp, pinp, "Couldn't find pin in clone list");
                pinp->modVarp(VN_AS(newVarp, Var));
            } else if (AstParamTypeDType* const typep = pinp->modPTypep()) {
                const auto newTypep = modInfo->findPinMap(typep);
                UASSERT_OBJ(newTypep, pinp, "Couldn't find pin in clone list");
                pinp->modPTypep(VN_AS(newTypep, ParamTypeDType));
            } else {
                pinp->v3fatalSrc("Not linked?");
            }
        }
    }
    bool updateClonedModInfo(ModInfo* modInfop, AstNodeModule* clonedModp) {
        AstNodeModule* const modp = modInfop->originalModp();
        string suffix;
        if (!modInfop->originalModp()->hierBlock()) {
            suffix = "__parameterized" + std::to_string(modInfop->nextParamModIndex());
        } else {
            suffix = "_hierblk" + std::to_string(modInfop->nextParamModIndex());
        }
        const string newModName = modp->name() + suffix;
        clonedModp->name(newModName);
        clonedModp->hasGParam(false);
        clonedModp->recursive(false);
        clonedModp->recursiveClone(false);
        // Only the first generation of clone holds this property
        clonedModp->hierBlock(modp->hierBlock() && !modp->recursiveClone());
        // Recursion may need level cleanups
        if (clonedModp->level() <= m_modp->level()) clonedModp->level(m_modp->level() + 1);
        UINFO(6, "  New paramed module: " << clonedModp << endl);
        if ((clonedModp->level() - modp->level()) >= (v3Global.opt.moduleRecursionDepth() - 2)) {
            m_cellNodep->v3error("Exceeded maximum --module-recursion-depth of "
                                 << v3Global.opt.moduleRecursionDepth());
            return false;
        }
        return true;
    }
    bool checkIfacePinConnection(AstPin* pinsp) {
        for (AstPin* pinp = pinsp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            const AstVar* const modvarp = pinp->modVarp();
            if (!modvarp->isIfaceRef()) continue;
            AstNodeDType* const ifaceDtypep = modvarp->subDTypep();
            AstIfaceRefDType* portIrefp = VN_CAST(ifaceDtypep, IfaceRefDType);
            if (!portIrefp) portIrefp = VN_CAST(arraySubDTypep(ifaceDtypep), IfaceRefDType);

            const AstNode* const exprp = pinp->exprp();
            const AstVarRef* varrefp = VN_CAST(exprp, VarRef);
            if (!varrefp) {
                if (const AstNodePreSel* const preselp = VN_CAST(exprp, NodePreSel)) {
                    varrefp = VN_CAST(preselp->fromp(), VarRef);
                }
            }
            AstIfaceRefDType* pinIrefp = nullptr;
            if (varrefp) {
                if (const AstVar* const varp = varrefp->varp()) {
                    AstNodeDType* const pinDtypep = varp->subDTypep();
                    pinIrefp = VN_CAST(pinDtypep, IfaceRefDType);
                    if (!pinIrefp) pinIrefp = VN_CAST(arraySubDTypep(pinDtypep), IfaceRefDType);
                }
            }
            if (!portIrefp) {
                pinp->v3error("Interface port " << modvarp->prettyNameQ()
                                                << " is not an interface " << modvarp);
            } else if (!pinIrefp) {
                pinp->v3error("Interface port "
                              << modvarp->prettyNameQ()
                              << " is not connected to interface/modport pin expression");
            } else if (portIrefp->ifaceViaCellp() != pinIrefp->ifaceViaCellp()) {
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
        return true;
    }
    bool checkCellParamSet(ModInfo* modInfop, ModParamSet* cellParam, AstPin* pinsp) {
        // Check parameters not given value
        for (const auto& item : modInfop->paramIndexMap()) {
            if (!item.first->valuep() && !cellParam->m_params[item.second]
                && VN_IS(modInfop->originalModp(), Class)) {
                m_cellNodep->v3error("Class parameter without initial value is never given value"
                                     << " (IEEE 1800-2017 6.20.1): " << item.first->prettyNameQ());
                return false;
            }
        }
        for (const auto& item : modInfop->typeParamIndexMap()) {
            AstNodeDType* dtypep = cellParam->m_typeParams[item.second];
            if (!dtypep || VN_IS(dtypep, VoidDType)) dtypep = item.first->subDTypep();
            if (!dtypep || VN_IS(dtypep, VoidDType)) {
                m_cellNodep->v3error("Missing type parameter: " << item.first->prettyNameQ());
                return false;
            }
        }
        // Check interface connection
        checkIfacePinConnection(pinsp);
        return true;
    }
    //! Find specialized module with given overridden parameters and interface pin, if not exists,
    //! clone a new one.
    AstNodeModule* findOrCloneDeparamedMod(AstNodeModule* modp, AstPin* paramsp, AstPin* pinsp) {
        BaseModInfo* baseModInfop = modp->user5u().to<BaseModInfo*>();
        UASSERT_OBJ(!baseModInfop->isDeparamed(), modp, "Should use original node");
        ModInfo* modInfop = static_cast<ModInfo*>(baseModInfop);

        std::unique_ptr<ModParamSet> overriddenParams;
        overriddenParams.reset(collectOverriddenParamSet(modInfop, paramsp, pinsp));
        AstNodeModule* foundp = modInfop->findNodeWithOverriddenParamSet(overriddenParams.get());
        if (foundp) {
            UINFO(7, "Overridden param set found in modinfo\n");
            return foundp;
        }

        const bool checkOk = checkCellParamSet(modInfop, overriddenParams.get(), pinsp);
        if (!checkOk) return nullptr;

        auto fullParams = std::make_unique<ModParamSet>(*overriddenParams);
        // Collect constants from original module for not overridden parameters, so potentially
        // don't need to clone a new module and evaluate them
        bool hasEmptyParam = false;
        for (const auto& item : modInfop->paramIndexMap()) {
            if (!fullParams->m_params[item.second]) {  // not overridden
                if (!item.first->valuep()) {  // skip parameter with no value
                } else if (AstConst* const constp = VN_CAST(item.first->valuep(), Const)) {
                    fullParams->m_params[item.second] = constp;
                } else {
                    hasEmptyParam = true;
                }
            }
        }
        for (const auto& item : modInfop->typeParamIndexMap()) {
            if (!fullParams->m_typeParams[item.second]) {  // not overridden
                if (!item.first->childDTypep()) {  // skip parameter with no value
                } else {
                    // We are not sure if item.first->childDTypep() is constant (e.g. has
                    // non-constant range), so just mark it currently
                    hasEmptyParam = true;
                }
            }
        }
        AstNodeModule* clonedModp = nullptr;
        if (hasEmptyParam) {
            // If still has unknown parameters, evaluate them before finding in the fullParamSet
            UINFO(7, "  Evaluating unoverridden params in cloned module\n");
            clonedModp = evaluateModParams(modp, modInfop, fullParams.get());
        }
        // Find in the fullParamSet
        fullParams->rehash();
        foundp = modInfop->findNodeWithFullParamSet(fullParams.get());
        overriddenParams->skipTypesRef();
        if (foundp) {
            UINFO(7, "  Full param set found in modinfo\n");
            modInfop->insertOverriddenParamSet(overriddenParams.release(), foundp);
            // A specialized module with the same param set is already exist. The cloned one is not
            // necessary anymore
            if (clonedModp) VL_DO_DANGLING(m_deleter.pushDeletep(clonedModp), clonedModp);
            return foundp;
        }
        // Clone a new one if we didn't do it
        if (!clonedModp) clonedModp = deepCloneModule(modp, modInfop, fullParams.get());
        DeparamedModInfo* deparamedModInfo = new DeparamedModInfo;
        m_allocatedModInfo.push_back(deparamedModInfo);
        clonedModp->user5p(deparamedModInfo);
        deparamedModInfo->setPinMap(std::move(m_clonedModPinMap));
        if (!updateClonedModInfo(modInfop, clonedModp)) return nullptr;
        fullParams->skipTypesRef();
        modInfop->insertOverriddenParamSet(overriddenParams.release(), clonedModp);
        modInfop->insertFullParamSet(fullParams.release(), clonedModp);
        // Keep tree sorted by level. Note: Different parameterizations of the same recursive
        // module end up with the same level, which we will need to fix up at the end, as we do not
        // know up front how recursive modules are expanded, and a later expansion might re-use an
        // earlier expansion (see t_recursive_module_bug_2).
        AstNode* insertp = modp;
        while (VN_IS(insertp->nextp(), NodeModule)
               && VN_AS(insertp->nextp(), NodeModule)->level() <= clonedModp->level()) {
            insertp = insertp->nextp();
        }
        insertp->addNextHere(clonedModp);
        return clonedModp;
    }

    bool nodeDeparamCommon(AstNodeModule*& srcModpr, AstPin* paramsp, AstPin* pinsp) {
        // Make sure constification worked
        // Must be a separate loop, as constant conversion may have changed some pointers.
        UINFO(6, "Deparam: processing  " << m_cellNodep << endl);
        UINFO(6, "         src module: " << srcModpr << endl);
        probeModule(srcModpr);
        if (!BaseModInfo::isParameterizable(srcModpr->user5p())) {  // Not parameterizable
            checkIfacePinConnection(pinsp);
            UINFO(6, "  skip not parameterizable module" << endl);
            return false;
        }
        if (srcModpr->user5u().to<BaseModInfo*>()->isDeparamed()) {
            // After processing, some ClassRefs can be copied and assigned to new module, and then
            // be revisited, so just skip them.
            UINFO(6, "  skip already processed cell" << endl);
            return false;
        }
        AstNodeModule* newModp = findOrCloneDeparamedMod(srcModpr, paramsp, pinsp);
        if (!newModp) {
            UINFO(6, "  deparam failed" << endl);
            VL_DO_DANGLING(m_cellNodep->unlinkFrBack()->deleteTree(), m_cellNodep);
            return false;
        }
        newModp->dead(false);
        relinkPins(newModp->user5u().to<DeparamedModInfo*>(), pinsp);
        // Delete the parameters from the cell; they're not relevant any longer.
        if (paramsp) m_deleter.pushDeletep(paramsp->unlinkFrBackWithNext());
        srcModpr = newModp;
        UINFO(6, "  new module for cell: " << newModp << endl);
        return true;
    }

    void cellDeparam(AstCell* nodep, AstNodeModule*& srcModpr) {
        if (nodeDeparamCommon(srcModpr, nodep->paramsp(), nodep->pinsp())) {
            nodep->modp(srcModpr);
            nodep->modName(srcModpr->name());
        }
        nodep->recursive(false);
    }

    void classRefDeparam(AstClassOrPackageRef* nodep, AstNodeModule*& srcModpr) {
        if (nodeDeparamCommon(srcModpr, nodep->paramsp(), nullptr))
            nodep->classOrPackagep(srcModpr);
    }

    void classRefDeparam(AstClassRefDType* nodep, AstNodeModule*& srcModpr) {
        if (nodeDeparamCommon(srcModpr, nodep->paramsp(), nullptr)) {
            AstClass* const classp = VN_AS(srcModpr, Class);
            nodep->classp(classp);
            nodep->classOrPackagep(classp);
        }
    }

    void loadParameterizedHierBlocks(const V3HierBlockOptSet& hierOpts, AstNetlist* nodep) {
        std::unordered_set<string> hierOrigModNames;  // set of origName
        std::unordered_map<string, AstNodeModule*> hierModMap;  // modName -> node
        std::multimap<string, string> hierModNameList;  // origName -> list[mangledName]
        for (const auto& hierOpt : hierOpts) {
            const string& origName = hierOpt.second.origName();
            const string& mangledName = hierOpt.second.mangledName();
            if (mangledName != v3Global.opt.topModule()) {
                hierOrigModNames.insert(origName);
                hierModMap[origName] = nullptr;
                hierModMap[mangledName] = nullptr;
                hierModNameList.insert({origName, mangledName});
            }
        }
        if (!hierModNameList.empty()) {
            for (auto* modp = nodep->modulesp(); modp; modp = VN_AS(modp->nextp(), NodeModule)) {
                if (hierModMap.find(modp->prettyName()) != hierModMap.end())
                    hierModMap[modp->prettyName()] = modp;
            }
        }
        for (const string& modName : hierOrigModNames) {
            AstNodeModule* const origModp = hierModMap[modName];
            UASSERT(origModp, "Can not find original module for " << modName << endl);
            probeModule(origModp);
            ModInfo* modInfo = origModp->user5u().to<ModInfo*>();
            if (!BaseModInfo::isParameterizable(modInfo)) continue;
            std::unordered_map<string, AstNode*> origModPinMap;
            for (AstNode* stmtp = origModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                    if (varp->isIO() || varp->isIfaceRef()) origModPinMap[varp->name()] = varp;
                }
            }
            const auto hierModRange = hierModNameList.equal_range(modName);
            for (auto it = hierModRange.first; it != hierModRange.second; ++it) {
                const V3HierarchicalBlockOption* hierOpt = &hierOpts.find(it->second)->second;
                AstNodeModule* const paramModp = hierModMap[it->second];
                UASSERT(paramModp, "Can not find hierarchical block for " << it->second << endl);
                std::unordered_map<string, AstConst*> paramMap;
                for (auto paramItem : hierOpt->params()) {
                    AstConst* constp{AstConst::parseParamLiteral(
                        new FileLine{FileLine::builtInFilename()}, paramItem.second)};
                    UASSERT(constp, paramItem.second << " is not a valid parameter literal");
                    m_deleter.pushDeletep(constp);
                    paramMap[paramItem.first] = constp;
                }
                auto& paramIndexMap = modInfo->paramIndexMap();
                std::vector<AstNodeExpr*> paramsList{paramIndexMap.size(), nullptr};
                for (const auto& indexMapItem : paramIndexMap) {
                    const AstVar* const varp = indexMapItem.first;
                    if (!varp->isParam()) continue;
                    auto paramMapIt = paramMap.find(varp->name());
                    if (paramMapIt == paramMap.end()) continue;
                    paramsList[indexMapItem.second] = paramMapIt->second;
                    paramMap.erase(paramMapIt);
                }
                for (const auto& paramMapItem : paramMap) {
                    v3error("Unknown parameter for hierarchical block: " << paramMapItem.first);
                }
                // Add pin mapping
                m_clonedModPinMap.clear();
                for (AstNode* stmtp = paramModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                    if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                        if (varp->isIO() || varp->isIfaceRef()) {
                            AstNode* const origPin = origModPinMap[varp->name()];
                            UASSERT_OBJ(origPin, varp, "Failed to map pin to original module");
                            m_clonedModPinMap[origPin] = varp;
                        }
                    }
                }
                DeparamedModInfo* deparamedModInfo = new DeparamedModInfo;
                m_allocatedModInfo.push_back(deparamedModInfo);
                paramModp->user5p(deparamedModInfo);
                deparamedModInfo->setPinMap(std::move(m_clonedModPinMap));
                auto* paramSetp = new ModParamSet;
                paramSetp->m_params = std::move(paramsList);
                paramSetp->rehash();
                modInfo->insertFullParamSet(paramSetp, paramModp);
            }
        }
    }

public:
    void dumpSelf(const string& filename) {
        const std::unique_ptr<std::ofstream> logp{V3File::new_ofstream(filename)};
        if (logp->fail()) v3fatal("Can't write " << filename);
        std::ostream& os = *logp;
        for (const BaseModInfo* const item : m_allocatedModInfo) {
            if (item->isDeparamed()) continue;
            const ModInfo* const modInfo = static_cast<const ModInfo*>(item);
            modInfo->dumpSelf(os);
            os << endl << endl;
        }
    }

    void nodeDeparam(AstNode* nodep, AstNodeModule*& srcModpr, AstNodeModule* modp,
                     const string& someInstanceName) {
        m_modp = modp;
        m_cellNodep = nodep;
        // Cell: Check for parameters in the instantiation.
        // We always run this, even if no parameters, as need to look for interfaces.
        if (debug() >= 10) nodep->dumpTree("-  cell: ");
        // Evaluate all module constants
        V3Const::constifyParamsEdit(nodep);
        srcModpr->someInstanceName(someInstanceName + "." + nodep->name());

        if (auto* cellp = VN_CAST(nodep, Cell)) {
            cellDeparam(cellp, srcModpr);
        } else if (auto* classRefp = VN_CAST(nodep, ClassRefDType)) {
            classRefDeparam(classRefp, srcModpr);
        } else if (auto* classPkgRefp = VN_CAST(nodep, ClassOrPackageRef)) {
            classRefDeparam(classPkgRefp, srcModpr);
        } else {
            nodep->v3fatalSrc("Expected module parameterization");
        }
        // if (debug() >= 10)
        // v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("param-out.tree"));
        m_modp = nullptr;
        m_cellNodep = nullptr;
    }

    // CONSTRUCTORS
    explicit ParamProcessor(AstNetlist* nodep) {
        if (v3Global.opt.hierChild()) {
            loadParameterizedHierBlocks(v3Global.opt.hierBlocks(), nodep);
        }
        // for (AstNodeModule* modp = nodep->modulesp(); modp;
        //      modp = VN_AS(modp->nextp(), NodeModule)) {
        //     m_allModuleNames.insert(modp->name());
        // }
    }
    ~ParamProcessor() {
        for (BaseModInfo* const modInfo : m_allocatedModInfo) {
            VL_DO_DANGLING(modInfo->destroy(), modInfo);
        }
    };
    VL_UNCOPYABLE(ParamProcessor);
};

//######################################################################
// Process parameter visitor

class ParamVisitor final : public VNVisitor {
    // NODE STATE
    // AstNodeModule::user1 -> bool: already fixed level (temporary)

    // STATE
    ParamProcessor m_processor;  // De-parameterize a cell, build modules
    UnrollStateful m_unroller;  // Loop unroller

    bool m_iterateModule = false;  // Iterating module body
    string m_generateHierName;  // Generate portion of hierarchy name
    string m_unlinkedTxt;  // Text for AstUnlinkedRef
    AstNodeModule* m_modp;  // Module iterating
    std::vector<AstDot*> m_dots;  // Dot references to process
    std::multimap<bool, AstNode*> m_cellps;  // Cells left to process (in current module)
    std::multimap<int, AstNodeModule*> m_workQueue;  // Modules left to process
    std::vector<AstClass*> m_paramClasses;  // Parameterized classes

    // Map from AstNodeModule to set of all AstNodeModules that instantiates it.
    std::unordered_map<AstNodeModule*, std::unordered_set<AstNodeModule*>> m_parentps;

    // METHODS

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
            void* const user5p = modp->user5p();
            if (!BaseModInfo::isVisited(user5p)) {
                modp->user5p(BaseModInfo::setVisited(user5p));
                // TODO: this really should be an assert, but classes and hier_blocks are
                // special...
                if (modp->someInstanceName().empty()) modp->someInstanceName(modp->origName());

                // Iterate the body
                {
                    VL_RESTORER(m_modp);
                    m_modp = modp;
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
                if (const auto* modCellp = VN_CAST(cellp, Cell)) {
                    srcModp = modCellp->modp();
                } else if (const auto* classRefp = VN_CAST(cellp, ClassOrPackageRef)) {
                    const AstNode* const clsOrPkgNodep = classRefp->classOrPackageNodep();
                    if (VN_IS(clsOrPkgNodep, Typedef) || VN_IS(clsOrPkgNodep, ParamTypeDType))
                        continue;
                    srcModp = classRefp->classOrPackagep();
                } else if (const auto* classRefp = VN_CAST(cellp, ClassRefDType)) {
                    srcModp = classRefp->classp();
                } else {
                    cellp->v3fatalSrc("Expected module parameterization");
                }
                UASSERT_OBJ(srcModp, cellp, "Unlinked class ref");

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

    // RHSs of AstDots need a relink when LHS is a parameterized class reference
    void relinkDots() {
        for (AstDot* const dotp : m_dots) {
            const AstClassOrPackageRef* const classRefp = VN_AS(dotp->lhsp(), ClassOrPackageRef);
            const AstClass* const lhsClassp = VN_AS(classRefp->classOrPackageNodep(), Class);
            AstClassOrPackageRef* const rhsp = VN_AS(dotp->rhsp(), ClassOrPackageRef);
            for (auto* itemp = lhsClassp->membersp(); itemp; itemp = itemp->nextp()) {
                if (itemp->name() == rhsp->name()) {
                    rhsp->classOrPackageNodep(itemp);
                    break;
                }
            }
        }
    }

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        // if (nodep->recursiveClone()) nodep->dead(true);  // Fake, made for recursive elimination
        if (nodep->dead()) return;  // Marked by LinkDot (and above)
        if (AstClass* const classp = VN_CAST(nodep, Class)) {
            if (classp->hasGParam()) {
                // Don't enter into a definition.
                // If a class is used, it will be visited through a reference
                m_paramClasses.push_back(classp);  // TODO: remove it in V3Dead?
                return;
            }
        }

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

    void visit(AstCell* nodep) override {
        visitCellOrClassRef(nodep, VN_IS(nodep->modp(), Iface));
    }
    void visit(AstClassRefDType* nodep) override { visitCellOrClassRef(nodep, false); }
    void visit(AstClassOrPackageRef* nodep) override { visitCellOrClassRef(nodep, false); }

    // Make sure all parameters are constantified
    void visit(AstVar* nodep) override {
        if (nodep->user5SetOnce()) return;  // Process once
        iterateChildren(nodep);
        if (nodep->isParam()) {
            if (!nodep->valuep() && !VN_IS(m_modp, Class)) {
                nodep->v3error("Parameter without initial value is never given value"
                               << " (IEEE 1800-2017 6.20.1): " << nodep->prettyNameQ());
            } else {
                V3Const::constifyParamsEdit(nodep);  // The variable, not just the var->valuep()
            }
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
    void visit(AstVarXRef* nodep) override {
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

    void visit(AstDot* nodep) override {
        iterate(nodep->lhsp());
        // Check if it is a reference to a field of a parameterized class.
        // If so, the RHS should be updated, when the LHS is replaced
        // by a class with actual parameter values.
        const AstClass* lhsClassp = nullptr;
        const AstClassOrPackageRef* const classRefp = VN_CAST(nodep->lhsp(), ClassOrPackageRef);
        if (classRefp) lhsClassp = VN_CAST(classRefp->classOrPackageNodep(), Class);
        AstNode* rhsDefp = nullptr;
        AstClassOrPackageRef* const rhsp = VN_CAST(nodep->rhsp(), ClassOrPackageRef);
        if (rhsp) rhsDefp = rhsp->classOrPackageNodep();
        if (lhsClassp && rhsDefp) {
            m_dots.push_back(nodep);
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
    void visit(AstGenIf* nodep) override {
        UINFO(9, "  GENIF " << nodep << endl);
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

    //! Parameter substitution for generated for loops.
    //! @todo Unlike generated IF, we don't have to worry about short-circuiting the conditional
    //!       expression, since this is currently restricted to simple comparisons. If we ever do
    //!       move to more generic constant expressions, such code will be needed here.
    void visit(AstBegin* nodep) override {
        if (AstGenFor* const forp = VN_AS(nodep->genforp(), GenFor)) {
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
    void visit(AstGenFor* nodep) override {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc("GENFOR should have been wrapped in BEGIN");
    }
    void visit(AstGenCase* nodep) override {
        UINFO(9, "  GENCASE " << nodep << endl);
        bool hit = false;
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
                        V3Number match{nodep, 1};
                        match.opEq(ccondp->num(), exprp->num());
                        if (!hit && match.isNeqZero()) {
                            hit = true;
                            keepp = itemp->stmtsp();
                        }
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
                if (!hit) {
                    hit = true;
                    keepp = itemp->stmtsp();
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
    explicit ParamVisitor(AstNetlist* netlistp)
        : m_processor{netlistp} {
        // Relies on modules already being in top-down-order
        iterate(netlistp);

        relinkDots();

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
            for (AstNodeModule* const modp : modps) netlistp->addModulesp(modp);

            for (AstClass* const classp : m_paramClasses) {
                if (!classp->user5p()) {
                    VL_DO_DANGLING(pushDeletep(classp->unlinkFrBack()), classp);
                }
            }
        }

        if (dumpLevel() >= 4) {
            m_processor.dumpSelf(v3Global.debugFilename("parameterization_report") + ".txt");
        }
    }
    ~ParamVisitor() override = default;
    VL_UNCOPYABLE(ParamVisitor);
};

//######################################################################
// Param class functions

void V3Param::param(AstNetlist* rootp) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { ParamVisitor{rootp}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("param", 0, dumpTreeLevel() >= 6);
}
