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
//      For each cell:
//          If parameterized,
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

// #define DEBUG_DONT_REMOVE_MODS

//######################################################################
// Descriptions

struct ModParamSet final {
    struct Hash {
        size_t operator()(const ModParamSet* p) const noexcept { return p->m_hashValue; }
    };
    struct Compare {
        bool operator()(const ModParamSet* x, const ModParamSet* y) const {
#if VL_DEBUG
            UASSERT(x->m_params.size() == y->m_params.size(), "vector size mismatch");
            UASSERT(x->m_ifaces.size() == y->m_ifaces.size(), "vector size mismatch");
#endif
            const size_t paramCount = x->m_params.size();
            for (size_t i = 0; i < paramCount; i++) {
                const AstNode *const xp = x->m_params[i], *const yp = y->m_params[i];
                if (!xp && !yp) continue;  // both null
                if (!xp || !yp) return false;  // null vs. non-null
                if (const auto* const xConstp = VN_CAST(xp, Const)) {
                    const AstConst* yConstp = VN_CAST(yp, Const);
                    if (!yConstp) return false;
                    if (!xConstp->num().isCaseEq(yConstp->num())) return false;
                } else if (const auto* const xTypeParamp = VN_CAST(xp, NodeDType)) {
                    const AstNodeDType* yTypeParamp = VN_CAST(yp, NodeDType);
                    if (!yTypeParamp) return false;
                    if (!xTypeParamp->similarDType(yTypeParamp)) return false;
                } else {
                    if (!xp->sameTree(yp)) return false;
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
    // Items are Const/InitArray/NodeDType
    std::vector<AstNode*> m_params;
    std::vector<AstNodeModule*> m_ifaces;

    ModParamSet() = default;

    void skipTypesRef() {
        for (auto& item : m_params)
            if (auto* const dtypep = VN_CAST(item, NodeDType)) item = dtypep->skipRefToEnump();
    }
    void rehash() {
        V3Hash hash;
        for (AstNode* const nodep : m_params) {
            if (const auto* const constp = VN_CAST(nodep, Const)) {
                hash += constp->num().toHash();  // TODO: hash constp
                continue;
            }
            AstNode* hashNodep = nodep;
            if (const auto* const typeParamp = VN_CAST(nodep, NodeDType))
                hashNodep = typeParamp->skipRefToEnump();
            hash += hashNodep ? V3Hasher::uncachedHash(hashNodep) : V3Hash();
        }
        for (AstNodeModule* const iface : m_ifaces) { hash += reinterpret_cast<size_t>(iface); }
        m_hashValue = static_cast<size_t>(hash.value());
    }
};

class BaseModInfo VL_NOT_FINAL {
public:
    enum ModType : int {
        ORIGINAL_MOD,
        DEPARAMED_MOD,
    };

protected:
    ModType m_type;
    bool m_hierBlock = false;  // hier block's top wrapper drops the hierBlock flag for modules,
                               // so need this extra field
    bool m_visited = false;
    BaseModInfo(ModType type)
        : m_type(type) {}

public:
    void destroy();
    static bool isParameterized(const void* userp) {
        return userp >= reinterpret_cast<const void*>(0x10);
    }
    static bool isVisited(const void* userp) {
        if (userp == reinterpret_cast<const void*>(0x2)) {
            // Not a parameterized module, visited
            return true;
        } else if (isParameterized(userp)) {
            return static_cast<const BaseModInfo*>(userp)->visited();
        } else {
            return false;
        }
    }
    static void* setVisited(void* userp) {
        if (!isParameterized(userp)) {
            return reinterpret_cast<void*>(0x2);  // Not a parameterized module, visited
        } else {
            static_cast<BaseModInfo*>(userp)->visited(true);
            return userp;
        }
    }
    bool isDeparamed() const {
        switch (m_type) {
        case DEPARAMED_MOD: return true;
        case ORIGINAL_MOD: return false;
        default: v3fatalSrc("bad case"); return false;
        }
    }
    bool hierBlock() const { return m_hierBlock; }
    void hierBlock(bool flag) { m_hierBlock = flag; }
    bool visited() const { return m_visited; }
    void visited(bool flag) { m_visited = flag; }
};

class ModInfo final : public BaseModInfo {
    struct ParamMap : std::unordered_map<const ModParamSet*, AstNodeModule*, ModParamSet::Hash,
                                         ModParamSet::Compare> {
        ~ParamMap() {
            for (auto& item : *this) delete item.first;  // delete the ModParamSet
        }
        AstNodeModule* findNode(const ModParamSet* paramSet) {
            const auto it = find(paramSet);
            return it != end() ? it->second : nullptr;
        }
        void insert(const ModParamSet* paramSet, AstNodeModule* nodep) {
            AstNodeModule** pos = &(*this)[paramSet];
            if (*pos) delete paramSet;
            *pos = nodep;
        }
    };
    /// Keep the original modules tracked, so we can delete them after everything is done
    AstNodeModule* const m_origModp;
    /// List of AstVar/AstParamTypeDType for parameters
    const std::vector<const AstNode*> m_paramList;
    /// List of parameterized interface ports
    const std::vector<const AstVar*> m_ifaceList;
    std::map<const AstNode*, int> m_paramIndexMap;
    std::map<const AstVar*, int> m_ifaceIndexMap;
    /// Map param sets to specialized instances
    ParamMap m_paramsMap;
    std::vector<std::pair<const ModParamSet*, AstNodeModule*>> m_paramModList;

public:
    ModInfo(AstNodeModule* origModp, std::vector<const AstNode*>&& paramList,
            std::vector<const AstVar*>&& ifaceList)
        : BaseModInfo(BaseModInfo::ORIGINAL_MOD)
        , m_origModp(origModp)
        , m_paramList(std::move(paramList))
        , m_ifaceList(std::move(ifaceList)) {
        for (size_t i = 0; i < m_paramList.size(); i++) m_paramIndexMap[m_paramList[i]] = i;
        for (size_t i = 0; i < m_ifaceList.size(); i++) m_ifaceIndexMap[m_ifaceList[i]] = i;
    }
    ~ModInfo() {
        if (!m_origModp->recursive())
            m_origModp->dead(true);  // Unused modules/ifaces are removed in V3Dead
        if (VN_IS(m_origModp, Class))
            VL_DO_DANGLING(m_origModp->unlinkFrBack()->deleteTree(), m_origModp);
    }
    const auto& paramList() const { return m_paramList; }
    const AstNode* paramListAt(size_t index) const { return m_paramList[index]; }
    const auto& paramIndexMap() const { return m_paramIndexMap; }
    const auto& ifaceIndexMap() const { return m_ifaceIndexMap; }
    void addParamedMod(const ModParamSet* paramSet, AstNodeModule* nodep) {
        m_paramModList.push_back({paramSet, nodep});
    }
    void insertParamedModMap(const ModParamSet* paramSet, AstNodeModule* nodep) {
        m_paramsMap.insert(paramSet, nodep);
    }
    AstNodeModule* findParamedNode(const ModParamSet* paramSet) {
        return m_paramsMap.findNode(paramSet);
    }
    size_t nextParamModIndex() const { return m_paramModList.size() + 1; }
    AstNodeModule* originalModp() const { return m_origModp; }
    void dumpSelf(std::ostream& os) const {
        const char* const hierBlk = hierBlock() ? "  [HIERBLK]" : "";
        os << m_origModp->prettyTypeName() << hierBlk << " (" << m_origModp << ")\n";
        for (const auto& item : m_paramsMap) {
            os << "- Instance " << item.second->prettyNameQ() << ": " << item.second << "\n";
            os << "    Hash: " << ModParamSet::Hash()(item.first) << "\n";
            const ModParamSet* const paramSet = item.first;
            for (size_t i = 0; i < m_paramList.size(); i++) {
                string str;
                V3Hash hash;
                AstNode* const nodep = paramSet->m_params[i];
                if (AstConst* const constp = VN_CAST(nodep, Const)) {
                    str = constp->num().ascii();
                    hash = constp->num().toHash();
                } else if (AstInitArray* const initArrp = VN_CAST(nodep, InitArray)) {
                    str = "InitArray[" + std::to_string(initArrp->map().size()) + "]";
                    hash = V3Hasher::uncachedHash(initArrp);
                } else if (AstNodeDType* const dtypep = VN_CAST(nodep, NodeDType)) {
                    str = dtypep->prettyDTypeName() + " (" + cvtToStr(dtypep) + ")";
                    AstNode* hashNodep = nodep;
                    if (const auto* const typeParamp = VN_CAST(nodep, NodeDType))
                        hashNodep = typeParamp->skipRefToEnump();
                    hash = hashNodep ? V3Hasher::uncachedHash(hashNodep) : V3Hash();
                }
                os << "    Parameter " << i << ": " << m_paramList[i]->name() << " -> "
                   << (str.empty() ? "(none)" : str) << ", hash=" << hash.value() << "\n";
            }
            for (size_t i = 0; i < m_ifaceList.size(); i++) {
                os << "    Interface " << i << ": " << m_ifaceList[i]->name() << " -> ";
                if (const AstNodeModule* const modp = paramSet->m_ifaces[i])
                    os << modp;
                else
                    os << "(none)";
                os << "\n";
            }
            os << endl;
        }
    }
};

class DeparamedModInfo final : public BaseModInfo {
    /// Maps pins in original module to pins in cloned module, used to relink pins/params after
    /// cloning.  Contains nodes for ports/parameters/localparams
    std::map<const AstNode*, AstNode*> m_pinMap;

public:
    DeparamedModInfo()
        : BaseModInfo(ModInfo::DEPARAMED_MOD) {}
    void setPinMap(std::map<const AstNode*, AstNode*>&& pinMap) { m_pinMap = std::move(pinMap); }
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
    //   AstNodeModule::user5p() // BaseModInfo* 0x1: Not a parameterized module, nor visited
    //                                           0x2: Not a parameterized module, visited
    //                                           0x3: Module probing. Used to detect circular
    //                                               reference
    //                                           Other non-null values: BaseModInfo for
    //                                               parameterized modules
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
    std::unordered_set<string> m_allModuleNames;  // Module name list to avoid name collision. Only
                                                  // for --hierarchical runs

    // STATIC METHODS
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
    static AstConst* convertToStringp(AstNodeExpr* nodep) {
        AstConst* const constp = VN_CAST(nodep, Const);
        // Check if it wasn't already converted
        if (constp && !constp->num().isString()) {
            return new AstConst{constp->fileline(), AstConst::String{}, constp->num().toString()};
        }
        return nullptr;
    }
    static AstNodeExpr* replaceWithStringp(AstNodeExpr* nodep) {
        // Should be called on values of parameters of type string to convert them to properly
        // typed string constants. Has no effect if the value is not a string constant.
        if (AstConst* const newConstp = convertToStringp(nodep)) {
            nodep->replaceWith(newConstp);
            nodep->deleteTree();
            return newConstp;
        }
        return nodep;
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

    // METHODS

    //! Check if the module/class is parameterized (has parameter, or for modules, has interface
    //! port that can be parameterized), and collect the parameters and parameterized interface
    //! ports for further uses.  Not for cloned modules.
    void probeModule(AstNodeModule* modp) {
        if (modp->user5p()) return;  // Already processed
        modp->user5p(reinterpret_cast<void*>(0x3));  // Avoid circular reference
        // Collect all parameters and parameterized interface ports inside source module
        std::vector<const AstNode*> paramList;
        std::vector<const AstVar*> ifaceList;
        for (auto* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (const AstVar* const varp = VN_CAST(stmtp, Var)) {
                if (varp->isGParam()) {
                    paramList.push_back(varp);
                } else if (varp->isIfaceRef()) {
                    AstIface* const ifacep = getIfaceFromVar(varp);
                    probeModule(ifacep);
                    BaseModInfo* ifaceModInfop = ifacep->user5u().to<BaseModInfo*>();
                    if (ifaceModInfop == reinterpret_cast<BaseModInfo*>(0x3)) {
                        m_cellNodep->v3warn(E_UNSUPPORTED,
                                            "Circular reference on interface ports");
                    } else if (BaseModInfo::isParameterized(ifaceModInfop)) {
                        ifaceList.push_back(varp);
                    }
                }
            } else if (AstParamTypeDType* const dtypep = VN_CAST(stmtp, ParamTypeDType)) {
                if (dtypep->isGParam()) paramList.push_back(dtypep);
            }
        }
        UINFO(6, "  probeModule: " << modp << endl);
        UINFO(6, "    collected: " << paramList.size() << " params, " << ifaceList.size()
                                   << " param ifaces" << endl);
        const bool hasGParam = !paramList.empty();
        const bool isParameterized = hasGParam || !ifaceList.empty();
        UASSERT(hasGParam == modp->hasGParam(), "modp->hasGParam() is not consistent");
        ModInfo* modInfop;
        if (isParameterized) {
            modInfop = new ModInfo(modp, std::move(paramList), std::move(ifaceList));
            modInfop->hierBlock(modp->hierBlock());
            m_allocatedModInfo.push_back(modInfop);
        } else {
            // 0x1: Not a parameterized module, nor visited
            modInfop = reinterpret_cast<ModInfo*>(0x1);
        }
        modp->user5p(modInfop);
    }
    template <typename T_KEY, typename T_MAP, typename T_LIST, typename T_VAL>
    void insertOverriddenParamSet(T_KEY* key, const std::map<const T_MAP*, int>& paramIndexMap,
                                  std::vector<T_LIST*>& paramList, T_VAL* paramVal,
                                  const AstPin* errp) {
        const auto it = paramIndexMap.find(key);
        UASSERT_OBJ(it != paramIndexMap.end(), errp, "Invalid pin connection");
        int index = it->second;
        UASSERT_OBJ(index < static_cast<int>(paramList.size()), errp, "Pin list corrupted");
        paramList[index] = paramVal;
    }
    //! Collect overridden parameters and interfaces from Cell/ClassRef
    ModParamSet* collectOverriddenParamSet(const ModInfo* modInfop, const AstPin* paramsp,
                                           const AstPin* pinsp) {
        auto& paramIndexMap = modInfop->paramIndexMap();
        auto& ifaceIndexMap = modInfop->ifaceIndexMap();
        std::vector<AstNode*> params{paramIndexMap.size(), nullptr};
        std::vector<AstNodeModule*> ifaces{ifaceIndexMap.size(), nullptr};
        for (auto* pinp = paramsp; pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            if (!pinp->exprp()) continue;
            if (AstVar* const modVarp = pinp->modVarp()) {
                if (!modVarp->isGParam()) continue;
                AstNodeExpr* exprp = VN_CAST(pinp->exprp(), NodeExpr);
                bool hierBlockSupported = false;
                if (!exprp) continue;
                if (!VN_IS(exprp, InitArray)) exprp = V3Const::constifyParamsEdit(exprp);
                if (AstConst* constp = VN_CAST(exprp, Const)) {
                    // Some constants not under AstVar are not converted to string automatically,
                    // so we need to convert them here.
                    if (isString(modVarp->subDTypep())) exprp = replaceWithStringp(constp);
                    hierBlockSupported = !constp->isOpaque();
                } else if (VN_IS(exprp, InitArray) && arraySubDTypep(modVarp->subDTypep())) {
                    // Array assigned to array
                } else {
                    pinp->v3error("Can't convert parameter value to constant: Param "
                                  << pinp->prettyNameQ() << " of " << m_cellNodep->prettyNameQ());
                    continue;
                }
                if (modInfop->hierBlock() && !hierBlockSupported) {
                    pinp->v3error(modInfop->originalModp()->prettyNameQ()
                                  << " has hier_block metacomment, hierarchical Verilation"
                                  << " supports only integer/floating point/string parameters");
                }
                insertOverriddenParamSet(modVarp, paramIndexMap, params, exprp, pinp);
            } else if (AstParamTypeDType* const paramDTypep = pinp->modPTypep()) {
                if (modInfop->hierBlock()) {
                    pinp->v3error(
                        modInfop->originalModp()->prettyNameQ()
                        << " has hier_block metacomment, but 'parameter type' is not supported");
                }
                AstNodeDType* dtypep = VN_CAST(pinp->exprp(), NodeDType);
                insertOverriddenParamSet(paramDTypep, paramIndexMap, params, dtypep, pinp);
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
                if (!BaseModInfo::isParameterized(ifacep->user5p())) continue;
                insertOverriddenParamSet(modVarp, ifaceIndexMap, ifaces, ifacep, pinp);
            }
        }
        auto* paramSetp = new ModParamSet;
        paramSetp->m_params = std::move(params);
        paramSetp->m_ifaces = std::move(ifaces);
        paramSetp->rehash();
        return paramSetp;
    }
    //! Deep clone original module, assign parameters to it, and check if they're valid.
    //! Note all module internal variables will be re-linked to the new modules by clone. However,
    //! links outside the module (like on the upper cells) will not.
    AstNodeModule* deepCloneModule(AstNodeModule* srcModp, ModInfo* modInfop,
                                   ModParamSet* paramsp) {
        // Clone parameters before cloning srcModp, so it won't make clonep inaccessible
        std::vector<AstNode*> paramCopies{paramsp->m_params};
        for (AstNode*& paramp : paramCopies)
            if (paramp) paramp = paramp->cloneTree(false);

        // Deep clone the module
        AstNodeModule* const newModp = srcModp->cloneTree(false);
        static size_t s_cloneSeqNum = 0;
        newModp->name(newModp->name() + "__tmpcloned" + std::to_string(s_cloneSeqNum++));
        UINFO(6, "  clone module: " << srcModp << endl);
        UINFO(6, "        result: " << newModp << endl);

        if (AstClass* const newClassp = VN_CAST(newModp, Class)) {
            replaceRefsRecurse(newModp->stmtsp(), newClassp, VN_AS(srcModp, Class));
        }
        // Assign params to the cloned module
        for (size_t i = 0; i < modInfop->paramList().size(); i++) {
            const AstNode* const paramp = modInfop->paramListAt(i);
            AstNode* const valuep = paramCopies[i];
            if (!valuep) continue;  // not overridden
            if (AstVar* clonedVarp = VN_CAST(paramp->clonep(), Var)) {
                if (auto* const nodep = clonedVarp->valuep()) nodep->unlinkFrBack()->deleteTree();
                clonedVarp->valuep(valuep);
            } else if (AstParamTypeDType* const clonedTypep
                       = VN_CAST(paramp->clonep(), ParamTypeDType)) {
                if (auto* const dtypep = clonedTypep->childDTypep())
                    dtypep->unlinkFrBack()->deleteTree();
                clonedTypep->childDTypep(VN_AS(valuep, NodeDType));
            }
        }
        for (const auto& item : modInfop->ifaceIndexMap()) {
            AstIfaceRefDType* dtypep = getIfaceDtypeFromVar(item.first->clonep());
            if (AstNodeModule* const modp = paramsp->m_ifaces[item.second]) {
                dtypep->ifacep(VN_AS(modp, Iface));
            }
        }
        // Collect all parameters and I/O pins, so we can remap them for other referencing cells or
        // XRefs later.
        // Since V3Const::constifyParamsEdit used in evaluateModParams may also clone some nodes
        // and make clonep of the pins inaccessible, so we have to collect them here
        collectPins(newModp);
        return newModp;
    }
    //! Evaluate all parameters in a newly-cloned module, and collect the values
    //! @return the cloned module, with parameters propagated
    AstNodeModule* evaluateModParams(AstNodeModule* srcModp, ModInfo* modInfop,
                                     ModParamSet* paramsp) {
        UINFO(7, "  evaluating params in cloned module...\n");
        AstNodeModule* const newModp = deepCloneModule(srcModp, modInfop, paramsp);
        // Propagate constant through the parameters in the new module
        for (const AstNode* paramp : modInfop->paramList()) {
            V3Const::constifyParamsEdit(m_clonedModPinMap[paramp]);
        }
        // Collect evaluated parameters
        for (const auto& item : modInfop->paramIndexMap()) {
            AstNode* const clonep = m_clonedModPinMap[item.first];
            if (AstVar* clonedVarp = VN_CAST(clonep, Var)) {
                // clonedVarp->varType(VVarType::LPARAM);
                AstNodeExpr* exprp = VN_CAST(clonedVarp->valuep(), NodeExpr);
                if (modInfop->hierBlock()) {
                    if (AstConst* constp = VN_CAST(exprp, Const)) {
                        if (constp->isOpaque()) continue;
                    } else {
                        continue;
                    }
                }
                paramsp->m_params[item.second] = exprp;
            } else if (AstParamTypeDType* clonedDtp = VN_AS(clonep, ParamTypeDType)) {
                if (modInfop->hierBlock()) continue;
                paramsp->m_params[item.second] = clonedDtp->subDTypep();
            }
        }
        paramsp->skipTypesRef();
        paramsp->rehash();
        return newModp;
    }
    //! Grab all pins, so we can remap our pins later
    void collectPins(AstNodeModule* clonedModp) {
        m_clonedModPinMap.clear();
        for (AstNode* stmtp = clonedModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            const AstNode* origNodep = nullptr;
            if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                if (varp->isIO() || varp->isIfaceRef() || varp->isParam()) {
                    origNodep = varp->clonep();
                }
            } else if (AstParamTypeDType* const dtypep = VN_CAST(stmtp, ParamTypeDType)) {
                if (dtypep->isGParam()) origNodep = dtypep->clonep();
            }
            if (origNodep) m_clonedModPinMap[origNodep] = stmtp;
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
    bool updateClonedModInfo(ModInfo* modInfop, AstNodeModule* clonedModp, ModParamSet* paramsp) {
        AstNodeModule* const modp = modInfop->originalModp();
        string newModName;
        if (!modInfop->hierBlock()) {
            newModName = modp->name() + "__p" + std::to_string(modInfop->nextParamModIndex());
        } else {
            const uint32_t hash = static_cast<uint32_t>(ModParamSet::Hash()(paramsp));
            const string hashStr = cvtToHex(hash);
            // Don't use '__' since this module will be loaded by Verilator later
            const string hierPrefix = modp->name() + "_hierblk";
            for (int len = 4; len <= 8; len += 2) {
                const string trailName = hierPrefix + '_' + hashStr.substr(0, len);
                if (m_allModuleNames.find(trailName) != m_allModuleNames.end()) {
                    newModName = std::move(trailName);
                    break;
                }
            }
            if (newModName.empty()) {  // Use unique sequence name in case of hash collision
                newModName = hierPrefix + std::to_string(modInfop->nextParamModIndex());
            }
            m_allModuleNames.insert(newModName);
        }
        clonedModp->name(std::move(newModName));
        clonedModp->hasGParam(false);
        clonedModp->recursive(false);
        clonedModp->recursiveClone(false);
        // Recursion may need level cleanups
        if (clonedModp->level() <= m_modp->level()) clonedModp->level(m_modp->level() + 1);
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
        for (size_t i = 0; i < modInfop->paramList().size(); i++) {
            const AstNode* const paramp = modInfop->paramListAt(i);
            if (const AstVar* const varp = VN_CAST(paramp, Var)) {
                if (!varp->valuep() && !cellParam->m_params[i]
                    && VN_IS(modInfop->originalModp(), Class)) {
                    m_cellNodep->v3error(
                        "Class parameter without initial value is never given value"
                        << " (IEEE 1800-2017 6.20.1): " << varp->prettyNameQ());
                    return false;
                }
            } else if (const AstParamTypeDType* const pdtypep = VN_CAST(paramp, ParamTypeDType)) {
                AstNodeDType* dtypep = VN_CAST(cellParam->m_params[i], NodeDType);
                if (!dtypep || VN_IS(dtypep, VoidDType)) dtypep = pdtypep->subDTypep();
                if (!dtypep || VN_IS(dtypep, VoidDType)) {
                    m_cellNodep->v3error("Missing type parameter: " << pdtypep->prettyNameQ());
                    return false;
                }
            }
        }
        // Check interface connection
        checkIfacePinConnection(pinsp);
        return true;
    }
    //! Find specialized module with given overridden parameters and interface pins. If not exists,
    //! clone a new one.
    AstNodeModule* findOrCloneDeparamedMod(AstNodeModule* modp, AstPin* paramsp, AstPin* pinsp) {
        BaseModInfo* baseModInfop = modp->user5u().to<BaseModInfo*>();
        UASSERT_OBJ(!baseModInfop->isDeparamed(), modp, "Should use original node for deparam");
        ModInfo* modInfop = static_cast<ModInfo*>(baseModInfop);

        std::unique_ptr<ModParamSet> overriddenParams;
        overriddenParams.reset(collectOverriddenParamSet(modInfop, paramsp, pinsp));
        AstNodeModule* foundp = modInfop->findParamedNode(overriddenParams.get());
        if (foundp) {
            UINFO(7, "  module found with overridden param set\n");
            return foundp;
        }

        const bool checkOk = checkCellParamSet(modInfop, overriddenParams.get(), pinsp);
        if (!checkOk) return nullptr;

        auto collectedParams = std::make_unique<ModParamSet>(*overriddenParams);
        // Collect constants from original module for not overridden parameters, so potentially
        // don't need to clone a new module
        bool hasEmptyParam = false;
        for (size_t i = 0; i < modInfop->paramList().size(); i++) {
            const AstNode* const paramp = modInfop->paramListAt(i);
            if (collectedParams->m_params[i]) continue;
            if (const AstVar* const varp = VN_CAST(paramp, Var)) {
                if (!varp->valuep()) {  // skip parameter with no value
                } else if (AstConst* constp = VN_CAST(varp->valuep(), Const)) {
                    if (isString(varp->subDTypep())) {
                        constp = VN_AS(replaceWithStringp(constp), Const);
                    }
                    if (modInfop->hierBlock() && constp->isOpaque()) continue;
                    collectedParams->m_params[i] = constp;
                } else {
                    if (modInfop->hierBlock()) continue;
                    hasEmptyParam = true;
                }
            } else if (const AstParamTypeDType* const dtypep = VN_CAST(paramp, ParamTypeDType)) {
                if (modInfop->hierBlock()) continue;
                if (!dtypep->childDTypep()) {  // skip parameter with no value
                } else {
                    // We are not sure if item.first->childDTypep() is constant (e.g. has
                    // non-constant range), so just mark it currently
                    hasEmptyParam = true;
                }
            }
        }
        (void)hasEmptyParam;
        collectedParams->rehash();
        foundp = modInfop->findParamedNode(collectedParams.get());
        if (foundp) {
            UINFO(7, "  module found with collected param set\n");
            modInfop->insertParamedModMap(overriddenParams.release(), foundp);
            modInfop->insertParamedModMap(collectedParams.release(), foundp);
            return foundp;
        }
        AstNodeModule* clonedModp = nullptr;
        // Even if there's no unknown parameters, we still have to re-evaluate them under module's
        // context (to perform truncation/extension/type propagation/...)
        auto evaluatedParams = std::make_unique<ModParamSet>(*overriddenParams);
        clonedModp = evaluateModParams(modp, modInfop, evaluatedParams.get());

        foundp = modInfop->findParamedNode(evaluatedParams.get());
        if (foundp) {
            UINFO(7, "  module found with evaluated param set\n");

            // A specialized module with the same param set is already exist. The cloned one is not
            // necessary anymore
#ifdef DEBUG_DONT_REMOVE_MODS  // FIXME: todo
            // Directly remove the module seems to make some nodes in type table link broken
            if (clonedModp) {
                clonedModp->dead(true);
                modp->addNextHere(clonedModp);
            }
#else
            if (clonedModp) VL_DO_DANGLING(m_deleter.pushDeletep(clonedModp), clonedModp);
#endif

            modInfop->insertParamedModMap(overriddenParams.release(), foundp);
            modInfop->insertParamedModMap(collectedParams.release(), foundp);
            modInfop->insertParamedModMap(evaluatedParams.release(), foundp);
            return foundp;
        }

        if (v3Global.opt.hierChild() || !v3Global.opt.hierBlocks().empty()) {
            UASSERT_OBJ(!modInfop->hierBlock(), m_cellNodep,
                        "Failed to find module for hierarchical block\n");
        }
        DeparamedModInfo* deparamedModInfo = new DeparamedModInfo;
        deparamedModInfo->hierBlock(modInfop->hierBlock());
        m_allocatedModInfo.push_back(deparamedModInfo);
        clonedModp->user5p(deparamedModInfo);
        deparamedModInfo->setPinMap(std::move(m_clonedModPinMap));
        if (!updateClonedModInfo(modInfop, clonedModp, collectedParams.get())) return nullptr;
        collectedParams->skipTypesRef();
        UINFO(6, "  insert new deparamed module: " << clonedModp << endl);
        modInfop->addParamedMod(evaluatedParams.release(), clonedModp);
        modInfop->insertParamedModMap(overriddenParams.release(), clonedModp);
        modInfop->insertParamedModMap(collectedParams.release(), clonedModp);
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
        // Must be a separate loop, as constant conversion may have changed some pointers.
        UINFO(6, "Deparam: processing: " << m_cellNodep << endl);
        UINFO(6, "         src module: " << srcModpr << endl);
        probeModule(srcModpr);
        BaseModInfo* modInfo = srcModpr->user5u().to<BaseModInfo*>();
        if (!BaseModInfo::isParameterized(modInfo)) {  // Not parameterized
            checkIfacePinConnection(pinsp);
            UINFO(6, "  skip not parameterized module" << endl);
            return false;
        } else if (modInfo->isDeparamed()) {
            // After processing, some ClassRefs inside parameter pins could be copied and assigned
            // to new module, and then be revisited, so just skip them.
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
        std::unordered_set<string> hierOrigModNames;  // set[origName]
        std::unordered_map<string, AstNodeModule*> hierModMap;  // modName -> node
        std::multimap<string, string> hierModNameList;  // origName -> set[mangledName]
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
                // Recursive hierarchical module may change its name, so we have to match its
                // origName.
                const string actualName = modp->recursive() && !modp->recursiveClone()
                                              ? modp->origName()
                                              : modp->name();
                if (hierModMap.find(actualName) != hierModMap.end()) {
                    hierModMap[actualName] = modp;
                }
            }
        }
        for (const string& modName : hierOrigModNames) {
            AstNodeModule* const origModp = hierModMap[modName];
            UASSERT(origModp, "Can not find original module for " << modName << endl);
            probeModule(origModp);
            ModInfo* modInfo = origModp->user5u().to<ModInfo*>();
            if (!BaseModInfo::isParameterized(modInfo)) continue;
            modInfo->hierBlock(true);
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
                std::vector<AstNode*> paramsList{paramIndexMap.size(), nullptr};
                for (const auto& indexMapItem : paramIndexMap) {
                    if (!VN_IS(indexMapItem.first, Var)) continue;
                    const AstVar* const varp = VN_AS(indexMapItem.first, Var);
                    // if (!varp->isParam()) continue;
                    auto paramMapIt = paramMap.find(varp->name());
                    if (paramMapIt == paramMap.end()) continue;
                    if (isString(varp->subDTypep())) {
                        paramMapIt->second = convertToStringp(paramMapIt->second);
                    }
                    paramsList[indexMapItem.second] = paramMapIt->second;
                    paramMap.erase(paramMapIt);
                }
                for (const auto& paramMapItem : paramMap) {
                    v3fatalSrc("Unknown parameter for hierarchical block: " << paramMapItem.first);
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
                deparamedModInfo->hierBlock(true);
                m_allocatedModInfo.push_back(deparamedModInfo);
                paramModp->user5p(deparamedModInfo);
                deparamedModInfo->setPinMap(std::move(m_clonedModPinMap));
                auto* paramSetp = new ModParamSet;
                paramSetp->m_params = std::move(paramsList);
                paramSetp->rehash();
                modInfo->addParamedMod(paramSetp, paramModp);
                modInfo->insertParamedModMap(paramSetp, paramModp);
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
        // Cell: Check for parameters in the instantiation.
        // We always run this, even if no parameters, as need to look for interfaces.
        m_modp = modp;
        m_cellNodep = nodep;
        srcModpr->someInstanceName(someInstanceName + "." + nodep->name());
        V3Const::constifyParamsEdit(nodep);

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
        if (!v3Global.opt.hierBlocks().empty()) {
            loadParameterizedHierBlocks(v3Global.opt.hierBlocks(), nodep);
        }
        if (v3Global.opt.hierarchical()) {
            for (AstNodeModule* modp = nodep->modulesp(); modp;
                 modp = VN_AS(modp->nextp(), NodeModule)) {
                m_allModuleNames.insert(modp->name());
            }
        }
    }
    ~ParamProcessor() {
        for (BaseModInfo* const modInfo : m_allocatedModInfo) modInfo->destroy();
        m_allocatedModInfo.clear();
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

    /*************** FIXME: temporarily fix ***************/
    std::unordered_map<string, AstNodeModule*> delayModMap;
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
        if (nodep->dead()) return;  // Marked by LinkDot (and above)
        if (AstClass* const classp = VN_CAST(nodep, Class)) {
            if (classp->hasGParam()) {
                // Don't enter into a definition.
                // If a class is used, it will be visited through a reference
                m_paramClasses.push_back(classp);  // FIXME: remove it in V3Dead?
                return;
            }
        }

        if (m_iterateModule) {  // Iterating body
            UINFO(4, " MOD-under-MOD.  " << nodep << endl);
            m_workQueue.emplace(nodep->level(), nodep);  // Delay until current module is done
            return;
        }

        bool doVisit = false;
        if (nodep->level() <= 2) {  // Haven't added top yet, so level 2 is the top
            doVisit = true;
        } else if (VN_IS(nodep, Class)) {  // Nor moved classes
            doVisit = true;
        } else if (VN_IS(nodep, Package)) {  // Likewise haven't done wrapTopPackages yet
            doVisit = true;
        } else if (VN_IS(nodep, Iface) && v3Global.opt.lintOnly()) {
            // In lint-only mode the interface can be referenced by top level ports without Cells
            doVisit = true;
        }
        if (doVisit) {
            // Start traversal at root-like things
            visitCells(nodep);
        }
    }

    /*************** FIXME: temporarily fix ***************/
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
    /*************** FIXME: temporarily fix ***************/

    void visit(AstCell* nodep) override {
        /*************** FIXME: temporarily fix ***************/
        size_t pos = nodep->modp()->name().find("__Vrcm");
        if (pos != string::npos) {
            string s = nodep->modp()->name();
            s.erase(pos);
            AstNodeModule* item = delayModMap[s];
            nodep->modp(item);
            relinkPinsByName(nodep->paramsp(), item);
            relinkPinsByName(nodep->pinsp(), item);
        }
        /*************** FIXME: temporarily fix ***************/
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
        /*************** FIXME: temporarily fix ***************/
        for (AstNodeModule* modp = netlistp->modulesp(); modp;
             modp = VN_AS(modp->nextp(), NodeModule)) {
            if (modp->name() == "delay" || modp->name() == "delay_hierblk1"
                || modp->name() == "delay_hierblk2" || modp->name() == "delay_hierblk3") {
                delayModMap[modp->name()] = modp;
            }
        }
        /*************** FIXME: temporarily fix ***************/
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
