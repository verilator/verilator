// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Interface typedef capture helper.
//   Stores (refp, typedefp, cellp, owners, pendingClone) so LinkDot can
//   rebind refs when symbol lookup fails, and V3Param clones can retarget
//   typedefs without legacy paths.
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

#ifndef VERILATOR_V3LINKDOTIFACECAPTURE_H_
#define VERILATOR_V3LINKDOTIFACECAPTURE_H_

#include "config_build.h"

#include "V3Ast.h"

#include <cstddef>
#include <functional>
#include <string>
#include <unordered_map>
#include <vector>

class VSymEnt;

class V3LinkDotIfaceCapture final {
public:
    enum class CaptureType { IFACE, CLASS };

    // Path-based map key: no pointers, only stable strings.
    // {ownerModName, refName, cellPath, cloneCellPath} uniquely identifies
    // every captured REFDTYPE.  You cannot have two typedefs with the same
    // name in the same module, so this tuple is unique.
    struct CaptureKey final {
        string ownerModName;  // Module containing the REFDTYPE (e.g. "cca_xbar")
        string refName;  // REFDTYPE name (e.g. "r_chan_t")
        string cellPath;  // Template path (e.g. "cca_io.tlb_io")
        string cloneCellPath;  // Instance path (e.g. "xbar1"), empty for template
        bool operator==(const CaptureKey& o) const {
            return ownerModName == o.ownerModName && refName == o.refName && cellPath == o.cellPath
                   && cloneCellPath == o.cloneCellPath;
        }
    };
    struct CaptureKeyHash final {
        size_t operator()(const CaptureKey& k) const {
            size_t h = std::hash<string>{}(k.ownerModName);
            h ^= std::hash<string>{}(k.refName) + 0x9e3779b9 + (h << 6) + (h >> 2);
            h ^= std::hash<string>{}(k.cellPath) + 0x9e3779b9 + (h << 6) + (h >> 2);
            h ^= std::hash<string>{}(k.cloneCellPath) + 0x9e3779b9 + (h << 6) + (h >> 2);
            return h;
        }
    };

    // Template key: matches ALL entries regardless of cloneCellPath.
    // Used for propagateClone and debug searches.
    struct TemplateKey final {
        string ownerModName;
        string refName;
        string cellPath;
    };

    struct CapturedEntry final {
        CaptureType captureType = CaptureType::IFACE;
        AstRefDType* refp = nullptr;
        string cellPath;  // Template path (e.g. "cca_io.tlb_io") - immutable key component
        string cloneCellPath;  // Instance-specific path (e.g. "cca_io1.tlb_io") - set by
                               // propagateClone when V3Param clones; empty for original entries
        AstClass* origClassp = nullptr;  // For CLASS captures
        // Module where the RefDType lives
        AstNodeModule* ownerModp = nullptr;
        // Typedef definition being referenced
        AstTypedef* typedefp = nullptr;
        // For PARAMTYPEDTYPE
        AstParamTypeDType* paramTypep = nullptr;
        // Name of the module/interface that owns the typedef (stable string)
        string typedefOwnerModName;
        // Interface port variable for matching during cloning
        AstVar* ifacePortVarp = nullptr;
        // Additional REFDTYPEs sharing the same key (e.g. from macro expansions
        // that produce multiple $bits() references to the same interface typedef).
        // The primary refp is stored above; extras are appended here so that
        // retargeting fixes ALL of them, not just the last-writer-wins primary.
        std::vector<AstRefDType*> extraRefps;
        // Visit every AstNode* pointer field (analogous to AstNode::foreachLink).
        // The callback receives an AstNode* by reference; if it nulls the
        // pointer the typed member is nulled accordingly.
        template <typename T_func>
        void foreachLink(T_func&& fn) {
            auto callOnNode = [&](auto*& ptr) {
                AstNode* np = ptr;
                fn(np);
                if (!np) ptr = nullptr;
            };
            callOnNode(refp);
            callOnNode(ownerModp);
            callOnNode(typedefp);
            callOnNode(paramTypep);
            callOnNode(ifacePortVarp);
            callOnNode(origClassp);
            for (auto& xrefp : extraRefps) callOnNode(xrefp);
        }
    };

    using CapturedMap = std::unordered_map<CaptureKey, CapturedEntry, CaptureKeyHash>;

private:
    friend class TypeTableDeadRefVisitor;

    static CapturedMap s_map;
    static bool s_enabled;

    // --- Internal-only methods (not called outside V3LinkDotIfaceCapture.cpp) ---
    static void enable(bool flag);  // LCOV_EXCL_LINE
    static void reset();
    static void clearModuleCache();
    static AstIfaceRefDType* ifaceRefFromVarDType(AstNodeDType* dtypep);
    static string extractIfacePortName(const string& dotText);
    static AstNodeDType* findDTypeByPrettyName(AstNodeModule* modp, const string& prettyName);
    static AstNodeModule* findCloneViaHierarchy(AstNodeModule* containingModp,
                                                AstNodeModule* deadTargetModp, int depth = 0);
    static AstNodeModule* findLiveCloneOf(AstNodeModule* deadTargetModp,
                                          AstNodeModule** containerp = nullptr);
    static int fixDeadRefs(AstRefDType* refp, AstNodeModule* containingModp, const char* location);
    static void captureInnerParamTypeRefs(AstParamTypeDType* paramTypep, AstRefDType* refp,
                                          const string& cellPath, const string& ownerModName,
                                          const string& ptOwnerName);
    static int fixDeadRefsInTypeTable();
    static int fixDeadRefsInModules();
    static int fixWrongCloneRefs();
    static void verifyNoDeadRefs();
    template <typename T_FilterFn, typename T_Fn>
    static void forEachImpl(T_FilterFn&& filter, T_Fn&& fn);

public:
    static bool enabled() { return s_enabled; }
    static AstNodeModule* findOwnerModule(AstNode* nodep);
    // Find a Typedef by name in a module's top-level statements
    static AstTypedef* findTypedefInModule(AstNodeModule* modp, const string& name);
    // Find a NodeDType by name and VNType in a module's top-level statements
    static AstNodeDType* findDTypeInModule(AstNodeModule* modp, const string& name, VNType type);
    // Find a ParamTypeDType by name in a module's top-level statements
    static AstParamTypeDType* findParamTypeInModule(AstNodeModule* modp, const string& name);
    static void add(AstRefDType* refp, const string& cellPath, AstNodeModule* ownerModp,
                    AstTypedef* typedefp = nullptr, const string& typedefOwnerModName = "",
                    AstVar* ifacePortVarp = nullptr);
    static void addClass(AstRefDType* refp, AstClass* origClassp, AstNodeModule* ownerModp,
                         AstTypedef* typedefp = nullptr, const string& typedefOwnerModName = "");
    static void addParamType(AstRefDType* refp, const string& cellPath, AstNodeModule* ownerModp,
                             AstParamTypeDType* paramTypep, const string& paramTypeOwnerModName,
                             AstVar* ifacePortVarp);
    // Exact lookup by full key
    static const CapturedEntry* find(const CaptureKey& key);
    // Pointer-based lookup: linear scan with early exit (no std::function overhead)
    static const CapturedEntry* find(const AstRefDType* refp);
    static void forEach(const std::function<void(const CapturedEntry&)>& fn);
    static void forEachOwned(const AstNodeModule* ownerModp,
                             const std::function<void(const CapturedEntry&)>& fn);
    static std::size_t size() { return s_map.size(); }

    // Walk a dot-separated cell path (e.g. "cca_io.tlb_io") starting from
    // startModp, returning the module at the end of the path.  Returns
    // nullptr if any component cannot be resolved.
    static AstNodeModule* followCellPath(AstNodeModule* startModp, const string& cellPath);

    // Create a new clone entry in the ledger, inheriting from the template.
    // Ledger-only: no target lookup or AST mutation.  Target resolution
    // happens later in finalizeIfaceCapture where cell pointers are wired up.
    static void propagateClone(const TemplateKey& tkey, AstRefDType* newRefp,
                               const string& cloneCellPath);

    static void captureTypedefContext(AstRefDType* refp, const char* stageLabel, int dotPos,
                                      bool dotIsFinal, const std::string& dotText,
                                      VSymEnt* dotSymp, VSymEnt* curSymp, AstNodeModule* modp,
                                      AstNode* nodep,
                                      const std::function<std::string()>& indentFn);

    // Null out ledger refp entries that point to freed nodes (not in the live AST).
    // Called once after V3Param completes, before any code touches the ledger.
    static void purgeStaleRefs();

    // Debug: dump all captured entries
    static void dumpEntries(const string& label);

    // Called after V3Param but before V3Dead to fix any remaining cross-interface refs
    // that still point to template nodes (which will be deleted by V3Dead).
    static void finalizeIfaceCapture();
};

#endif  // VERILATOR_V3LINKDOTIFACECAPTURE_H_
