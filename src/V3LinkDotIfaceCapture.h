//*************************************************************************
// DESCRIPTION: Interface typedef capture helper.
//
// ARCHITECTURE - Separation of Concerns (do not change without reading):
//
//   The IfaceCapture system has three phases with strict responsibilities:
//
//   1. CAPTURE (V3LinkDot, primary pass):
//      add() / addParamType() / addTypedef() record template entries.
//      Template entries store the REFDTYPE, its cellPath, and the
//      original paramTypep / typedefp from the template module.
//      Template entries have cloneCellPath = "".
//
//   2. CLONE REGISTRATION (V3Param, deepCloneModule):
//      propagateClone() creates clone entries in the ledger.
//      ** LEDGER-ONLY - no target lookup, no AST mutation. **
//      At this point the cloned module's cells still reference template
//      interface modules (cell->modp() is stale).  Any attempt to walk
//      cellPath here finds the wrong module.  Clone entries store the
//      cloned REFDTYPE and cloneCellPath but clear paramTypep/typedefp
//      so that stale template pointers are never carried forward.
//
//   3. TARGET RESOLUTION (finalizeIfaceCapture, after V3Param):
//      Runs after all cloning is complete and cell pointers are wired
//      to the correct interface clones.  For each entry, walks cellPath
//      starting from the entry's owner module (using findOwnerModule(refp)
//      for clone entries) to find the correct target module, then locates
//      the PARAMTYPEDTYPE / TYPEDEF by name and applies it to the REFDTYPE.
//      ** This is the ONLY place that resolves targets and mutates AST. **
//
//   KEY INVARIANT: The path {ownerModName, refName, cellPath, cloneCellPath}
//   is the sole identity.  No clonep(), no pointer matching.  The path IS
//   the disambiguation.
//
//   Template entries have cloneCellPath = ""; clone entries get it set by
//   propagateClone.  TemplateKey (ownerModName, refName, cellPath) matches
//   all entries regardless of cloneCellPath - used for propagation and debug.
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3LINKDOTIFACECAPTURE_H_
#define VERILATOR_V3LINKDOTIFACECAPTURE_H_

#include "config_build.h"

#include "V3Ast.h"
#include "V3SymTable.h"

#include <cstddef>
#include <functional>
#include <string>
#include <unordered_map>

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
        bool operator==(const TemplateKey& o) const {
            return ownerModName == o.ownerModName && refName == o.refName
                   && cellPath == o.cellPath;
        }
    };
    struct TemplateKeyHash final {
        size_t operator()(const TemplateKey& k) const {
            size_t h = std::hash<string>{}(k.ownerModName);
            h ^= std::hash<string>{}(k.refName) + 0x9e3779b9 + (h << 6) + (h >> 2);
            h ^= std::hash<string>{}(k.cellPath) + 0x9e3779b9 + (h << 6) + (h >> 2);
            return h;
        }
    };
    static TemplateKey templateKeyOf(const CaptureKey& k) {
        return {k.ownerModName, k.refName, k.cellPath};
    }

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
    };

    using CapturedMap = std::unordered_map<CaptureKey, CapturedEntry, CaptureKeyHash>;

    // Captured localparam expression for interfaces/classes
    struct CapturedIfaceLocalparam final {
        AstVar* varp = nullptr;  // The localparam variable
        AstNode* origExprp = nullptr;  // Clone of original expression (before constification)
        AstNodeModule* ownerModp = nullptr;  // Owning interface/class
    };
    using LocalparamMap = std::unordered_map<const AstVar*, CapturedIfaceLocalparam>;

private:
    static CapturedMap s_map;
    static LocalparamMap s_localparamMap;
    static bool s_enabled;

    static string extractIfacePortName(const string& dotText);

    template <typename FilterFn, typename Fn>
    static void forEachImpl(FilterFn&& filter, Fn&& fn);

public:
    static void enable(bool flag) {
        s_enabled = flag;
        if (!flag) {
            s_map.clear();
            s_localparamMap.clear();
        }
    }
    static bool enabled() { return s_enabled; }
    static void reset() {
        s_map.clear();
        s_localparamMap.clear();
    }
    static AstNodeModule* findOwnerModule(AstNode* nodep);
    // Extract the last dot-separated component from a cellPath
    static string lastPathComponent(const string& cellPath);
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
    // Lookup by template key (returns first match, for compat)
    static const CapturedEntry* findByTemplate(const TemplateKey& tkey);
    // Iterate all entries matching a template key (all clones + template)
    static void forEachAtPath(const TemplateKey& tkey,
                              const std::function<void(CapturedEntry&)>& fn);
    static bool erase(const CaptureKey& key);
    // Pointer-based erase: remove all entries whose refp matches
    static bool erase(const AstRefDType* refp);
    // Erase all entries matching a template key
    static bool eraseByTemplate(const TemplateKey& tkey);
    static void forEach(const std::function<void(const CapturedEntry&)>& fn);
    static void forEachOwned(const AstNodeModule* ownerModp,
                             const std::function<void(const CapturedEntry&)>& fn);
    static bool replaceRef(const CaptureKey& oldKey, AstRefDType* newRefp);
    // Pointer-based replaceRef: retarget all entries whose refp matches oldRefp
    static bool replaceRef(const AstRefDType* oldRefp, AstRefDType* newRefp);
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

    static void
    captureTypedefContext(AstRefDType* refp, const char* stageLabel, int dotPos, bool dotIsFinal,
                          const std::string& dotText, VSymEnt* dotSymp, VSymEnt* curSymp,
                          AstNodeModule* modp, AstNode* nodep,
                          const std::function<bool(AstVar*, AstRefDType*)>& promoteVarCb,
                          const std::function<std::string()>& indentFn);

    // Localparam expression capture
    static void addLocalparam(AstVar* varp, AstNode* exprp, AstNodeModule* ownerModp);
    static const CapturedIfaceLocalparam* findLocalparam(const AstVar* varp);
    static void
    forEachLocalparamOwned(const AstNodeModule* ownerModp,
                           const std::function<void(const CapturedIfaceLocalparam&)>& fn);
    static std::size_t localparamSize() { return s_localparamMap.size(); }

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
