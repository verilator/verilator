// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Interface typedef capture helper
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

#include "V3LinkDotIfaceCapture.h"

#include "V3Error.h"
#include "V3Global.h"
#include "V3Stats.h"
#include "V3SymTable.h"

#include <unordered_map>
#include <unordered_set>

VL_DEFINE_DEBUG_FUNCTIONS;

V3LinkDotIfaceCapture::CapturedMap V3LinkDotIfaceCapture::s_map{};
bool V3LinkDotIfaceCapture::s_enabled = true;

// LCOV_EXCL_START
void V3LinkDotIfaceCapture::enable(bool flag) {
    s_enabled = flag;
    if (!flag) {
        s_map.clear();
        clearModuleCache();
    }
}
// LCOV_EXCL_STOP

void V3LinkDotIfaceCapture::reset() {
    s_map.clear();
    clearModuleCache();
}

// Per-module cache of statement-level names to avoid O(N*M) linear scans.
// Lazily built on first access for a given module; cleared at phase boundaries.
// Uses vectors per name to handle rare cases where different node types share a name
// (e.g. a Typedef and a ParamTypeDType both named 'sc_tag_status_t').
namespace {
struct StmtNameMap final {
    std::unordered_map<string, std::vector<AstNode*>> m_byName;
    std::unordered_map<string, std::vector<AstNodeDType*>> m_byPrettyName;
};
std::unordered_map<AstNodeModule*, StmtNameMap> s_moduleCache;

const StmtNameMap& getOrBuild(AstNodeModule* modp) {
    auto it = s_moduleCache.find(modp);
    if (it != s_moduleCache.end()) return it->second;
    StmtNameMap& cache = s_moduleCache[modp];
    for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
        const string& nm = stmtp->name();
        if (!nm.empty()) cache.m_byName[nm].push_back(stmtp);
        if (AstNodeDType* const dtp = VN_CAST(stmtp, NodeDType)) {
            const string pn = dtp->prettyName();
            if (!pn.empty()) cache.m_byPrettyName[pn].push_back(dtp);
        }
    }
    return cache;
}
}  // namespace

void V3LinkDotIfaceCapture::clearModuleCache() { s_moduleCache.clear(); }

AstIfaceRefDType* V3LinkDotIfaceCapture::ifaceRefFromVarDType(AstNodeDType* dtypep) {
    AstIfaceRefDType* resultp = nullptr;
    for (AstNodeDType* curp = dtypep; curp;) {
        if (AstIfaceRefDType* const irefp = VN_CAST(curp, IfaceRefDType)) {
            resultp = irefp;
            break;
        } else if (AstBracketArrayDType* const bracketp = VN_CAST(curp, BracketArrayDType)) {
            curp = bracketp->subDTypep();
        } else if (AstUnpackArrayDType* const unpackp = VN_CAST(curp, UnpackArrayDType)) {
            curp = unpackp->subDTypep();
        } else {
            v3fatalSrc("ifaceRefFromVarDType: unexpected dtype " << curp->prettyTypeName()
                                                                 << " in chain");
        }
    }
    return resultp;
}

namespace {
// Resolve the owner module name for a typedef/paramType node.
// Returns hint if non-empty, otherwise walks backp() to find the owner module name.
string resolveOwnerName(const string& hint, AstNode* nodep) {
    if (!hint.empty()) return hint;
    if (!nodep) return "";
    AstNodeModule* const ownerp = V3LinkDotIfaceCapture::findOwnerModule(nodep);
    return ownerp ? ownerp->name() : string{};
}
}  // namespace

AstTypedef* V3LinkDotIfaceCapture::findTypedefInModule(AstNodeModule* modp, const string& name) {
    AstTypedef* resultp = nullptr;
    const StmtNameMap& cache = getOrBuild(modp);
    const auto it = cache.m_byName.find(name);
    if (!(it == cache.m_byName.end())) {
        for (AstNode* nodep : it->second) {
            if (AstTypedef* const tdp = VN_CAST(nodep, Typedef)) {
                resultp = tdp;
                break;
            }
        }
    }
    return resultp;
}
AstNodeDType* V3LinkDotIfaceCapture::findDTypeInModule(AstNodeModule* modp, const string& name,
                                                       VNType type) {

    AstNodeDType* resultp = nullptr;
    const StmtNameMap& cache = getOrBuild(modp);
    const auto it = cache.m_byName.find(name);
    if (!(it == cache.m_byName.end())) {
        for (AstNode* nodep : it->second) {
            if (AstNodeDType* const dtp = VN_CAST(nodep, NodeDType)) {
                if (dtp->type() == type) {
                    resultp = dtp;
                    break;
                }
            }
        }
    }
    return resultp;
}
AstParamTypeDType* V3LinkDotIfaceCapture::findParamTypeInModule(AstNodeModule* modp,
                                                                const string& name) {

    AstParamTypeDType* resultp = nullptr;
    const StmtNameMap& cache = getOrBuild(modp);
    const auto it = cache.m_byName.find(name);
    if (!(it == cache.m_byName.end())) {
        for (AstNode* nodep : it->second) {
            if (AstParamTypeDType* const ptdp = VN_CAST(nodep, ParamTypeDType)) {
                resultp = ptdp;
                break;
            }
        }
    }
    return resultp;
}

AstNodeDType* V3LinkDotIfaceCapture::findDTypeByPrettyName(AstNodeModule* modp,
                                                           const string& prettyName) {
    const StmtNameMap& cache = getOrBuild(modp);
    const auto it = cache.m_byPrettyName.find(prettyName);
    if (it == cache.m_byPrettyName.end()) return nullptr;
    return it->second.front();
}

AstNodeModule* V3LinkDotIfaceCapture::findCloneViaHierarchy(AstNodeModule* containingModp,
                                                            AstNodeModule* deadTargetModp,
                                                            int depth) {
    if (depth > 20) return nullptr;  // Safety limit
    for (AstNode* stmtp = containingModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
        if (AstCell* const cellp = VN_CAST(stmtp, Cell)) {
            AstNodeModule* const cellModp = cellp->modp();
            if (!cellModp || cellModp->dead()) continue;
            // Check if cellModp is a clone of deadTargetModp by comparing
            // the template name (part before "__")
            const string& cellModName = cellModp->name();
            const string& deadName = deadTargetModp->name();
            const size_t pos = cellModName.find("__");
            if (pos != string::npos && cellModName.substr(0, pos) == deadName) { return cellModp; }
            // Recurse into sub-cells
            AstNodeModule* const found
                = findCloneViaHierarchy(cellModp, deadTargetModp, depth + 1);
            if (found) return found;
        }
    }
    return nullptr;
}

int V3LinkDotIfaceCapture::fixDeadRefs(AstRefDType* refp, AstNodeModule* containingModp,
                                       const char* location) {
    int fixed = 0;

    // Fix typedefp pointing to dead module
    if (refp->typedefp()) {
        AstNodeModule* const typedefModp = findOwnerModule(refp->typedefp());
        if (typedefModp && typedefModp->dead()) {
            AstNodeModule* cloneModp = nullptr;
            if (containingModp) { cloneModp = findCloneViaHierarchy(containingModp, typedefModp); }
            if (cloneModp) {
                const string& tdName = refp->typedefp()->name();
                if (AstTypedef* const newTdp = findTypedefInModule(cloneModp, tdName)) {
                    UINFO(9, "iface capture finalizeCapture ("
                                 << location << "): fixing typedefp refp=" << refp << " dead="
                                 << typedefModp->name() << " -> " << cloneModp->name());
                    refp->typedefp(newTdp);
                    ++fixed;
                }
            }
        }
    }

    // Fix refDTypep pointing to dead module
    if (refp->refDTypep()) {
        AstNodeModule* const targetModp = findOwnerModule(refp->refDTypep());
        if (targetModp && targetModp->dead()) {
            AstNodeModule* cloneModp = nullptr;
            if (containingModp) { cloneModp = findCloneViaHierarchy(containingModp, targetModp); }
            bool foundByName = false;
            if (cloneModp) {
                const string& targetName = refp->refDTypep()->prettyName();
                if (AstNodeDType* const newDtp = findDTypeByPrettyName(cloneModp, targetName)) {
                    UINFO(9, "iface capture finalizeCapture ("
                                 << location << "): fixing refDTypep refp=" << refp
                                 << " dead=" << targetModp->name() << " -> " << cloneModp->name());
                    refp->refDTypep(newDtp);
                    ++fixed;
                    foundByName = true;
                }
            }
            // If name-based search failed, try to derive refDTypep from
            // the already-fixed typedefp chain.  The typedefp was fixed
            // above to point to the clone's typedef, so its subDTypep()
            // returns a live dtype (type-table entry or clone-owned).
            // This avoids setting refDTypep to nullptr which would force
            // V3Width to re-walk the dtype tree under TYPETABLE where
            // module provenance is lost, triggering spurious warnings.
            if (!foundByName) {
                AstNodeDType* derivedp = nullptr;
                if (refp->typedefp() && refp->typedefp()->subDTypep()) {
                    derivedp = refp->typedefp()->subDTypep();
                    AstNodeModule* const derivedOwnerp = findOwnerModule(derivedp);
                    if (derivedOwnerp && derivedOwnerp->dead()) { derivedp = nullptr; }
                }
                UINFO(9, "iface capture finalizeCapture ("
                             << location << "): deriving refDTypep from typedefp refp=" << refp
                             << " dead=" << targetModp->name() << " derived=" << derivedp);
                refp->refDTypep(derivedp);
                ++fixed;
            }
        }
    }

    // Fix base-class dtypep() - V3Broken checks this pointer, and V3Width
    // may have set it to a node in the dead template module.  Derive from
    // the (already fixed) typedefp chain when possible.
    if (refp->dtypep()) {
        AstNodeModule* const dtOwnerp = findOwnerModule(refp->dtypep());
        if (dtOwnerp && dtOwnerp->dead()) {
            AstNodeDType* newDtp = nullptr;
            // Derive from the fixed typedef's subDTypep.  This always succeeds
            // because the typedefp was fixed above to point to a clone's typedef
            // whose subDTypep is a live type-table entry or clone-owned dtype.
            // If this fires, either typedefp was not fixed or subDTypep is stale.
            // Dump refp->typedefp() and dtOwnerp to diagnose.
            if (refp->typedefp() && refp->typedefp()->subDTypep()) {
                newDtp = refp->typedefp()->subDTypep();
                AstNodeModule* const newDtOwnerp = findOwnerModule(newDtp);
                if (newDtOwnerp && newDtOwnerp->dead()) newDtp = nullptr;
            }
            UASSERT_OBJ(newDtp, refp,
                        "fixDeadRefs dtypep: could not derive live dtypep for "
                            << refp->prettyNameQ() << " dead owner=" << dtOwnerp->name()
                            << " typedefp="
                            << (refp->typedefp() ? refp->typedefp()->name() : "<null>"));
            UINFO(9, "iface capture finalizeCapture ("
                         << location << "): fixing dtypep refp=" << refp
                         << " dead=" << dtOwnerp->name() << " -> " << newDtp);
            refp->dtypep(newDtp);
            ++fixed;
        }
    }

    return fixed;
}

AstNodeModule* V3LinkDotIfaceCapture::findLiveCloneOf(AstNodeModule* deadTargetModp,
                                                      AstNodeModule** containerp) {
    for (AstNode* np = v3Global.rootp()->modulesp(); np; np = np->nextp()) {
        if (AstNodeModule* const modp = VN_CAST(np, NodeModule)) {
            if (modp->dead()) continue;
            AstNodeModule* const found = findCloneViaHierarchy(modp, deadTargetModp);
            if (found) {
                if (containerp) *containerp = modp;
                return found;
            }
        }
    }
    if (containerp) *containerp = nullptr;
    return nullptr;
}

AstNodeModule* V3LinkDotIfaceCapture::findOwnerModule(AstNode* nodep) {
    for (AstNode* curp = nodep; curp; curp = curp->backp()) {
        // Guard against corrupted backp() chains (e.g. freed memory,
        // low addresses like 0x1) from nodes unlinked by linkDotParamed.
        if (reinterpret_cast<uintptr_t>(curp) < 0x1000) return nullptr;
        if (AstNodeModule* const modp = VN_CAST(curp, NodeModule)) return modp;
    }
    return nullptr;
}

void V3LinkDotIfaceCapture::purgeStaleRefs() {
    if (!s_enabled || s_map.empty() || !v3Global.rootp()) return;
    // Collect every live AstNode* in the AST so we can detect stale pointers
    // in the ledger (refp, ownerModp, typedefp, paramTypep, etc.).
    std::unordered_set<const AstNode*> liveNodes;
    v3Global.rootp()->foreach([&](AstNode* np) { liveNodes.insert(np); });
    for (auto& kv : s_map) {
        kv.second.foreachLink([&](AstNode*& nodep) {
            if (nodep && !liveNodes.count(nodep)) nodep = nullptr;
        });
    }
}

void V3LinkDotIfaceCapture::dumpEntries(const string& label) {
    UINFO(9, "========== iface capture dumpEntries: " << label << " (entries=" << s_map.size()
                                                      << ") ==========");
    int idx = 0;
    for (const auto& pair : s_map) {
        const CaptureKey& key = pair.first;
        const CapturedEntry& entry = pair.second;
        const char* captType = (entry.captureType == CaptureType::IFACE) ? "IFACE" : "CLASS";
        UINFO(9,
              "  [" << idx << "] " << captType << " key={" << key.ownerModName << ","
                    << key.refName << "," << key.cellPath << "," << key.cloneCellPath << "}"
                    << " ref=" << (entry.refp ? entry.refp->name() : "<null>")
                    << " refp=" << cvtToHex(entry.refp) << " cellPath='" << entry.cellPath << "'"
                    << " ownerMod=" << (entry.ownerModp ? entry.ownerModp->name() : "<null>")
                    << " typedefp=" << (entry.typedefp ? entry.typedefp->name() : "<null>")
                    << " typedefOwnerModName='" << entry.typedefOwnerModName << "'"
                    << " paramTypep=" << (entry.paramTypep ? entry.paramTypep->name() : "<null>")
                    << " ifacePortVarp="
                    << (entry.ifacePortVarp ? entry.ifacePortVarp->name() : "<null>"));
        ++idx;
    }
    UINFO(9, "========== end iface capture dumpEntries ==========");
}

string V3LinkDotIfaceCapture::extractIfacePortName(const string& dotText) {
    string name = dotText;
    const size_t dotPos = name.find('.');
    if (dotPos != string::npos) name = name.substr(0, dotPos);
    const size_t braPos = name.find("__BRA__");
    if (braPos != string::npos) name = name.substr(0, braPos);
    return name;
}

void V3LinkDotIfaceCapture::add(AstRefDType* refp, const string& cellPath,
                                AstNodeModule* ownerModp, AstTypedef* typedefp,
                                const string& typedefOwnerModName, AstVar* ifacePortVarp) {
    UASSERT(refp, "add() called with null refp");
    UASSERT(ownerModp, "add() called with null ownerModp for refp=" << refp->prettyNameQ());
    if (!typedefp) typedefp = refp->typedefp();
    const string tdOwnerName = resolveOwnerName(typedefOwnerModName, typedefp);
    const string ownerModName = ownerModp->name();
    const CaptureKey key{ownerModName, refp->name(), cellPath, ""};
    auto it = s_map.find(key);
    if (it != s_map.end()) {
        // Key already exists - append this refp as an extra
        it->second.extraRefps.push_back(refp);
        UINFO(9, "iface capture add (extra): refp="
                     << refp->name() << " cellPath='" << cellPath << "'" << " ownerMod="
                     << ownerModName << " extraRefps.size=" << it->second.extraRefps.size());
    } else {
        s_map[key] = CapturedEntry{
            CaptureType::IFACE,     refp,      cellPath,
            /*cloneCellPath=*/"",
            /*origClassp=*/nullptr, ownerModp, typedefp, nullptr, tdOwnerName, ifacePortVarp, {}};
        UINFO(9, "iface capture add: refp=" << refp->name() << " cellPath='" << cellPath << "'"
                                            << " ownerMod=" << ownerModName << " typedefp="
                                            << (typedefp ? typedefp->name() : "<null>")
                                            << " typedefOwnerModName='" << tdOwnerName << "'");
    }
}

void V3LinkDotIfaceCapture::addClass(AstRefDType* refp, AstClass* origClassp,
                                     AstNodeModule* ownerModp, AstTypedef* typedefp,
                                     const string& typedefOwnerModName) {
    UASSERT(refp, "addClass() called with null refp");
    UASSERT(ownerModp, "addClass() called with null ownerModp");
    if (!typedefp) typedefp = refp->typedefp();
    const string tdOwnerName = resolveOwnerName(typedefOwnerModName, typedefp);
    // For CLASS captures, use the class name as cellPath
    UASSERT_OBJ(origClassp, refp, "addClass() called with null origClassp for refp=" << refp);
    const string cellPath = origClassp->name();
    UASSERT_OBJ(!cellPath.empty(), origClassp, "addClass() produced empty cellPath");
    const string ownerModName = ownerModp->name();
    const CaptureKey key{ownerModName, refp->name(), cellPath, ""};
    s_map[key] = CapturedEntry{CaptureType::CLASS,   refp,       cellPath,
                               /*cloneCellPath=*/"", origClassp, ownerModp, typedefp, nullptr,
                               tdOwnerName,          nullptr,    {}};
    UINFO(9, "iface capture addClass: refp=" << refp->name() << " cellPath='" << cellPath << "'"
                                             << " ownerMod="
                                             << (ownerModp ? ownerModp->name() : "<null>"));
}

// Not called in production - retained as a diagnostic/debug entry point
// for inspecting the capture ledger by key (e.g. from GDB or future code).
const V3LinkDotIfaceCapture::CapturedEntry*  // LCOV_EXCL_START
V3LinkDotIfaceCapture::find(const CaptureKey& key) {
    const auto it = s_map.find(key);
    if (VL_UNLIKELY(it == s_map.end())) return nullptr;
    return &it->second;
}  // LCOV_EXCL_STOP

const V3LinkDotIfaceCapture::CapturedEntry* V3LinkDotIfaceCapture::find(const AstRefDType* refp) {
    if (!refp) return nullptr;
    for (const auto& kv : s_map) {
        if (kv.second.refp == refp) return &kv.second;
    }
    return nullptr;
}

// Walk a dot-separated cell path through the cell / IFACEREFDTYPE hierarchy
// starting from startModp.  Returns the module at the end of the path, or
// nullptr if any component cannot be resolved.
// Cell/port names are preserved across clones by cloneTree, so this works
// identically on template and cloned modules.
AstNodeModule* V3LinkDotIfaceCapture::followCellPath(AstNodeModule* startModp,
                                                     const string& cellPath) {
    if (cellPath.empty() || !startModp) return nullptr;
    AstNodeModule* curModp = startModp;
    string remaining = cellPath;
    while (!remaining.empty() && curModp) {
        string component;
        const size_t dotPos = remaining.find('.');
        if (dotPos == string::npos) {
            component = remaining;
            remaining.clear();
        } else {
            component = remaining.substr(0, dotPos);
            remaining = remaining.substr(dotPos + 1);
        }
        const size_t braPos = component.find("__BRA__");
        const string componentBase
            = (braPos == string::npos) ? component : component.substr(0, braPos);
        AstNodeModule* nextModp = nullptr;
        for (AstNode* sp = curModp->stmtsp(); sp; sp = sp->nextp()) {
            if (AstCell* const cellp = VN_CAST(sp, Cell)) {
                if ((cellp->name() == component || cellp->name() == componentBase)
                    && cellp->modp()) {
                    nextModp = cellp->modp();
                    break;
                }
            }
            if (AstVar* const varp = VN_CAST(sp, Var)) {
                if (varp->isIfaceRef() && varp->subDTypep()) {
                    string varBaseName = varp->name();
                    const size_t viftopPos = varBaseName.find("__Viftop");
                    if (viftopPos != string::npos) {
                        varBaseName = varBaseName.substr(0, viftopPos);
                    }
                    if (varBaseName == component || varBaseName == componentBase) {
                        if (AstIfaceRefDType* const irefp
                            = ifaceRefFromVarDType(varp->subDTypep())) {
                            AstIface* const ifacep = irefp->ifaceViaCellp();
                            if (ifacep) {
                                nextModp = ifacep;
                                break;
                            }
                        }
                    }
                }
            }
        }
        curModp = nextModp;
    }
    return curModp;
}

// Phase 2: CLONE REGISTRATION - ledger only.
// Called from V3Param::deepCloneModule.  At this point the cloned module's
// cells still reference template interface modules (cell->modp() is stale),
// so we MUST NOT walk cellPath or resolve targets here.  We only record the
// clone entry.  Target resolution happens in finalizeIfaceCapture (Phase 3)
// after all cell pointers are wired to the correct interface clones.
// See header ARCHITECTURE comment for the full picture.
void V3LinkDotIfaceCapture::propagateClone(const TemplateKey& tkey, AstRefDType* newRefp,
                                           const string& cloneCellPath) {
    UASSERT(newRefp, "propagateClone() called with null newRefp");
    // Find the template entry by exact key.  The entry was captured during
    // the primary LinkDot pass, so it must exist.  If this fires, either the
    // capture was missed or the key components (ownerModName, refName,
    // cellPath) diverged between capture and clone time.
    const CaptureKey templateKey{tkey.ownerModName, tkey.refName, tkey.cellPath, ""};
    auto it = s_map.find(templateKey);
    UASSERT(it != s_map.end(), "propagateClone: no template entry for tkey={"
                                   << tkey.ownerModName << "," << tkey.refName << ","
                                   << tkey.cellPath << "} cloneCellPath='" << cloneCellPath
                                   << "'");

    // Create a new clone entry - ledger only.
    // Target resolution (paramTypep/typedefp) happens in finalizeIfaceCapture
    // where cell pointers are already wired to the correct interface clones.
    CapturedEntry newEntry = it->second;
    newEntry.refp = newRefp;
    newEntry.cellPath = tkey.cellPath;
    newEntry.cloneCellPath = cloneCellPath;
    newEntry.clearStaleRefs();
    const CaptureKey newKey{tkey.ownerModName, tkey.refName, tkey.cellPath, cloneCellPath};
    s_map[newKey] = newEntry;

    UINFO(9, "propagateClone: tkey={" << tkey.ownerModName << "," << tkey.refName << ","
                                      << tkey.cellPath << "} refp=" << newRefp->name()
                                      << " cloneCellPath='" << cloneCellPath << "'");
}

template <typename T_FilterFn, typename T_Fn>
void V3LinkDotIfaceCapture::forEachImpl(T_FilterFn&& filter, T_Fn&& fn) {
    if (s_map.empty()) return;
    std::vector<CaptureKey> keys;
    keys.reserve(s_map.size());
    for (const auto& kv : s_map) keys.push_back(kv.first);

    for (const CaptureKey& key : keys) {
        const auto it = s_map.find(key);
        if (it == s_map.end()) continue;
        const CapturedEntry& entry = it->second;
        if (!filter(entry)) continue;
        fn(entry);
    }
}

void V3LinkDotIfaceCapture::forEach(const std::function<void(const CapturedEntry&)>& fn) {
    if (!fn || s_map.empty()) return;
    forEachImpl([](const CapturedEntry&) { return true; }, fn);
}

void V3LinkDotIfaceCapture::forEachOwned(const AstNodeModule* ownerModp,
                                         const std::function<void(const CapturedEntry&)>& fn) {
    if (!ownerModp || !fn || s_map.empty()) return;
    const string ownerName = ownerModp->name();
    UINFO(9,
          "iface capture forEachOwned: ownerModp=" << ownerName << " map size=" << s_map.size());
    forEachImpl(
        [ownerModp, &ownerName](const CapturedEntry& e) {
            // Only match template entries (cloneCellPath='').
            // Clone entries are created by propagateClone and must not be
            // re-processed - each clone gets its own target independently.
            if (!e.cloneCellPath.empty()) return false;
            // Match by ownerModp pointer or typedefOwnerModName string
            const bool matches = e.ownerModp == ownerModp || e.typedefOwnerModName == ownerName;
            UINFO(9, "iface capture forEachOwned filter: ref="
                         << (e.refp ? e.refp->name() : "<null>") << " cellPath='" << e.cellPath
                         << "' ownerMod=" << (e.ownerModp ? e.ownerModp->name() : "<null>")
                         << " typedefOwnerModName='" << e.typedefOwnerModName
                         << "' matches=" << matches);
            return matches;
        },
        fn);
}

// replaces the lambda used in V3LinkDot.cpp for iface capture
void V3LinkDotIfaceCapture::captureTypedefContext(AstRefDType* refp, const char* stageLabel,
                                                  int dotPos, bool /*dotIsFinal*/,
                                                  const std::string& dotText, VSymEnt* dotSymp,
                                                  VSymEnt* curSymp, AstNodeModule* modp,
                                                  AstNode* /*nodep*/,
                                                  const std::function<std::string()>& indentFn) {
    if (!enabled() || !refp) return;

    UINFO(9, indentFn() << "iface capture capture request stage=" << stageLabel
                        << " typedef=" << refp << " name=" << refp->name() << " dotPos=" << dotPos
                        << " dotText='" << dotText << "' dotSym=" << dotSymp);

    const AstCell* ifaceCellp = nullptr;
    if (dotSymp && VN_IS(dotSymp->nodep(), Cell)) {
        const AstCell* const cellp = VN_AS(dotSymp->nodep(), Cell);
        if (cellp->modp() && VN_IS(cellp->modp(), Iface)) ifaceCellp = cellp;
    }
    if (!ifaceCellp) {
        UINFO(9, indentFn() << "iface capture capture skipped typedef=" << refp
                            << " (no iface context)");
        return;
    }
    // Skip internal interface typedef references (typedef used within its own interface)
    if (ifaceCellp->modp() == modp) {
        UINFO(9, indentFn() << "iface capture capture skipped typedef=" << refp
                            << " (internal to interface " << modp->name() << ")");
        return;
    }

    // dotText is always non-empty for interface typedef captures.  If this
    // fires, the caller resolved to an interface Cell but did not accumulate
    // a dotText path - investigate the dot-state in visitParseRef.
    UASSERT_OBJ(!dotText.empty(), refp, "captureTypedefContext: dotText empty");
    const string cellPath = dotText;

    AstVar* ifacePortVarp = nullptr;
    if (curSymp) {
        const std::string portName = extractIfacePortName(dotText);
        if (VSymEnt* const portSymp = curSymp->findIdFallback(portName)) {
            ifacePortVarp = VN_CAST(portSymp->nodep(), Var);
            UINFO(9, indentFn() << "iface capture found port var '" << portName << "' -> "
                                << ifacePortVarp);
        }
    }

    // Check if refDTypep is a ParamTypeDType - if so, use addParamType instead of add
    if (AstParamTypeDType* const paramTypep = VN_CAST(refp->refDTypep(), ParamTypeDType)) {
        V3LinkDotIfaceCapture::addParamType(refp, cellPath, modp, paramTypep, "", ifacePortVarp);
    } else {
        V3LinkDotIfaceCapture::add(refp, cellPath, modp, refp->typedefp(), "", ifacePortVarp);
    }

    UINFO(9, indentFn() << "iface capture capture success typedef=" << refp
                        << " cell=" << ifaceCellp << " cellPath='" << cellPath << "'"
                        << " mod=" << (ifaceCellp->modp() ? ifaceCellp->modp()->name() : "<null>")
                        << " dotPos=" << dotPos);
    // Note: the enclosingVar walk + promoteVarToParamType callback was removed.
    // It supported 'localparam xyz_t = iface.rq_t;' without the 'type' keyword,
    // which was never valid SystemVerilog.  CI-CD with v3fatalSrc asserts on
    // the promoteVarCb path and replaceRef confirmed this was dead code.
}

void V3LinkDotIfaceCapture::captureInnerParamTypeRefs(AstParamTypeDType* paramTypep,
                                                      AstRefDType* refp, const string& cellPath,
                                                      const string& ownerModName,
                                                      const string& ptOwnerName) {
    if (!paramTypep) return;
    paramTypep->foreach([&](AstRefDType* innerRefp) {
        if (innerRefp == refp) return;
        if (!innerRefp->refDTypep()) return;

        AstNodeModule* const refOwnerModp = findOwnerModule(innerRefp->refDTypep());
        if (refOwnerModp && VN_IS(refOwnerModp, Iface) && refOwnerModp->name() != ptOwnerName) {
            AstNodeModule* const innerOwnerModp = findOwnerModule(innerRefp);
            const string innerOwnerName = innerOwnerModp ? innerOwnerModp->name() : ownerModName;
            const CaptureKey innerKey{innerOwnerName, innerRefp->name(), cellPath, ""};
            if (s_map.find(innerKey) == s_map.end()) {
                // Find the cell name for the nested interface
                string nestedCellName;
                AstNodeModule* const ptOwnerModp = findOwnerModule(paramTypep);
                if (ptOwnerModp) {
                    for (AstNode* stmtp = ptOwnerModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                        if (AstCell* const cp = VN_CAST(stmtp, Cell)) {
                            if (cp->modp() == refOwnerModp) {
                                nestedCellName = cp->name();
                                break;
                            }
                        }
                    }
                }
                if (VL_UNCOVERABLE(nestedCellName.empty())) {
                    // The nested interface cell should always be found in the
                    // owner module's statements.  If this fires, either
                    // ptOwnerModp is wrong (findOwnerModule returned the wrong
                    // module) or the cell was pruned before capture.
                    v3fatalSrc("captureInnerParamTypeRefs: could not find cell for nested iface '"
                               << refOwnerModp->prettyNameQ() << "' in '"
                               << (ptOwnerModp ? ptOwnerModp->prettyNameQ() : "<null>") << "'");
                }
                UINFO(9, "addParamType: also capturing inner RefDType "
                             << innerRefp << " refDTypep owner=" << refOwnerModp->name()
                             << " nestedCellName='" << nestedCellName << "'");
                s_map[innerKey] = CapturedEntry{CaptureType::IFACE,
                                                innerRefp,
                                                nestedCellName.empty() ? cellPath : nestedCellName,
                                                /*cloneCellPath=*/"",
                                                /*origClassp=*/nullptr,
                                                ptOwnerModp,
                                                innerRefp->typedefp(),
                                                nullptr,
                                                refOwnerModp->name(),
                                                nullptr,
                                                {}};
            }
        }
    });
}

void V3LinkDotIfaceCapture::addParamType(AstRefDType* refp, const string& cellPath,
                                         AstNodeModule* ownerModp, AstParamTypeDType* paramTypep,
                                         const string& paramTypeOwnerModName,
                                         AstVar* ifacePortVarp) {
    UASSERT(refp, "addParamType() called with null refp");
    UASSERT(ownerModp,
            "addParamType() called with null ownerModp for refp='" << refp->prettyNameQ() << "'");
    UASSERT_OBJ(paramTypep, refp,
                "addParamType() called with null paramTypep for refp='" << refp->prettyNameQ()
                                                                        << "'");
    const string ptOwnerName = resolveOwnerName(paramTypeOwnerModName, paramTypep);
    UINFO(9, "addParamType: refp=" << refp << " cellPath='" << cellPath << "'"
                                   << " ownerModp=" << (ownerModp ? ownerModp->name() : "<null>")
                                   << " paramTypep=" << paramTypep << " paramTypeOwnerModName='"
                                   << ptOwnerName << "'");
    if (paramTypep) {
        UINFO(9, "addParamType: paramTypep subDTypep chain:");
        paramTypep->foreach([&](AstRefDType* innerRefp) {
            UINFO(9,
                  "  inner RefDType: "
                      << innerRefp << " refDTypep=" << innerRefp->refDTypep()
                      << (innerRefp->refDTypep() ? " refDTypep->name=" : "")
                      << (innerRefp->refDTypep() ? innerRefp->refDTypep()->prettyTypeName() : ""));
        });
    }
    const string ownerModName = ownerModp->name();
    const CaptureKey key{ownerModName, refp->name(), cellPath, ""};
    auto it = s_map.find(key);
    if (it != s_map.end()) {
        // Key already exists - append this refp as an extra
        it->second.extraRefps.push_back(refp);
        UINFO(9, "addParamType (extra): refp="
                     << refp->name() << " cellPath='" << cellPath << "'" << " ownerMod="
                     << ownerModName << " extraRefps.size=" << it->second.extraRefps.size());
    } else {
        s_map[key]
            = CapturedEntry{CaptureType::IFACE,     refp,      cellPath,
                            /*cloneCellPath=*/"",
                            /*origClassp=*/nullptr, ownerModp, nullptr,  paramTypep, ptOwnerName,
                            ifacePortVarp,          {}};
    }

    // Also capture REFDTYPEs inside the PARAMTYPEDTYPE's subDTypep chain.
    captureInnerParamTypeRefs(paramTypep, refp, cellPath, ownerModName, ptOwnerName);
}

// Visitor that fixes dead references in the global type table.
//
// When interface templates are cloned, REFDTYPEs in the global type table may
// still point to the dead template module. This visitor traverses the type
// table and redirects those references to the appropriate live clone.
//
// Handles both AstRefDType (direct typedef references) and AstMemberDType
// (struct/union member types) in a single traversal for efficiency.
class TypeTableDeadRefVisitor final : public VNVisitor {
    int m_fixed = 0;

    void visit(AstRefDType* refp) override {
        iterateChildren(refp);
        // For type table entries, find the first live module that contains
        // a cell hierarchy leading to the dead target
        AstNodeModule* containingModp = nullptr;
        AstNodeModule* deadTargetModp = nullptr;
        // Check BOTH typedefp and refDTypep for dead owners.
        // Either (or both) may point to a dead module.
        if (refp->typedefp()) {
            AstNodeModule* const tdOwnerp
                = V3LinkDotIfaceCapture::findOwnerModule(refp->typedefp());
            if (tdOwnerp && tdOwnerp->dead()) deadTargetModp = tdOwnerp;
        }
        if (!deadTargetModp && refp->refDTypep()) {
            AstNodeModule* const rdOwnerp
                = V3LinkDotIfaceCapture::findOwnerModule(refp->refDTypep());
            if (rdOwnerp && rdOwnerp->dead()) deadTargetModp = rdOwnerp;
        }
        if (deadTargetModp) {
            V3LinkDotIfaceCapture::findLiveCloneOf(deadTargetModp, &containingModp);
        }
        m_fixed += V3LinkDotIfaceCapture::fixDeadRefs(refp, containingModp, "type table");
    }

    void visit(AstMemberDType* memberp) override {
        iterateChildren(memberp);
        if (!memberp->dtypep()) return;
        AstNodeModule* const dtOwnerp = V3LinkDotIfaceCapture::findOwnerModule(memberp->dtypep());
        if (!dtOwnerp || !dtOwnerp->dead()) return;
        // Try to find the clone of the dead module
        AstNodeModule* const cloneModp = V3LinkDotIfaceCapture::findLiveCloneOf(dtOwnerp);
        if (cloneModp) {
            // Find matching type by name in the clone
            const string& dtName = memberp->dtypep()->prettyName();
            // Try typedef children
            for (AstNode* sp = cloneModp->stmtsp(); sp; sp = sp->nextp()) {
                if (AstTypedef* const tdp = VN_CAST(sp, Typedef)) {
                    if (tdp->subDTypep() && tdp->subDTypep()->prettyName() == dtName) {
                        UINFO(9, "iface capture type table MEMBERDTYPE fixup (via typedef): "
                                     << memberp->name() << " dtypep " << dtOwnerp->name() << " -> "
                                     << cloneModp->name());
                        memberp->dtypep(tdp->subDTypep());
                        ++m_fixed;
                        return;
                    }
                }
            }
        }
        // One of the above fixup paths (prettyName or typedef) always succeeds
        // when cloneModp is found.  If this fires, either cloneModp is null
        // (findLiveCloneOf failed - check that the dead template has a clone)
        // or the dtype name doesn't match any statement in the clone (check
        // memberp->dtypep()->prettyName() against cloneModp's statements).
        v3fatalSrc("MemberDType fixup: could not fix member '"
                   << memberp->name() << "' dtypep points to dead " << dtOwnerp->name()
                   << " cloneModp=" << (cloneModp ? cloneModp->name() : "<null>"));
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    int fixed() const { return m_fixed; }
    explicit TypeTableDeadRefVisitor(AstNode* nodep) { iterate(nodep); }
};

int V3LinkDotIfaceCapture::fixDeadRefsInTypeTable() {
    if (!v3Global.rootp()->typeTablep()) return 0;
    const TypeTableDeadRefVisitor visitor{v3Global.rootp()->typeTablep()};
    return visitor.fixed();
}

int V3LinkDotIfaceCapture::fixDeadRefsInModules() {
    int fixed = 0;
    for (AstNode* nodep = v3Global.rootp()->modulesp(); nodep; nodep = nodep->nextp()) {
        if (AstNodeModule* const modp = VN_CAST(nodep, NodeModule)) {
            if (modp->dead()) continue;
            const string modName = modp->name();
            modp->foreach(
                [&](AstRefDType* refp) { fixed += fixDeadRefs(refp, modp, modName.c_str()); });
        }
    }
    return fixed;
}

int V3LinkDotIfaceCapture::fixWrongCloneRefs() {
    int fixed = 0;

    // TARGET RESOLUTION - the ONLY place that resolves targets and
    // mutates AST.  By this point all cloning is complete and cell pointers
    // are wired to the correct interface clones.  For each entry we walk
    // cellPath from the owner module to find the correct target module, then
    // locate the PARAMTYPEDTYPE / TYPEDEF by name.
    // See V3LinkDotIfaceCapture.h ARCHITECTURE comment for the full picture.

    forEach([&](const CapturedEntry& entry) {
        AstRefDType* const refp = entry.refp;
        if (!refp) return;
        // For clone entries the stored ownerModp is the template (stale cells).
        // Use the actual module containing the REFDTYPE - its cells are wired
        // to the correct interface clones by this point.
        // findOwnerModule handles corrupted backp() chains gracefully.
        AstNodeModule* const ownerModp
            = !entry.cloneCellPath.empty() ? findOwnerModule(refp) : entry.ownerModp;
        if (!ownerModp || ownerModp->dead() || VN_IS(ownerModp, Package)) return;

        AstNodeModule* const rdOwnerBefore
            = (refp->refDTypep() ? findOwnerModule(refp->refDTypep()) : nullptr);
        UINFO(9,
              "finalizeIfaceCapture Phase3 entry: refp="
                  << refp->name() << " (" << cvtToHex(refp) << ")"
                  << " ownerMod=" << ownerModp->name() << " (dead=" << ownerModp->dead() << ")"
                  << " storedOwnerMod=" << (entry.ownerModp ? entry.ownerModp->name() : "<null>")
                  << " cellPath='" << entry.cellPath << "' cloneCellPath='" << entry.cloneCellPath
                  << "' typedefp=" << (refp->typedefp() ? refp->typedefp()->name() : "<null>")
                  << " refDTypep=" << (refp->refDTypep() ? refp->refDTypep()->name() : "<null>")
                  << " refDTypepOwner=" << (rdOwnerBefore ? rdOwnerBefore->name() : "<null>")
                  << " refDTypepDead=" << (rdOwnerBefore ? rdOwnerBefore->dead() : 0));

        // Determine the correct target module using cellPath
        AstNodeModule* correctModp = nullptr;
        if (!entry.cellPath.empty()) {
            correctModp = followCellPath(ownerModp, entry.cellPath);
            UINFO(9, "  followCellPath('"
                         << ownerModp->name() << "', '" << entry.cellPath
                         << "') = " << (correctModp ? correctModp->name() : "<null>")
                         << (correctModp ? (correctModp->dead() ? " (DEAD)" : " (live)") : ""));
            if (correctModp && correctModp->dead()) { correctModp = nullptr; }
        }

        // Proactive target resolution: when cellPath resolved to a valid
        // correctModp, find the PARAMTYPEDTYPE or TYPEDEF by name and apply.
        if (correctModp) {
            const string& refName = refp->name();
            bool resolved = false;
            if (AstParamTypeDType* const ptdp = findParamTypeInModule(correctModp, refName)) {
                refp->refDTypep(ptdp);
                refp->user3(true);
                resolved = true;
                UINFO(9, "finalizeIfaceCapture Phase3: resolved paramTypep '"
                             << refName << "' in " << correctModp->name() << " for refp in "
                             << ownerModp->name() << " cloneCellPath='" << entry.cloneCellPath
                             << "'");
            } else if (AstTypedef* const tdp = findTypedefInModule(correctModp, refName)) {
                refp->typedefp(tdp);
                refp->user3(true);
                resolved = true;
                UINFO(9, "finalizeIfaceCapture Phase3: resolved typedefp '"
                             << refName << "' in " << correctModp->name() << " for refp in "
                             << ownerModp->name() << " cloneCellPath='" << entry.cloneCellPath
                             << "'");
            }
            if (resolved) {
                ++fixed;
                return;
            }
        }

        // Note: the structural disambiguation infrastructure (collectReachable,
        // findCorrectClone, wrong-clone fixup blocks) was removed.  All captured
        // entries have non-empty cellPath, and disambiguateTarget always returns
        // nullptr through the "cellPath unresolved" path.  The wrong-clone fixup
        // blocks were dead code - CI-CD with v3fatalSrc asserts confirmed this.
        // Unresolved entries are fixed by fixDeadRefs in a later phase.
    });

    return fixed;
}

void V3LinkDotIfaceCapture::verifyNoDeadRefs() {
    // Assert: no REFDTYPE in any live module should have typedefp or refDTypep
    // pointing to a dead module.
    for (AstNode* nodep = v3Global.rootp()->modulesp(); nodep; nodep = nodep->nextp()) {
        if (AstNodeModule* const modp = VN_CAST(nodep, NodeModule)) {
            if (modp->dead()) continue;
            modp->foreach([&](AstRefDType* refp) {
                if (refp->typedefp()) {
                    AstNodeModule* const ownerModp = findOwnerModule(refp->typedefp());
                    // Diagnostic block: only entered when fixup logic has a bug
                    // and leaves a typedefp pointing to a dead module.
                    if (ownerModp && ownerModp->dead()) {  // LCOV_EXCL_START
                        bool inLedger = false;
                        forEach([&](const CapturedEntry& e) {
                            if (e.refp == refp) inLedger = true;
                        });
                        UINFO(9, "VERIFY FAIL typedefp: refp="
                                     << refp->name() << " (" << cvtToHex(refp) << ")" << " in mod="
                                     << modp->name() << " typedefp->owner=" << ownerModp->name()
                                     << " inLedger=" << inLedger);
                    }  // LCOV_EXCL_STOP
                    UASSERT_OBJ(!ownerModp || !ownerModp->dead(), refp,  // LCOV_EXCL_LINE
                                "REFDTYPE '" << refp->prettyNameQ() << "' in live module '"
                                             << modp->prettyNameQ()
                                             << "' has typedefp pointing to dead module '"
                                             << ownerModp->prettyNameQ() << "'");
                }
                if (refp->refDTypep()) {
                    AstNodeModule* const ownerModp = findOwnerModule(refp->refDTypep());
                    // Diagnostic block: only entered when fixup logic has a bug
                    // and leaves a refDTypep pointing to a dead module.
                    if (ownerModp && ownerModp->dead()) {  // LCOV_EXCL_START
                        bool inLedger = false;
                        forEach([&](const CapturedEntry& e) {
                            if (e.refp == refp) inLedger = true;
                        });
                        UINFO(9, "VERIFY FAIL refDTypep: refp="
                                     << refp->name() << " (" << cvtToHex(refp) << ")" << " in mod="
                                     << modp->name() << " refDTypep->owner=" << ownerModp->name()
                                     << " inLedger=" << inLedger);
                    }  // LCOV_EXCL_STOP
                    UASSERT_OBJ(!ownerModp || !ownerModp->dead(), refp,  // LCOV_EXCL_LINE
                                "REFDTYPE '" << refp->prettyNameQ() << "' in live module '"
                                             << modp->prettyNameQ()
                                             << "' has refDTypep pointing to dead module '"
                                             << ownerModp->prettyNameQ() << "'");
                }
            });
        }
    }
    if (v3Global.rootp()->typeTablep()) {
        for (AstNode* nodep = v3Global.rootp()->typeTablep()->typesp(); nodep;
             nodep = nodep->nextp()) {
            nodep->foreach([&](AstRefDType* refp) {
                if (refp->typedefp()) {
                    AstNodeModule* const ownerModp = findOwnerModule(refp->typedefp());
                    // Bug-only assertion: fires only if fixup logic fails to
                    // resolve a type-table typedefp away from a dead module.
                    UASSERT_OBJ(!ownerModp || !ownerModp->dead(), refp,  // LCOV_EXCL_LINE
                                "REFDTYPE '"
                                    << refp->prettyNameQ()
                                    << "' in type table has typedefp pointing to dead module '"
                                    << ownerModp->prettyNameQ() << "'");
                }
                if (refp->refDTypep()) {
                    AstNodeModule* const ownerModp = findOwnerModule(refp->refDTypep());
                    // Bug-only assertion: fires only if fixup logic fails to
                    // resolve a type-table refDTypep away from a dead module.
                    UASSERT_OBJ(!ownerModp || !ownerModp->dead(), refp,  // LCOV_EXCL_LINE
                                "REFDTYPE '"
                                    << refp->prettyNameQ()
                                    << "' in type table has refDTypep pointing to dead module '"
                                    << ownerModp->prettyNameQ() << "'");
                }
            });
        }
    }
}

void V3LinkDotIfaceCapture::finalizeIfaceCapture() {
    if (!s_enabled) return;
    UINFO(4, "finalizeIfaceCapture: fixing remaining cross-interface refs");
    if (!v3Global.rootp()) return;
    clearModuleCache();  // Ensure fresh view after all cloning/widthing

    const int typeTableFixed = fixDeadRefsInTypeTable();
    const int moduleFixed = fixDeadRefsInModules();
    UINFO(4, "finalizeIfaceCapture: fixed " << typeTableFixed << " in type table, " << moduleFixed
                                            << " in modules (dead refs)");

    const int wrongCloneFixed = fixWrongCloneRefs();
    UINFO(4, "finalizeIfaceCapture: fixed " << wrongCloneFixed << " wrong-live-clone pointers");

    if (debug() >= 9) dumpEntries("after finalizeIfaceCapture");

    // Emit statistics for --stats
    int templates = 0;
    int clones = 0;
    for (const auto& kv : s_map) {
        if (kv.first.cloneCellPath.empty()) {
            ++templates;
        } else {
            ++clones;
        }
    }
    V3Stats::addStat("IfaceCapture, Entries total", s_map.size());
    V3Stats::addStat("IfaceCapture, Entries template", templates);
    V3Stats::addStat("IfaceCapture, Entries cloned", clones);
    V3Stats::addStat("IfaceCapture, Dead refs fixed in type table", typeTableFixed);
    V3Stats::addStat("IfaceCapture, Dead refs fixed in modules", moduleFixed);
    V3Stats::addStat("IfaceCapture, Wrong-clone refs fixed", wrongCloneFixed);

    verifyNoDeadRefs();
    reset();
}
