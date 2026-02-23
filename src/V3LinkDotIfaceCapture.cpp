//*************************************************************************
// DESCRIPTION: Verilator: Interface typedef capture with path-based keys
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

#include "V3LinkDotIfaceCapture.h"

#include "V3Error.h"
#include "V3Global.h"

#include <unordered_set>

VL_DEFINE_DEBUG_FUNCTIONS;

V3LinkDotIfaceCapture::CapturedMap V3LinkDotIfaceCapture::s_map{};
bool V3LinkDotIfaceCapture::s_enabled = false;

namespace {
AstIfaceRefDType* ifaceRefFromVarDType(AstNodeDType* dtypep) {
    for (AstNodeDType* curp = dtypep; curp;) {
        if (AstIfaceRefDType* const irefp = VN_CAST(curp, IfaceRefDType)) return irefp;
        if (AstBracketArrayDType* const bracketp = VN_CAST(curp, BracketArrayDType)) {
            curp = bracketp->subDTypep();
            continue;
        }
        if (AstUnpackArrayDType* const unpackp = VN_CAST(curp, UnpackArrayDType)) {
            curp = unpackp->subDTypep();
            continue;
        }
        break;
    }
    return nullptr;
}
}  // namespace

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
        CapturedEntry& e = kv.second;
        if (e.refp && !liveNodes.count(e.refp)) {
            UINFO(9, "purgeStaleRefs: refp=" << cvtToHex(e.refp) << " key={"
                                             << kv.first.ownerModName << "," << kv.first.refName
                                             << "}" << endl);
            e.refp = nullptr;
        }
        if (e.ownerModp && !liveNodes.count(e.ownerModp)) e.ownerModp = nullptr;
        if (e.typedefp && !liveNodes.count(e.typedefp)) e.typedefp = nullptr;
        if (e.paramTypep && !liveNodes.count(e.paramTypep)) e.paramTypep = nullptr;
        if (e.ifacePortVarp && !liveNodes.count(e.ifacePortVarp)) e.ifacePortVarp = nullptr;
        if (e.origClassp && !liveNodes.count(e.origClassp)) e.origClassp = nullptr;
        for (auto& xrefp : e.extraRefps) {
            if (xrefp && !liveNodes.count(xrefp)) xrefp = nullptr;
        }
    }
}

void V3LinkDotIfaceCapture::dumpEntries(const string& label) {
    UINFO(9, "========== iface capture dumpEntries: " << label << " (entries=" << s_map.size()
                                                      << ") ==========" << endl);
    int idx = 0;
    for (const auto& pair : s_map) {
        const CaptureKey& key = pair.first;
        const CapturedEntry& entry = pair.second;
        const char* captType = (entry.captureType == CaptureType::IFACE) ? "IFACE" : "CLASS";
        UINFO(9,
              "  [" << idx << "] " << captType << " key={" << key.ownerModName << ","
                    << key.refName << "," << key.cellPath << "," << key.cloneCellPath << "}"
                    << " ref='" << (entry.refp ? entry.refp->name() : "<null>") << "'"
                    << " refp=" << cvtToHex(entry.refp) << " cellPath='" << entry.cellPath << "'"
                    << " ownerMod=" << (entry.ownerModp ? entry.ownerModp->name() : "<null>")
                    << " typedefp=" << (entry.typedefp ? entry.typedefp->name() : "<null>")
                    << " typedefOwnerModName='" << entry.typedefOwnerModName << "'"
                    << " paramTypep=" << (entry.paramTypep ? entry.paramTypep->name() : "<null>")
                    << " ifacePortVarp="
                    << (entry.ifacePortVarp ? entry.ifacePortVarp->name() : "<null>") << endl);
        ++idx;
    }
    UINFO(9, "========== end iface capture dumpEntries ==========" << endl);
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
    UASSERT(ownerModp, "add() called with null ownerModp for refp='" << refp->name() << "'");
    if (!typedefp) typedefp = refp->typedefp();
    string tdOwnerName = typedefOwnerModName;
    if (tdOwnerName.empty() && typedefp) {
        AstNodeModule* const tdOwnerModp = findOwnerModule(typedefp);
        if (tdOwnerModp) tdOwnerName = tdOwnerModp->name();
    }
    const string ownerModName = ownerModp->name();
    const CaptureKey key{ownerModName, refp->name(), cellPath, ""};
    auto it = s_map.find(key);
    if (it != s_map.end()) {
        // Key already exists - append this refp as an extra
        it->second.extraRefps.push_back(refp);
        UINFO(9, "iface capture add (extra): refp=" << refp->name() << " cellPath='" << cellPath
                                                    << "'" << " ownerMod=" << ownerModName
                                                    << " extraRefps.size="
                                                    << it->second.extraRefps.size() << endl);
    } else {
        s_map[key] = CapturedEntry{
            CaptureType::IFACE,     refp,      cellPath,
            /*cloneCellPath=*/"",
            /*origClassp=*/nullptr, ownerModp, typedefp, nullptr, tdOwnerName, ifacePortVarp, {}};
        UINFO(9, "iface capture add: refp="
                     << refp->name() << " cellPath='" << cellPath << "'" << " ownerMod="
                     << ownerModName << " typedefp=" << (typedefp ? typedefp->name() : "<null>")
                     << " typedefOwnerModName='" << tdOwnerName << "'" << endl);
    }
}

void V3LinkDotIfaceCapture::addClass(AstRefDType* refp, AstClass* origClassp,
                                     AstNodeModule* ownerModp, AstTypedef* typedefp,
                                     const string& typedefOwnerModName) {
    UASSERT(refp, "addClass() called with null refp");
    UASSERT(ownerModp, "addClass() called with null ownerModp");
    if (!typedefp) typedefp = refp->typedefp();
    string tdOwnerName = typedefOwnerModName;
    if (tdOwnerName.empty() && typedefp) {
        AstNodeModule* const tdOwnerModp = findOwnerModule(typedefp);
        if (tdOwnerModp) tdOwnerName = tdOwnerModp->name();
    }
    // For CLASS captures, use the class name as cellPath
    UASSERT_OBJ(origClassp, refp,
                "addClass() called with null origClassp for refp='" << refp->name() << "'");
    const string cellPath = origClassp->name();
    UASSERT(!cellPath.empty(),
            "addClass() produced empty cellPath from class='" << origClassp->name() << "'");
    const string ownerModName = ownerModp->name();
    const CaptureKey key{ownerModName, refp->name(), cellPath, ""};
    s_map[key] = CapturedEntry{CaptureType::CLASS,   refp,       cellPath,
                               /*cloneCellPath=*/"", origClassp, ownerModp, typedefp, nullptr,
                               tdOwnerName,          nullptr,    {}};
    UINFO(9, "iface capture addClass: refp="
                 << refp->name() << " cellPath='" << cellPath << "'"
                 << " ownerMod=" << (ownerModp ? ownerModp->name() : "<null>") << endl);
}

const V3LinkDotIfaceCapture::CapturedEntry* V3LinkDotIfaceCapture::find(const CaptureKey& key) {
    const auto it = s_map.find(key);
    if (VL_UNLIKELY(it == s_map.end())) return nullptr;
    return &it->second;
}


bool V3LinkDotIfaceCapture::erase(const CaptureKey& key) {
    const auto it = s_map.find(key);
    if (it == s_map.end()) return false;
    s_map.erase(it);
    return true;
}

const V3LinkDotIfaceCapture::CapturedEntry* V3LinkDotIfaceCapture::find(const AstRefDType* refp) {
    if (!refp || s_map.empty()) return nullptr;
    for (const auto& kv : s_map) {
        if (kv.second.refp == refp) return &kv.second;
    }
    return nullptr;
}

bool V3LinkDotIfaceCapture::erase(const AstRefDType* refp) {
    if (!refp || s_map.empty()) return false;
    bool any = false;
    for (auto it = s_map.begin(); it != s_map.end();) {
        if (it->second.refp == refp) {
            it = s_map.erase(it);
            any = true;
        } else {
            ++it;
        }
    }
    return any;
}

bool V3LinkDotIfaceCapture::replaceRef(const AstRefDType* oldRefp, AstRefDType* newRefp) {
    if (!oldRefp || !newRefp || s_map.empty()) return false;
    std::vector<CaptureKey> keys;
    for (const auto& kv : s_map) {
        if (kv.second.refp == oldRefp) keys.push_back(kv.first);
    }
    bool any = false;
    for (const auto& oldKey : keys) {
        auto mit = s_map.find(oldKey);
        if (mit == s_map.end()) continue;
        auto entry = mit->second;
        entry.refp = newRefp;
        s_map.erase(mit);
        const CaptureKey newKey{oldKey.ownerModName, newRefp->name(), oldKey.cellPath,
                                oldKey.cloneCellPath};
        s_map.emplace(newKey, entry);
        any = true;
    }
    return any;
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
    // Find the template entry by path
    const CaptureKey templateKey{tkey.ownerModName, tkey.refName, tkey.cellPath, ""};
    auto it = s_map.find(templateKey);
    if (it == s_map.end()) {
        // Try empty cellPath as fallback (PARAMTYPEDTYPE entries may have empty cellPath)
        const CaptureKey emptyKey{tkey.ownerModName, tkey.refName, "", ""};
        it = s_map.find(emptyKey);
        if (it == s_map.end()) {
            UINFO(9, "propagateClone: no entry for tkey={"
                         << tkey.ownerModName << "," << tkey.refName << "," << tkey.cellPath
                         << "} cloneCellPath='" << cloneCellPath << "' - skipping" << endl);
            return;
        }
    }

    // Create a new clone entry - ledger only.
    // Target resolution (paramTypep/typedefp) happens in finalizeIfaceCapture
    // where cell pointers are already wired to the correct interface clones.
    CapturedEntry newEntry = it->second;
    newEntry.refp = newRefp;
    newEntry.cellPath = tkey.cellPath;  // ensure cellPath is set (empty-key fallback)
    newEntry.cloneCellPath = cloneCellPath;
    // Clear stale template targets - finalizeIfaceCapture will find the
    // correct ones by walking cellPath in the clone's owner module.
    newEntry.paramTypep = nullptr;
    newEntry.typedefp = nullptr;
    newEntry.extraRefps.clear();  // Template's extras are stale in clone context
    const CaptureKey newKey{tkey.ownerModName, tkey.refName, tkey.cellPath, cloneCellPath};
    s_map[newKey] = newEntry;

    UINFO(9, "propagateClone: tkey={" << tkey.ownerModName << "," << tkey.refName << ","
                                      << tkey.cellPath << "} refp=" << newRefp->name()
                                      << " cloneCellPath='" << cloneCellPath << "'" << endl);
}

template <typename FilterFn, typename Fn>
void V3LinkDotIfaceCapture::forEachImpl(FilterFn&& filter, Fn&& fn) {
    if (s_map.empty()) return;
    std::vector<CaptureKey> keys;
    keys.reserve(s_map.size());
    for (const auto& kv : s_map) keys.push_back(kv.first);

    for (const CaptureKey& key : keys) {
        const auto it = s_map.find(key);
        if (it == s_map.end()) continue;
        CapturedEntry& entry = it->second;
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
    UINFO(9, "iface capture forEachOwned: ownerModp=" << ownerName << " map size=" << s_map.size()
                                                      << endl);
    forEachImpl(
        [ownerModp, &ownerName](const CapturedEntry& e) {
            // Only match template entries (cloneCellPath='').
            // Clone entries are created by propagateClone and must not be
            // re-processed - each clone gets its own target independently.
            if (!e.cloneCellPath.empty()) return false;
            // Match by ownerModp pointer or typedefOwnerModName string
            const bool matches = e.ownerModp == ownerModp || e.typedefOwnerModName == ownerName;
            UINFO(9, "iface capture forEachOwned filter: ref='"
                         << (e.refp ? e.refp->name() : "<null>") << "' cellPath='" << e.cellPath
                         << "' ownerMod=" << (e.ownerModp ? e.ownerModp->name() : "<null>")
                         << " typedefOwnerModName='" << e.typedefOwnerModName
                         << "' matches=" << matches << endl);
            return matches;
        },
        fn);
}

// replaces the lambda used in V3LinkDot.cpp for iface capture
void V3LinkDotIfaceCapture::captureTypedefContext(
    AstRefDType* refp, const char* stageLabel, int dotPos, bool dotIsFinal,
    const std::string& dotText, VSymEnt* dotSymp, VSymEnt* curSymp, AstNodeModule* modp,
    AstNode* nodep, const std::function<bool(AstVar*, AstRefDType*)>& promoteVarCb,
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

    // Use dotText as the hierarchical cellPath key component.
    // dotText is the full dot-separated path from the owning module to the
    // interface cell (e.g. "a_inst", "wif.a_inst", "outer.mid.inner").
    // Fall back to ifaceCellp->name() only when dotText is empty
    // (expected for PARAMTYPEDTYPE entries where dotText is not set).
    const string cellPath = dotText.empty() ? ifaceCellp->name() : dotText;
    if (dotText.empty()) {
        UINFO(9, indentFn() << "iface capture using ifaceCellp->name() fallback: '" << cellPath
                            << "' (dotText empty)" << endl);
    }
    UASSERT(!cellPath.empty(),
            "captureTypedefContext: cellPath is empty for refp='" << refp->name() << "'");

    AstVar* ifacePortVarp = nullptr;
    if (!dotText.empty() && curSymp) {
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
    if (!dotIsFinal) return;

    AstVar* enclosingVarp = nullptr;
    for (AstNode* curp = nodep; curp; curp = curp->backp()) {
        if (AstVar* const varp = VN_CAST(curp, Var)) {
            enclosingVarp = varp;
            break;
        }
        if (VN_IS(curp, ParamTypeDType)) break;
        if (VN_IS(curp, NodeModule)) break;
    }
    if (!enclosingVarp || enclosingVarp->user3SetOnce()) return;
    UINFO(9, indentFn() << "iface capture typedef owner var=" << enclosingVarp
                        << " name=" << enclosingVarp->prettyName());

    // Do NOT promote interface parent VARs - they have VARREFs pointing to them from interface
    // port connections. Deleting these VARs would leave dangling VARREFs.
    if (enclosingVarp->isIfaceParent()) {
        UINFO(9, indentFn() << "iface capture skipping isIfaceParent var promotion");
        return;
    }

    // Do NOT promote value parameters (LPARAM/GPARAM) to PARAMTYPEDTYPE.
    // A value param like 'localparam cb::cfg_t cb_cfg = '{XdatSize:$bits(cmd_beat_t)}'
    // merely references an interface typedef in its value expression - it is NOT
    // itself a type alias and must not be converted to a type parameter.
    if (enclosingVarp->isParam()) {
        UINFO(9, indentFn() << "iface capture skipping value param promotion name="
                            << enclosingVarp->prettyName());
        return;
    }

    if (promoteVarCb && promoteVarCb(enclosingVarp, refp)) return;
    UINFO(9, indentFn() << "iface capture failed to convert owner var name="
                        << enclosingVarp->prettyName());
}

void V3LinkDotIfaceCapture::addParamType(AstRefDType* refp, const string& cellPath,
                                         AstNodeModule* ownerModp, AstParamTypeDType* paramTypep,
                                         const string& paramTypeOwnerModName,
                                         AstVar* ifacePortVarp) {
    UASSERT(refp, "addParamType() called with null refp");
    UASSERT(ownerModp,
            "addParamType() called with null ownerModp for refp='" << refp->name() << "'");
    UASSERT_OBJ(paramTypep, refp,
                "addParamType() called with null paramTypep for refp='" << refp->name() << "'");
    string ptOwnerName = paramTypeOwnerModName;
    if (ptOwnerName.empty() && paramTypep) {
        AstNodeModule* const ptOwnerModp = findOwnerModule(paramTypep);
        if (ptOwnerModp) ptOwnerName = ptOwnerModp->name();
    }
    UINFO(9, "addParamType: refp=" << refp << " cellPath='" << cellPath << "'"
                                   << " ownerModp=" << (ownerModp ? ownerModp->name() : "<null>")
                                   << " paramTypep=" << paramTypep << " paramTypeOwnerModName='"
                                   << ptOwnerName << "'" << endl);
    if (paramTypep) {
        UINFO(9, "addParamType: paramTypep subDTypep chain:" << endl);
        paramTypep->foreach([&](AstRefDType* innerRefp) {
            UINFO(9,
                  "  inner RefDType: "
                      << innerRefp << " refDTypep=" << innerRefp->refDTypep()
                      << (innerRefp->refDTypep() ? " refDTypep->name=" : "")
                      << (innerRefp->refDTypep() ? innerRefp->refDTypep()->prettyTypeName() : "")
                      << endl);
        });
    }
    const string ownerModName = ownerModp->name();
    const CaptureKey key{ownerModName, refp->name(), cellPath, ""};
    auto it = s_map.find(key);
    if (it != s_map.end()) {
        // Key already exists - append this refp as an extra
        it->second.extraRefps.push_back(refp);
        UINFO(9, "addParamType (extra): refp=" << refp->name() << " cellPath='" << cellPath << "'"
                                               << " ownerMod=" << ownerModName
                                               << " extraRefps.size="
                                               << it->second.extraRefps.size() << endl);
    } else {
        s_map[key]
            = CapturedEntry{CaptureType::IFACE,     refp,      cellPath,
                            /*cloneCellPath=*/"",
                            /*origClassp=*/nullptr, ownerModp, nullptr,  paramTypep, ptOwnerName,
                            ifacePortVarp,          {}};
    }

    // Also capture REFDTYPEs inside the PARAMTYPEDTYPE's subDTypep chain.
    if (paramTypep) {
        paramTypep->foreach([&](AstRefDType* innerRefp) {
            if (innerRefp == refp) return;
            if (!innerRefp->refDTypep()) return;

            AstNodeModule* const refOwnerModp = findOwnerModule(innerRefp->refDTypep());
            if (refOwnerModp && VN_IS(refOwnerModp, Iface)
                && refOwnerModp->name() != ptOwnerName) {
                AstNodeModule* const innerOwnerModp = findOwnerModule(innerRefp);
                const string innerOwnerName
                    = innerOwnerModp ? innerOwnerModp->name() : ownerModName;
                const CaptureKey innerKey{innerOwnerName, innerRefp->name(), cellPath, ""};
                if (s_map.find(innerKey) == s_map.end()) {
                    // Find the cell name for the nested interface
                    string nestedCellName;
                    AstNodeModule* const ptOwnerModp = findOwnerModule(paramTypep);
                    if (ptOwnerModp) {
                        for (AstNode* stmtp = ptOwnerModp->stmtsp(); stmtp;
                             stmtp = stmtp->nextp()) {
                            if (AstCell* const cp = VN_CAST(stmtp, Cell)) {
                                if (cp->modp() == refOwnerModp) {
                                    nestedCellName = cp->name();
                                    break;
                                }
                            }
                        }
                    }
                    if (nestedCellName.empty()) {
                        UINFO(9, "addParamType WARNING: could not find cell for nested iface '"
                                     << refOwnerModp->name() << "' in '"
                                     << (ptOwnerModp ? ptOwnerModp->name() : "<null>")
                                     << "' - using parent cellPath='" << cellPath << "'" << endl);
                    }
                    UINFO(9, "addParamType: also capturing inner RefDType "
                                 << innerRefp << " refDTypep owner=" << refOwnerModp->name()
                                 << " nestedCellName='" << nestedCellName << "'" << endl);
                    s_map[innerKey]
                        = CapturedEntry{CaptureType::IFACE,
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
}

void V3LinkDotIfaceCapture::finalizeIfaceCapture() {
    if (!s_enabled) return;

    UINFO(4, "finalizeIfaceCapture: fixing remaining cross-interface refs" << endl);

    if (!v3Global.rootp()) return;

    // Context-aware fixup for REFDTYPEs whose typedefp/refDTypep point to dead
    // template modules.  Instead of a global template->clone map (which breaks
    // with multi-instantiation), we walk the cell hierarchy of the containing
    // module to find the correct clone of the target interface.

    // Helper: find a matching node by name in a module
    auto findInModule = [](AstNodeModule* modp, const string& name, bool wantTypedef) -> AstNode* {
        for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (wantTypedef) {
                if (AstTypedef* const tdp = VN_CAST(stmtp, Typedef)) {
                    if (tdp->name() == name) return tdp;
                }
            } else {
                if (AstNodeDType* const dtp = VN_CAST(stmtp, NodeDType)) {
                    if (dtp->prettyName() == name) return dtp;
                }
            }
        }
        return nullptr;
    };

    // Helper: given a module and a dead target module, find the correct clone
    // of the target by walking the containing module's cell hierarchy.
    // For example, if refp is in cache_if__Cz3 and targetModp is dead
    // cache_types_if, we look at cache_if__Cz3's cells to find which clone
    // of cache_types_if it instantiates (cache_types_if__Cz3).
    // This recurses through the hierarchy to handle arbitrary nesting depth.
    std::function<AstNodeModule*(AstNodeModule*, AstNodeModule*, int)> findCloneViaHierarchy;
    findCloneViaHierarchy = [&](AstNodeModule* containingModp, AstNodeModule* deadTargetModp,
                                int depth) -> AstNodeModule* {
        if (depth > 20) return nullptr;  // Safety limit
        for (AstNode* stmtp = containingModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstCell* const cellp = VN_CAST(stmtp, Cell)) {
                AstNodeModule* const cellModp = cellp->modp();
                if (!cellModp) continue;
                // Direct match: this cell points to a clone of the dead target
                if (!cellModp->dead()) {
                    // Check if cellModp is a clone of deadTargetModp by comparing
                    // the template name (part before "__")
                    const string& cellModName = cellModp->name();
                    const string& deadName = deadTargetModp->name();
                    const size_t pos = cellModName.find("__");
                    if (pos != string::npos && cellModName.substr(0, pos) == deadName) {
                        return cellModp;
                    }
                }
                // Recurse into sub-cells
                if (!cellModp->dead()) {
                    AstNodeModule* const found
                        = findCloneViaHierarchy(cellModp, deadTargetModp, depth + 1);
                    if (found) return found;
                }
            }
        }
        return nullptr;
    };

    // Helper: fix a single REFDTYPE's pointers if they point to dead modules.
    // containingModp is the live module that contains this REFDTYPE - used to
    // walk the cell hierarchy for context-aware clone resolution.
    // Fix typedefp FIRST, then refDTypep - this allows refDTypep to be derived
    // from the fixed typedef's subDTypep() when the name-based search fails
    // (e.g. for BASICDTYPE nodes that aren't top-level module statements).
    auto fixDeadRefs
        = [&](AstRefDType* refp, AstNodeModule* containingModp, const char* location) -> int {
        int fixed = 0;

        // Fix typedefp pointing to dead module
        if (refp->typedefp()) {
            AstNodeModule* const typedefModp = findOwnerModule(refp->typedefp());
            if (typedefModp && typedefModp->dead()) {
                AstNodeModule* cloneModp = nullptr;
                if (containingModp) {
                    cloneModp = findCloneViaHierarchy(containingModp, typedefModp, 0);
                }
                if (cloneModp) {
                    const string& tdName = refp->typedefp()->name();
                    if (AstNode* const newp = findInModule(cloneModp, tdName, true)) {
                        UINFO(9, "iface capture finalizeCapture ("
                                     << location << "): fixing typedefp refp=" << refp
                                     << " dead=" << typedefModp->name() << " -> "
                                     << cloneModp->name() << endl);
                        refp->typedefp(VN_AS(newp, Typedef));
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
                if (containingModp) {
                    cloneModp = findCloneViaHierarchy(containingModp, targetModp, 0);
                }
                bool foundByName = false;
                if (cloneModp) {
                    const string& targetName = refp->refDTypep()->prettyName();
                    if (AstNode* const newp = findInModule(cloneModp, targetName, false)) {
                        UINFO(9, "iface capture finalizeCapture ("
                                     << location << "): fixing refDTypep refp=" << refp << " dead="
                                     << targetModp->name() << " -> " << cloneModp->name() << endl);
                        refp->refDTypep(VN_AS(newp, NodeDType));
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
                    if (derivedp) {
                        UINFO(9, "iface capture finalizeCapture ("
                                     << location << "): deriving refDTypep from typedefp refp="
                                     << refp << " dead=" << targetModp->name()
                                     << " derived=" << derivedp << endl);
                        refp->refDTypep(derivedp);
                    } else {
                        UINFO(9, "iface capture finalizeCapture ("
                                     << location << "): clearing dead refDTypep refp=" << refp
                                     << " dead=" << targetModp->name() << endl);
                        refp->refDTypep(nullptr);
                    }
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
                // Try to derive from the fixed typedef's subDTypep
                if (refp->typedefp() && refp->typedefp()->subDTypep()) {
                    newDtp = refp->typedefp()->subDTypep();
                    AstNodeModule* const newDtOwnerp = findOwnerModule(newDtp);
                    if (newDtOwnerp && newDtOwnerp->dead()) newDtp = nullptr;
                }
                // Try refDTypep if we just fixed it
                if (!newDtp && refp->refDTypep()) {
                    newDtp = refp->refDTypep();
                    AstNodeModule* const newDtOwnerp = findOwnerModule(newDtp);
                    if (newDtOwnerp && newDtOwnerp->dead()) newDtp = nullptr;
                }
                if (newDtp) {
                    UINFO(9, "iface capture finalizeCapture ("
                                 << location << "): fixing dtypep refp=" << refp
                                 << " dead=" << dtOwnerp->name() << " -> " << newDtp << endl);
                    refp->dtypep(newDtp);
                    ++fixed;
                } else {
                    // Last resort: clear dtypep to avoid dangling pointer
                    UINFO(9, "iface capture finalizeCapture ("
                                 << location << "): clearing dead dtypep refp=" << refp
                                 << " dead=" << dtOwnerp->name() << endl);
                    refp->dtypep(nullptr);
                    ++fixed;
                }
            }
        }

        return fixed;
    };

    int typeTableFixed = 0;
    int moduleFixed = 0;

    // Walk the type table - no containing module context, but type table entries
    // that point to dead modules need special handling.  We find the containing
    // module by looking at which live module references this type table entry.
    if (v3Global.rootp()->typeTablep()) {
        // Build a map from type table REFDTYPE to the live module that uses it.
        // This is needed because type table entries don't have a direct parent module.
        std::unordered_map<const AstRefDType*, AstNodeModule*> typeTableRefOwners;
        for (AstNode* nodep = v3Global.rootp()->modulesp(); nodep; nodep = nodep->nextp()) {
            if (AstNodeModule* const modp = VN_CAST(nodep, NodeModule)) {
                if (modp->dead()) continue;
                modp->foreach([&](AstRefDType* refp) {
                    // Check if refp's refDTypep or typedefp is in the type table
                    // by checking if the owner module of the target is null or dead
                    if (refp->refDTypep()) {
                        AstNodeModule* const ownerp = findOwnerModule(refp->refDTypep());
                        if (!ownerp) {
                            // Type table entry - record the containing module
                            // (This is a heuristic; the first live module wins)
                        }
                    }
                });
            }
        }

        for (AstNode* nodep = v3Global.rootp()->typeTablep()->typesp(); nodep;
             nodep = nodep->nextp()) {
            nodep->foreach([&](AstRefDType* refp) {
                // For type table entries, find the first live module that contains
                // a cell hierarchy leading to the dead target
                AstNodeModule* containingModp = nullptr;
                AstNodeModule* deadTargetModp = nullptr;
                // Check BOTH typedefp and refDTypep for dead owners.
                // Either (or both) may point to a dead module.
                if (refp->typedefp()) {
                    AstNodeModule* const tdOwnerp = findOwnerModule(refp->typedefp());
                    if (tdOwnerp && tdOwnerp->dead()) deadTargetModp = tdOwnerp;
                }
                if (!deadTargetModp && refp->refDTypep()) {
                    AstNodeModule* const rdOwnerp = findOwnerModule(refp->refDTypep());
                    if (rdOwnerp && rdOwnerp->dead()) deadTargetModp = rdOwnerp;
                }
                if (deadTargetModp) {
                    // Search all live modules for one that has a cell hierarchy
                    // leading to a clone of the dead target
                    for (AstNode* mnodep = v3Global.rootp()->modulesp(); mnodep;
                         mnodep = mnodep->nextp()) {
                        if (AstNodeModule* const modp = VN_CAST(mnodep, NodeModule)) {
                            if (modp->dead()) continue;
                            AstNodeModule* const found
                                = findCloneViaHierarchy(modp, deadTargetModp, 0);
                            if (found) {
                                containingModp = modp;
                                break;
                            }
                        }
                    }
                }
                typeTableFixed += fixDeadRefs(refp, containingModp, "type table");
            });

            // Also fix AstMemberDType and other non-RefDType nodes whose
            // dtypep() points to a dead module.  V3Broken checks dtypep()
            // on ALL nodes, not just AstRefDType.
            nodep->foreach([&](AstMemberDType* memberp) {
                if (!memberp->dtypep()) return;
                AstNodeModule* const dtOwnerp = findOwnerModule(memberp->dtypep());
                if (!dtOwnerp || !dtOwnerp->dead()) return;
                // Try to find the clone of the dead module
                AstNodeModule* cloneModp = nullptr;
                for (AstNode* mnodep = v3Global.rootp()->modulesp(); mnodep;
                     mnodep = mnodep->nextp()) {
                    if (AstNodeModule* const modp = VN_CAST(mnodep, NodeModule)) {
                        if (modp->dead()) continue;
                        AstNodeModule* const found = findCloneViaHierarchy(modp, dtOwnerp, 0);
                        if (found) {
                            cloneModp = found;
                            break;
                        }
                    }
                }
                if (cloneModp) {
                    // Find matching type by name in the clone
                    const string& dtName = memberp->dtypep()->prettyName();
                    for (AstNode* sp = cloneModp->stmtsp(); sp; sp = sp->nextp()) {
                        if (AstNodeDType* const newDtp = VN_CAST(sp, NodeDType)) {
                            if (newDtp->prettyName() == dtName) {
                                UINFO(9, "iface capture type table MEMBERDTYPE fixup: "
                                             << memberp->name() << " dtypep " << dtOwnerp->name()
                                             << " -> " << cloneModp->name() << endl);
                                memberp->dtypep(newDtp);
                                ++typeTableFixed;
                                return;
                            }
                        }
                    }
                    // Try typedef children
                    for (AstNode* sp = cloneModp->stmtsp(); sp; sp = sp->nextp()) {
                        if (AstTypedef* const tdp = VN_CAST(sp, Typedef)) {
                            if (tdp->subDTypep() && tdp->subDTypep()->prettyName() == dtName) {
                                UINFO(9,
                                      "iface capture type table MEMBERDTYPE fixup (via typedef): "
                                          << memberp->name() << " dtypep " << dtOwnerp->name()
                                          << " -> " << cloneModp->name() << endl);
                                memberp->dtypep(tdp->subDTypep());
                                ++typeTableFixed;
                                return;
                            }
                        }
                    }
                }
                // If we can't find the clone, try deriving from the member's
                // subDTypep which may have been fixed already
                if (memberp->subDTypep()) {
                    AstNodeDType* const subDtp = memberp->subDTypep();
                    AstNodeModule* const subOwnerp = findOwnerModule(subDtp);
                    if (!subOwnerp || !subOwnerp->dead()) {
                        // subDTypep is live - use it as dtypep
                        UINFO(9, "iface capture type table MEMBERDTYPE fixup (from subDTypep): "
                                     << memberp->name() << " dtypep " << dtOwnerp->name()
                                     << " -> subDTypep" << endl);
                        memberp->dtypep(subDtp);
                        ++typeTableFixed;
                        return;
                    }
                }
                UINFO(9, "iface capture type table MEMBERDTYPE WARNING: "
                             << memberp->name() << " dtypep points to dead " << dtOwnerp->name()
                             << " - could not fix" << endl);
            });
        }
    }

    // Walk all non-dead modules - Phase 1: fix dead-module pointers
    for (AstNode* nodep = v3Global.rootp()->modulesp(); nodep; nodep = nodep->nextp()) {
        if (AstNodeModule* const modp = VN_CAST(nodep, NodeModule)) {
            if (modp->dead()) continue;
            const string modName = modp->name();
            modp->foreach([&](AstRefDType* refp) {
                moduleFixed += fixDeadRefs(refp, modp, modName.c_str());
            });
        }
    }

    UINFO(4, "finalizeIfaceCapture: fixed " << typeTableFixed << " in type table, " << moduleFixed
                                            << " in modules (dead refs)" << endl);

    // Walk all non-dead modules - Phase 2: fix wrong-live-clone pointers.
    //
    // After Phase 1, all dead-module pointers are fixed. But clonep()
    // last-writer-wins can leave REFDTYPEs pointing to a live sibling clone
    // instead of the correct clone for this instance. For example,
    // cache_if__Cz3 (wrap0) may have a REFDTYPE pointing to a typedef in
    // cache_types_if__Cz5 (wrap1's clone) instead of cache_types_if__Cz3.
    //
    // Detection: for each module, collect all modules reachable via its cell
    // hierarchy (recursively, to arbitrary depth). If a REFDTYPE's target
    // owner is NOT in the reachable set and NOT the module itself, it's
    // pointing to a wrong clone.
    //
    // Fix: search the reachable set for a node with the same name and type.
    int wrongCloneFixed = 0;

    // Per-module edge in the reachable graph: parent + connection name.
    struct ParentEdge final {
        AstNodeModule* parentp;  // Module that instantiates this one
        string connName;  // Cell instance name or port var name
    };

    // Data collected per-module during the reachable walk.
    struct ReachableInfo final {
        // origName -> vector of reachable modules with that origName
        std::map<string, std::vector<AstNodeModule*>> byOrigName;
        // For each reachable module, how it's connected to its parent
        std::map<AstNodeModule*, ParentEdge> parentMap;
        // Flat set for quick membership test
        std::set<AstNodeModule*> flat;
    };

    // Helper: collect all modules reachable from modp via cell hierarchy
    // AND via IFACEREFDTYPE port connections.
    // Both connection types are needed:
    //   - Cells: direct sub-module instantiations
    //   - IFACEREFDTYPE: interface port connections
    // Builds origName map AND parent map (with connection names) for disambiguation.
    // M itself is included in byOrigName so recursive parent-walk can terminate.
    auto collectReachable = [](AstNodeModule* modp) -> ReachableInfo {
        ReachableInfo info;
        info.flat.insert(modp);
        // Include M itself in byOrigName for recursive disambiguation
        const string& modOrigName = modp->origName().empty() ? modp->name() : modp->origName();
        info.byOrigName[modOrigName].push_back(modp);
        std::function<void(AstNodeModule*)> walk;
        walk = [&](AstNodeModule* curp) {
            for (AstNode* sp = curp->stmtsp(); sp; sp = sp->nextp()) {
                // Follow cell instantiations
                if (AstCell* const cellp = VN_CAST(sp, Cell)) {
                    AstNodeModule* const cellModp = cellp->modp();
                    if (cellModp && info.flat.insert(cellModp).second) {
                        const string& origName = cellModp->origName().empty()
                                                     ? cellModp->name()
                                                     : cellModp->origName();
                        info.byOrigName[origName].push_back(cellModp);
                        info.parentMap[cellModp] = {curp, cellp->name()};
                        walk(cellModp);
                    }
                }
                // Follow IFACEREFDTYPE port connections
                if (AstVar* const varp = VN_CAST(sp, Var)) {
                    if (varp->isIfaceRef() && varp->subDTypep()) {
                        if (AstIfaceRefDType* const irefp
                            = ifaceRefFromVarDType(varp->subDTypep())) {
                            AstIface* const ifacep = irefp->ifaceViaCellp();
                            if (ifacep && info.flat.insert(ifacep).second) {
                                const string& origName = ifacep->origName().empty()
                                                             ? ifacep->name()
                                                             : ifacep->origName();
                                info.byOrigName[origName].push_back(ifacep);
                                info.parentMap[ifacep] = {curp, varp->name()};
                                walk(ifacep);
                            }
                        }
                    }
                }
            }
        };
        walk(modp);
        return info;
    };

    // Helper: find the cell/port name that connects parentModp to childModp.
    // Scans parentModp's stmts for a cell or IFACEREFDTYPE port pointing to childModp.
    // Returns empty string if not found.
    auto findConnName = [](AstNodeModule* parentModp, AstNodeModule* childModp) -> string {
        for (AstNode* sp = parentModp->stmtsp(); sp; sp = sp->nextp()) {
            if (AstCell* const cellp = VN_CAST(sp, Cell)) {
                if (cellp->modp() == childModp) return cellp->name();
            }
            if (AstVar* const varp = VN_CAST(sp, Var)) {
                if (varp->isIfaceRef() && varp->subDTypep()) {
                    if (AstIfaceRefDType* const irefp = ifaceRefFromVarDType(varp->subDTypep())) {
                        if (irefp->ifaceViaCellp() == childModp) return varp->name();
                    }
                }
            }
        }
        return "";
    };

    // Helper: given a wrong target owner module W and the reachable info from M,
    // find the correct clone C in M's hierarchy.
    //
    // Strategy: look up modules with matching origName. If exactly one, use it.
    // If multiple (same interface template at different hierarchy levels), we
    // disambiguate using the parent map and connection names.
    //
    // The key invariant: M and the wrong sibling are clones of the same
    // template, so the structural path from M to C mirrors the path from
    // the sibling to W. The path is defined by (parent origName, connection name)
    // pairs at each level. Connection names (cell instance names, port var names)
    // are preserved across clones because cloneTree copies them verbatim.
    //
    // Algorithm:
    // 1. Find W's parent P_wrong and the connection name from P_wrong to W
    //    (by scanning all live modules for a cell/port pointing to W).
    // 2. Recursively find the correct clone of P_wrong in M's hierarchy.
    // 3. Pick the candidate connected to the correct parent via the same
    //    connection name.
    std::function<AstNodeModule*(AstNodeModule*, const ReachableInfo&, std::set<AstNodeModule*>&)>
        findCorrectClone;
    findCorrectClone = [&](AstNodeModule* wrongOwnerp, const ReachableInfo& info,
                           std::set<AstNodeModule*>& visited) -> AstNodeModule* {
        const string& wrongOrigName
            = wrongOwnerp->origName().empty() ? wrongOwnerp->name() : wrongOwnerp->origName();
        auto it = info.byOrigName.find(wrongOrigName);
        if (it == info.byOrigName.end()) return nullptr;
        const auto& candidates = it->second;
        if (candidates.size() == 1) return candidates[0];

        // Multiple candidates - disambiguate by parent + connection name.
        if (visited.count(wrongOwnerp)) return candidates[0];  // cycle guard
        visited.insert(wrongOwnerp);

        // Find W's instantiating parent and connection name by scanning all live modules
        AstNodeModule* wrongParentp = nullptr;
        string wrongConnName;
        for (AstNode* np = v3Global.rootp()->modulesp(); np; np = np->nextp()) {
            AstNodeModule* const scanModp = VN_CAST(np, NodeModule);
            if (!scanModp || scanModp->dead()) continue;
            wrongConnName = findConnName(scanModp, wrongOwnerp);
            if (!wrongConnName.empty()) {
                wrongParentp = scanModp;
                break;
            }
        }

        if (!wrongParentp) {
            UINFO(9, "finalizeIfaceCapture wrong-clone: cannot find parent of "
                         << wrongOwnerp->name() << ", using first candidate" << endl);
            return candidates[0];
        }

        UINFO(9, "finalizeIfaceCapture disambiguate: wrong "
                     << wrongOwnerp->name() << " parent=" << wrongParentp->name() << " conn='"
                     << wrongConnName << "'" << endl);

        // Recursively find the correct clone of W's parent
        AstNodeModule* correctParentp = nullptr;
        if (info.flat.count(wrongParentp)) {
            // W's parent is already in M's reachable set - it IS the correct parent
            correctParentp = wrongParentp;
        } else {
            correctParentp = findCorrectClone(wrongParentp, info, visited);
        }
        if (!correctParentp) return candidates[0];

        // Pick the candidate connected to correctParentp via the same connection name
        for (AstNodeModule* const candp : candidates) {
            auto pit = info.parentMap.find(candp);
            if (pit != info.parentMap.end() && pit->second.parentp == correctParentp
                && pit->second.connName == wrongConnName) {
                UINFO(9, "finalizeIfaceCapture disambiguate: resolved "
                             << wrongOwnerp->name() << " -> " << candp->name()
                             << " via parent=" << correctParentp->name() << " conn='"
                             << wrongConnName << "'" << endl);
                return candp;
            }
        }

        // Fallback: try parent-only match (connection name might differ
        // between cell and port representations)
        for (AstNodeModule* const candp : candidates) {
            auto pit = info.parentMap.find(candp);
            if (pit != info.parentMap.end() && pit->second.parentp == correctParentp) {
                UINFO(9, "finalizeIfaceCapture wrong-clone: parent-only match for "
                             << wrongOrigName << " -> " << candp->name() << " (conn mismatch: '"
                             << wrongConnName << "' vs '" << pit->second.connName << "')" << endl);
                return candp;
            }
        }

        // Final fallback
        UINFO(9, "finalizeIfaceCapture wrong-clone: could not disambiguate "
                     << wrongOrigName << " among " << candidates.size()
                     << " candidates under parent " << correctParentp->name() << " conn='"
                     << wrongConnName << "'" << ", using first" << endl);
        return candidates[0];
    };

    // Phase 3: TARGET RESOLUTION - the ONLY place that resolves targets and
    // mutates AST.  By this point all cloning is complete and cell pointers
    // are wired to the correct interface clones.  For each entry we walk
    // cellPath from the owner module to find the correct target module, then
    // locate the PARAMTYPEDTYPE / TYPEDEF by name.
    // See V3LinkDotIfaceCapture.h ARCHITECTURE comment for the full picture.
    //
    // For entries WITH cellPath: use followCellPath to find the correct target module.
    // For entries WITHOUT cellPath: use collectReachable + findCorrectClone.
    //
    // We cache ReachableInfo per owner module to avoid redundant walks.
    std::unordered_map<AstNodeModule*, ReachableInfo> reachableCache;
    auto getReachable = [&](AstNodeModule* modp) -> const ReachableInfo& {
        auto it = reachableCache.find(modp);
        if (it != reachableCache.end()) return it->second;
        return reachableCache.emplace(modp, collectReachable(modp)).first->second;
    };

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
                  << " refDTypepDead=" << (rdOwnerBefore ? rdOwnerBefore->dead() : 0) << endl);

        // Determine the correct target module using cellPath
        // followCellPath returns the module at the end of the path
        AstNodeModule* correctModp = nullptr;
        if (!entry.cellPath.empty()) {
            correctModp = followCellPath(ownerModp, entry.cellPath);
            UINFO(9, "  followCellPath('"
                         << ownerModp->name() << "', '" << entry.cellPath
                         << "') = " << (correctModp ? correctModp->name() : "<null>")
                         << (correctModp ? (correctModp->dead() ? " (DEAD)" : " (live)") : "")
                         << endl);
            if (correctModp && correctModp->dead()) { correctModp = nullptr; }
        }

        // Proactive target resolution: when cellPath resolved to a valid
        // correctModp, find the PARAMTYPEDTYPE or TYPEDEF by name and apply.
        // This is the primary resolution path for clone entries (whose
        // targets were cleared by propagateClone) and also fixes entries
        // whose targets point to dead or wrong-clone modules.
        if (correctModp) {
            const string& refName = refp->name();
            bool resolved = false;
            for (AstNode* sp = correctModp->stmtsp(); sp; sp = sp->nextp()) {
                if (AstParamTypeDType* const ptdp = VN_CAST(sp, ParamTypeDType)) {
                    if (ptdp->name() == refName) {
                        refp->refDTypep(ptdp);
                        refp->user3(true);
                        resolved = true;
                        UINFO(9, "finalizeIfaceCapture Phase3: resolved paramTypep '"
                                     << refName << "' in " << correctModp->name()
                                     << " for refp in " << ownerModp->name() << " cloneCellPath='"
                                     << entry.cloneCellPath << "'" << endl);
                        break;
                    }
                }
                if (AstTypedef* const tdp = VN_CAST(sp, Typedef)) {
                    if (tdp->name() == refName) {
                        refp->typedefp(tdp);
                        refp->user3(true);
                        resolved = true;
                        UINFO(9, "finalizeIfaceCapture Phase3: resolved typedefp '"
                                     << refName << "' in " << correctModp->name()
                                     << " for refp in " << ownerModp->name() << " cloneCellPath='"
                                     << entry.cloneCellPath << "'" << endl);
                        break;
                    }
                }
            }
            if (resolved) {
                ++wrongCloneFixed;
                return;  // Done - no need for the legacy fixup paths below
            }
        }

        // Fix typedefp pointing to wrong live clone
        if (refp->typedefp()) {
            AstNodeModule* const tdOwnerp = findOwnerModule(refp->typedefp());
            if (tdOwnerp && tdOwnerp != ownerModp && !tdOwnerp->dead()
                && !VN_IS(tdOwnerp, Package)) {
                AstNodeModule* fixModp = nullptr;
                if (correctModp && correctModp != tdOwnerp) {
                    // cellPath says the target should be in correctModp, not tdOwnerp
                    fixModp = correctModp;
                    UINFO(9, "finalizeIfaceCapture typedefp: cellPath disambiguated"
                             " refp="
                                 << refp->name() << " cellPath='" << entry.cellPath
                                 << "' cloneCellPath='" << entry.cloneCellPath
                                 << "' tdOwner=" << tdOwnerp->name()
                                 << " -> correctMod=" << correctModp->name() << endl);
                } else if (correctModp && correctModp == tdOwnerp) {
                    // cellPath confirms target is already correct - no fix needed
                    UINFO(9, "finalizeIfaceCapture typedefp: already correct"
                             " refp="
                                 << refp->name() << " cellPath='" << entry.cellPath
                                 << "' cloneCellPath='" << entry.cloneCellPath
                                 << "' tdOwner=" << tdOwnerp->name() << endl);
                } else if (!correctModp && !entry.cellPath.empty()) {
                    // cellPath couldn't resolve - skip, already logged above
                    UINFO(9, "finalizeIfaceCapture typedefp: cellPath unresolved, skipping"
                             " refp="
                                 << refp->name() << " cellPath='" << entry.cellPath
                                 << "' cloneCellPath='" << entry.cloneCellPath
                                 << "' tdOwner=" << tdOwnerp->name() << endl);
                } else {
                    // No cellPath - fall back to structural disambiguation
                    UASSERT_OBJ(entry.cellPath.empty(), refp,
                                "Unexpected state: correctModp=null but cellPath is non-empty");
                    const ReachableInfo& info = getReachable(ownerModp);
                    if (!info.flat.count(tdOwnerp)) {
                        std::set<AstNodeModule*> visited;
                        fixModp = findCorrectClone(tdOwnerp, info, visited);
                        UINFO(9, "finalizeIfaceCapture typedefp: structural disambig"
                                 " refp="
                                     << refp->name() << " cloneCellPath='" << entry.cloneCellPath
                                     << "' tdOwner=" << tdOwnerp->name() << " -> "
                                     << (fixModp ? fixModp->name() : "<null>") << endl);
                    }
                }
                if (fixModp) {
                    const string& tdName = refp->typedefp()->name();
                    bool found = false;
                    for (AstNode* sp = fixModp->stmtsp(); sp; sp = sp->nextp()) {
                        if (AstTypedef* const newTdp = VN_CAST(sp, Typedef)) {
                            if (newTdp->name() == tdName) {
                                UINFO(9, "finalizeIfaceCapture wrong-clone fixup: "
                                             << ownerModp->name() << " refp=" << refp->name()
                                             << " cellPath='" << entry.cellPath
                                             << "' cloneCellPath='" << entry.cloneCellPath
                                             << "' typedefp " << tdOwnerp->name() << " -> "
                                             << fixModp->name() << endl);
                                refp->typedefp(newTdp);
                                ++wrongCloneFixed;
                                found = true;
                                break;
                            }
                        }
                    }
                    if (!found) {
                        UINFO(9, "finalizeIfaceCapture wrong-clone WARNING: "
                                     << ownerModp->name() << " refp=" << refp->name()
                                     << " cellPath='" << entry.cellPath << "' cloneCellPath='"
                                     << entry.cloneCellPath << "' typedefp name='" << tdName
                                     << "' not found in " << fixModp->name() << endl);
                    }
                }
            }
        }
        // Fix refDTypep pointing to wrong live clone
        if (refp->refDTypep()) {
            AstNodeModule* const rdOwnerp = findOwnerModule(refp->refDTypep());
            if (rdOwnerp && rdOwnerp != ownerModp && !rdOwnerp->dead()
                && !VN_IS(rdOwnerp, Package)) {
                AstNodeModule* fixModp = nullptr;
                if (correctModp && correctModp != rdOwnerp) {
                    fixModp = correctModp;
                    UINFO(9, "finalizeIfaceCapture refDTypep: cellPath disambiguated"
                             " refp="
                                 << refp->name() << " cellPath='" << entry.cellPath
                                 << "' cloneCellPath='" << entry.cloneCellPath
                                 << "' rdOwner=" << rdOwnerp->name()
                                 << " -> correctMod=" << correctModp->name() << endl);
                } else if (correctModp && correctModp == rdOwnerp) {
                    // cellPath confirms target is already correct - no fix needed
                    UINFO(9, "finalizeIfaceCapture refDTypep: already correct"
                             " refp="
                                 << refp->name() << " cellPath='" << entry.cellPath
                                 << "' cloneCellPath='" << entry.cloneCellPath
                                 << "' rdOwner=" << rdOwnerp->name() << endl);
                } else if (!correctModp && !entry.cellPath.empty()) {
                    // cellPath couldn't resolve - skip, already logged above
                    UINFO(9, "finalizeIfaceCapture refDTypep: cellPath unresolved, skipping"
                             " refp="
                                 << refp->name() << " cellPath='" << entry.cellPath
                                 << "' cloneCellPath='" << entry.cloneCellPath
                                 << "' rdOwner=" << rdOwnerp->name() << endl);
                } else {
                    // No cellPath - fall back to structural disambiguation
                    UASSERT_OBJ(entry.cellPath.empty(), refp,
                                "Unexpected state: correctModp=null but cellPath is non-empty");
                    const ReachableInfo& info = getReachable(ownerModp);
                    if (!info.flat.count(rdOwnerp)) {
                        std::set<AstNodeModule*> visited;
                        fixModp = findCorrectClone(rdOwnerp, info, visited);
                        UINFO(9, "finalizeIfaceCapture refDTypep: structural disambig"
                                 " refp="
                                     << refp->name() << " cloneCellPath='" << entry.cloneCellPath
                                     << "' rdOwner=" << rdOwnerp->name() << " -> "
                                     << (fixModp ? fixModp->name() : "<null>") << endl);
                    }
                }
                if (fixModp) {
                    const string& rdName = refp->refDTypep()->name();
                    const VNType rdType = refp->refDTypep()->type();
                    bool found = false;
                    for (AstNode* sp = fixModp->stmtsp(); sp; sp = sp->nextp()) {
                        if (AstNodeDType* const newDtp = VN_CAST(sp, NodeDType)) {
                            if (newDtp->name() == rdName && newDtp->type() == rdType) {
                                UINFO(9, "finalizeIfaceCapture wrong-clone fixup: "
                                             << ownerModp->name() << " refp=" << refp->name()
                                             << " cellPath='" << entry.cellPath
                                             << "' cloneCellPath='" << entry.cloneCellPath
                                             << "' refDTypep " << rdOwnerp->name() << " -> "
                                             << fixModp->name() << endl);
                                refp->refDTypep(newDtp);
                                ++wrongCloneFixed;
                                found = true;
                                break;
                            }
                        }
                    }
                    if (!found) {
                        UINFO(9, "finalizeIfaceCapture wrong-clone WARNING: "
                                     << ownerModp->name() << " refp=" << refp->name()
                                     << " cellPath='" << entry.cellPath << "' cloneCellPath='"
                                     << entry.cloneCellPath << "' refDTypep name='" << rdName
                                     << "' not found in " << fixModp->name() << endl);
                    }
                }
            }
        }
    });

    UINFO(4, "finalizeIfaceCapture: fixed " << wrongCloneFixed << " wrong-live-clone pointers"
                                            << endl);

    if (debug() >= 9) dumpEntries("after Phase 3");

    // Assert: no REFDTYPE in any live module should have typedefp or refDTypep
    // pointing to a dead module. If this fires, V3Param's cloneRelinkGen() failed
    // to redirect a pointer, or something corrupted it after cloning.
    for (AstNode* nodep = v3Global.rootp()->modulesp(); nodep; nodep = nodep->nextp()) {
        if (AstNodeModule* const modp = VN_CAST(nodep, NodeModule)) {
            if (modp->dead()) continue;
            modp->foreach([&](AstRefDType* refp) {
                if (refp->typedefp()) {
                    AstNodeModule* const ownerModp = findOwnerModule(refp->typedefp());
                    if (ownerModp && ownerModp->dead()) {
                        // Check if this refp is in the ledger
                        bool inLedger = false;
                        forEach([&](const CapturedEntry& e) {
                            if (e.refp == refp) inLedger = true;
                        });
                        UINFO(9, "VERIFY FAIL typedefp: refp="
                                     << refp->name() << " (" << cvtToHex(refp) << ")" << " in mod="
                                     << modp->name() << " typedefp->owner=" << ownerModp->name()
                                     << " inLedger=" << inLedger << endl);
                    }
                    UASSERT_OBJ(!ownerModp || !ownerModp->dead(), refp,
                                "REFDTYPE '" << refp->name() << "' in live module '"
                                             << modp->name()
                                             << "' has typedefp pointing to dead module '"
                                             << ownerModp->name() << "'");
                }
                if (refp->refDTypep()) {
                    AstNodeModule* const ownerModp = findOwnerModule(refp->refDTypep());
                    if (ownerModp && ownerModp->dead()) {
                        // Check if this refp is in the ledger
                        bool inLedger = false;
                        forEach([&](const CapturedEntry& e) {
                            if (e.refp == refp) inLedger = true;
                        });
                        UINFO(9, "VERIFY FAIL refDTypep: refp="
                                     << refp->name() << " (" << cvtToHex(refp) << ")" << " in mod="
                                     << modp->name() << " refDTypep->owner=" << ownerModp->name()
                                     << " inLedger=" << inLedger << endl);
                    }
                    UASSERT_OBJ(!ownerModp || !ownerModp->dead(), refp,
                                "REFDTYPE '" << refp->name() << "' in live module '"
                                             << modp->name()
                                             << "' has refDTypep pointing to dead module '"
                                             << ownerModp->name() << "'");
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
                    UASSERT_OBJ(!ownerModp || !ownerModp->dead(), refp,
                                "REFDTYPE '"
                                    << refp->name()
                                    << "' in type table has typedefp pointing to dead module '"
                                    << ownerModp->name() << "'");
                }
                if (refp->refDTypep()) {
                    AstNodeModule* const ownerModp = findOwnerModule(refp->refDTypep());
                    UASSERT_OBJ(!ownerModp || !ownerModp->dead(), refp,
                                "REFDTYPE '"
                                    << refp->name()
                                    << "' in type table has refDTypep pointing to dead module '"
                                    << ownerModp->name() << "'");
                }
            });
        }
    }

    // Ledger is fully consumed - clean up.
    // Previously reset() was called in ~LinkDotState, but that runs before
    // finalizeIfaceCapture and destroyed the data we need.
    reset();
}
