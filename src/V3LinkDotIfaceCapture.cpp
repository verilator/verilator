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
//   Each captured REFDTYPE carries its own capture record (a VIfaceCaptureTag,
//   see AstRefDType::captureTagp): the cell path from its owner module to the
//   interface, the interface's name, and whether the target is a typedef or a
//   parameter type.  Nothing here points into the AST, so a freed reference
//   takes its record with it, and a cloned reference shares it.
//
//   1. CAPTURE (V3LinkDot, primary pass):
//      captureTypedefContext() / addParamType() tag the reference.
//
//   2. PARAMETERIZATION (V3Param):
//      After a module is cloned, and after an interface cell is specialized,
//      V3Param walks that one module and retargets its tagged references by
//      cell path, so widths computed during parameterization use the
//      specialized interface.
//
//   3. TARGET RESOLUTION (finalizeIfaceCapture, after V3Param):
//      Walks every tagged reference in a live module, follows its cell path
//      from its owner module and retargets it by name, then clears all tags.
//

#include "V3LinkDotIfaceCapture.h"

#include "V3Error.h"
#include "V3Global.h"
#include "V3Stats.h"
#include "V3SymTable.h"

#include <unordered_map>
#include <unordered_set>

VL_DEFINE_DEBUG_FUNCTIONS;

std::deque<VIfaceCaptureTag> V3LinkDotIfaceCapture::s_tags{};
bool V3LinkDotIfaceCapture::s_enabled = true;

// LCOV_EXCL_START
void V3LinkDotIfaceCapture::enable(bool flag) {
    s_enabled = flag;
    if (!flag) clearModuleCache();
}
// LCOV_EXCL_STOP

void V3LinkDotIfaceCapture::reset() {
    s_tags.clear();
    clearModuleCache();
}

// Per-module cache of statement-level names to avoid O(N*M) linear scans.
// Lazily built on first access for a given module; cleared at phase boundaries.
// Uses vectors per name to handle rare cases where different node types share a name
// (e.g. a Typedef and a ParamTypeDType both named 'sc_tag_status_t').
namespace {
struct StmtNameMap final {
    std::unordered_map<string, std::vector<AstNode*>> m_byName;
};
std::unordered_map<AstNodeModule*, StmtNameMap> s_moduleCache;

const StmtNameMap& getOrBuild(AstNodeModule* modp) {
    auto it = s_moduleCache.find(modp);
    if (it != s_moduleCache.end()) return it->second;
    StmtNameMap& cache = s_moduleCache[modp];
    for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
        const string& nm = stmtp->name();
        if (!nm.empty()) cache.m_byName[nm].push_back(stmtp);
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

bool V3LinkDotIfaceCapture::retargetRefToModule(AstRefDType* refp, AstNodeModule* targetModp) {
    const VIfaceCaptureTag* const tagp = refp->captureTagp();
    UASSERT_OBJ(tagp, refp, "Retarget of a reference that was not captured");
    if (!targetModp) return false;

    if (tagp->m_kind == VIfaceCaptureTag::Kind::PARAM_TYPE) {
        AstParamTypeDType* const paramTypep = findParamTypeInModule(targetModp, refp->name());
        if (!paramTypep) return false;
        retargetRefToParamType(refp, paramTypep);
        return true;
    }

    AstTypedef* const typedefp = findTypedefInModule(targetModp, refp->name());
    if (!typedefp) return false;
    retargetRefToTypedef(refp, typedefp);
    return true;
}

void V3LinkDotIfaceCapture::retargetRefToParamType(AstRefDType* refp,
                                                   AstParamTypeDType* paramTypep) {
    UASSERT_OBJ(paramTypep, refp, "Retarget to a null parameter type");
    refp->refDTypep(paramTypep);
    refp->dtypep(paramTypep);
}

void V3LinkDotIfaceCapture::retargetRefToTypedef(AstRefDType* refp, AstTypedef* typedefp) {
    UASSERT_OBJ(typedefp, refp, "Retarget to a null typedef");
    refp->typedefp(typedefp);
    // An incomplete typedef is still a successful name resolution, but
    // must not erase type links that a later width pass can complete.
    if (AstNodeDType* const dtypep = typedefp->subDTypep()) {
        refp->refDTypep(dtypep);
        refp->dtypep(dtypep);
    }
}

bool V3LinkDotIfaceCapture::isCloneOfModule(const AstNodeModule* modp,
                                            const AstNodeModule* templateModp) {
    if (!modp || !templateModp || modp == templateModp) return false;
    // Only a module that was actually copied has copies, which keeps a copy from
    // matching another copy of the same original.
    if (!templateModp->parameterizedTemplate()) return false;
    // A copy keeps the name the module was written with, whatever it was renamed to.
    return modp->origName() == templateModp->origName();
}

AstNodeModule* V3LinkDotIfaceCapture::findCloneViaHierarchy(AstNodeModule* containingModp,
                                                            AstNodeModule* deadTargetModp,
                                                            int depth) {
    if (depth > 20) return nullptr;  // Safety limit
    for (AstNode* stmtp = containingModp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
        if (AstCell* const cellp = VN_CAST(stmtp, Cell)) {
            AstNodeModule* const cellModp = cellp->modp();
            if (!cellModp || cellModp->dead()) continue;
            if (isCloneOfModule(cellModp, deadTargetModp)) return cellModp;
            // Recurse into sub-cells
            AstNodeModule* const found
                = findCloneViaHierarchy(cellModp, deadTargetModp, depth + 1);
            if (found) return found;
        }
    }
    return nullptr;
}

namespace {
using LiveNodes = std::unordered_set<const AstNode*>;

// A scoped snapshot of every node currently in the tree.  V3Broken::isLinkable()
// cannot serve this role: its table is populated only while V3Broken::brokenAll()
// runs and is cleared before it returns, and brokenAll() would itself assert on
// the dangling cross-links this pass has yet to repair.
LiveNodes collectLiveNodes() {
    LiveNodes liveNodes;
    v3Global.rootp()->foreach([&](AstNode* nodep) { liveNodes.insert(nodep); });
    return liveNodes;
}

// Find the module that owns this node; a snapshot, if given, stops the walk at a stale link.
AstNodeModule* findOwnerModuleImpl(AstNode* nodep, const LiveNodes* liveNodesp) {
    for (AstNode* curp = nodep; curp; curp = curp->backp()) {
        if (liveNodesp && !liveNodesp->count(curp)) return nullptr;
        if (AstNodeModule* const modp = VN_CAST(curp, NodeModule)) return modp;
    }
    return nullptr;
}

AstNodeModule* findOwnerModuleIfLive(AstNode* nodep, const LiveNodes& liveNodes) {
    return findOwnerModuleImpl(nodep, &liveNodes);
}

// Shared by the callers that all asked this the same way.
AstNodeModule* dyingOwnerOf(AstNode* nodep, const LiveNodes& liveNodes) {
    if (!nodep || !liveNodes.count(nodep)) return nullptr;
    AstNodeModule* const ownerp = findOwnerModuleIfLive(nodep, liveNodes);
    return (ownerp && ownerp->dead()) ? ownerp : nullptr;
}

bool moduleMatchesOwner(const AstNodeModule* modp, const string& ownerName) {
    if (!modp || ownerName.empty()) return false;
    return modp->name() == ownerName || modp->origName() == ownerName;
}
}  // namespace

int V3LinkDotIfaceCapture::fixDeadRefs(AstRefDType* refp, AstNodeModule* containingModp,
                                       const char* location, const LiveNodes& liveNodes) {
    int fixed = 0;

    // Check both links, a reference may only have one of them.
    AstTypedef* const oldTypedefp = refp->typedefp();
    AstNodeModule* deadModp = dyingOwnerOf(oldTypedefp, liveNodes);
    if (!deadModp) deadModp = dyingOwnerOf(refp->refDTypep(), liveNodes);

    if (deadModp && containingModp) {
        // The module we are in can be the copy we want.
        AstNodeModule* const cloneModp = isCloneOfModule(containingModp, deadModp)
                                             ? containingModp
                                             : findCloneViaHierarchy(containingModp, deadModp);
        if (cloneModp) {
            // A reference without a typedef still has its own name.
            const string& tdName = oldTypedefp ? oldTypedefp->name() : refp->name();
            // Use the same retargets as the ledger so nothing is left behind.
            if (AstTypedef* const newTdp = findTypedefInModule(cloneModp, tdName)) {
                UINFO(9, "iface capture finalizeCapture (" << location << "): fixing refp=" << refp
                                                           << " dead=" << deadModp->name()
                                                           << " -> " << cloneModp->name());
                retargetRefToTypedef(refp, newTdp);
                ++fixed;
            }
        }
    }

    // Only worth checking when there is no typedef, as that is read first.
    AstNodeDType* const oldRefDTypep = refp->refDTypep();
    if (!refp->typedefp() && oldRefDTypep && liveNodes.count(oldRefDTypep)) {
        AstNodeModule* const targetModp = findOwnerModuleIfLive(oldRefDTypep, liveNodes);
        UASSERT_OBJ(!targetModp || !targetModp->dead(), refp,
                    "refDTypep of '" << refp->prettyNameQ() << "' points to dead module '"
                                     << (targetModp ? targetModp->name() : "") << "'");
    }

    // dtypep (checked later by V3Broken) likewise never points at a dead module.
    AstNodeDType* const oldDTypep = refp->dtypep();
    if (oldDTypep && liveNodes.count(oldDTypep)) {
        AstNodeModule* const dtOwnerp = findOwnerModuleIfLive(oldDTypep, liveNodes);
        UASSERT_OBJ(!dtOwnerp || !dtOwnerp->dead(), refp,
                    "dtypep of '" << refp->prettyNameQ() << "' points to dead module '"
                                  << (dtOwnerp ? dtOwnerp->name() : "") << "'");
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
    return findOwnerModuleImpl(nodep, nullptr);
}

void V3LinkDotIfaceCapture::dumpEntries(const string& label) {
    UINFO(9, "========== iface capture dumpEntries: " << label << " ==========");
    int idx = 0;
    v3Global.rootp()->foreach([&](AstRefDType* refp) {
        const VIfaceCaptureTag* const tagp = captureTag(refp);
        if (!tagp) return;
        const AstNodeModule* const ownerModp = findOwnerModule(refp);
        UINFO(9, "  [" << idx << "] ref=" << refp->name() << " refp=" << cvtToHex(refp)
                       << " ownerMod=" << (ownerModp ? ownerModp->name() : "<null>")
                       << " cellPath='" << tagp->m_cellPath << "' ownerModName='"
                       << tagp->m_ownerModName << "' kind="
                       << (tagp->m_kind == VIfaceCaptureTag::Kind::PARAM_TYPE ? "param type"
                                                                              : "typedef"));
        ++idx;
    });
    UINFO(9, "========== end iface capture dumpEntries (" << idx << " captured) ==========");
}

void V3LinkDotIfaceCapture::tag(AstRefDType* refp, const AstNodeModule* capturedInp,
                                VIfaceCaptureTag::Kind kind, const string& cellPath,
                                const string& ownerModName) {
    if (refp->captureTagp()) return;  // First capture wins
    UASSERT_OBJ(capturedInp, refp, "Captured reference is not in a module");
    s_tags.push_back(VIfaceCaptureTag{kind, cellPath, ownerModName, capturedInp->origName()});
    refp->captureTagp(&s_tags.back());
}

const VIfaceCaptureTag* V3LinkDotIfaceCapture::captureTag(AstRefDType* refp) {
    const VIfaceCaptureTag* const tagp = refp->captureTagp();
    if (!tagp) return nullptr;
    const AstNodeModule* const ownerp = findOwnerModule(refp);
    if (!ownerp || ownerp->origName() != tagp->m_capturedInName) return nullptr;
    return tagp;
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
        // Matched without any array index; the elements of an instance array (see V3Param) all
        // instantiate the same module, so any of them will do
        const string componentBase = AstNode::nameNoArray(component);
        AstNodeModule* nextModp = nullptr;
        for (AstNode* sp = curModp->stmtsp(); sp; sp = sp->nextp()) {
            if (AstCell* const cellp = VN_CAST(sp, Cell)) {
                if ((cellp->name() == component
                     || AstNode::nameNoArray(cellp->name()) == componentBase)
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
                    if (varBaseName == component
                        || AstNode::nameNoArray(varBaseName) == componentBase) {
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

// replaces the lambda used in V3LinkDot.cpp for iface capture
void V3LinkDotIfaceCapture::captureTypedefContext(AstRefDType* refp, const char* stageLabel,
                                                  int dotPos, const std::string& dotText,
                                                  VSymEnt* dotSymp, AstNodeModule* modp,
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

    // A reference to a ParamTypeDType is captured as a parameter type, else as a typedef
    if (AstParamTypeDType* const paramTypep = VN_CAST(refp->refDTypep(), ParamTypeDType)) {
        V3LinkDotIfaceCapture::addParamType(refp, cellPath, modp, paramTypep, "");
    } else {
        tag(refp, modp, VIfaceCaptureTag::Kind::TYPEDEF, cellPath,
            resolveOwnerName("", refp->typedefp()));
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
                                                      AstRefDType* refp,
                                                      const string& ptOwnerName) {
    if (!paramTypep) return;
    paramTypep->foreach([&](AstRefDType* innerRefp) {
        if (innerRefp == refp) return;
        if (!innerRefp->refDTypep()) return;

        AstNodeModule* const refOwnerModp = findOwnerModule(innerRefp->refDTypep());
        if (refOwnerModp && VN_IS(refOwnerModp, Iface) && refOwnerModp->name() != ptOwnerName) {
            if (!innerRefp->captureTagp()) {
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
                tag(innerRefp, ptOwnerModp, VIfaceCaptureTag::Kind::TYPEDEF, nestedCellName,
                    refOwnerModp->name());
            }
        }
    });
}

void V3LinkDotIfaceCapture::addParamType(AstRefDType* refp, const string& cellPath,
                                         AstNodeModule* ownerModp, AstParamTypeDType* paramTypep,
                                         const string& paramTypeOwnerModName) {
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
    tag(refp, ownerModp, VIfaceCaptureTag::Kind::PARAM_TYPE, cellPath, ptOwnerName);

    // Also capture REFDTYPEs inside the PARAMTYPEDTYPE's subDTypep chain.
    captureInnerParamTypeRefs(paramTypep, refp, ptOwnerName);
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
    const LiveNodes& m_liveNodes;
    int m_fixed = 0;

    void visit(AstRefDType* refp) override {
        iterateChildren(refp);
        // For type table entries, find the first live module that contains
        // a cell hierarchy leading to the dead target
        AstNodeModule* containingModp = nullptr;
        // Either (or both) links may point to a dead module.
        AstNodeModule* deadTargetModp = dyingOwnerOf(refp->typedefp(), m_liveNodes);
        if (!deadTargetModp) deadTargetModp = dyingOwnerOf(refp->refDTypep(), m_liveNodes);
        if (deadTargetModp) {
            V3LinkDotIfaceCapture::findLiveCloneOf(deadTargetModp, &containingModp);
        }
        m_fixed
            += V3LinkDotIfaceCapture::fixDeadRefs(refp, containingModp, "type table", m_liveNodes);
    }

    void visit(AstMemberDType* memberp) override {
        iterateChildren(memberp);
        if (!memberp->dtypep()) return;
        UASSERT_OBJ(m_liveNodes.count(memberp->dtypep()), memberp,
                    "MemberDType has a dangling dtypep");
        AstNodeModule* const dtOwnerp = findOwnerModuleIfLive(memberp->dtypep(), m_liveNodes);
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
    TypeTableDeadRefVisitor(AstNode* nodep, const LiveNodes& liveNodes)
        : m_liveNodes{liveNodes} {
        iterate(nodep);
    }
};

int V3LinkDotIfaceCapture::fixDeadRefsInTypeTable(const LiveNodes& liveNodes) {
    if (!v3Global.rootp()->typeTablep()) return 0;
    const TypeTableDeadRefVisitor visitor{v3Global.rootp()->typeTablep(), liveNodes};
    return visitor.fixed();
}

int V3LinkDotIfaceCapture::fixDeadRefsInModules(const LiveNodes& liveNodes) {
    int fixed = 0;
    for (AstNode* nodep = v3Global.rootp()->modulesp(); nodep; nodep = nodep->nextp()) {
        if (AstNodeModule* const modp = VN_CAST(nodep, NodeModule)) {
            if (modp->dead()) continue;
            const string modName = modp->name();
            modp->foreach([&](AstRefDType* refp) {
                fixed += fixDeadRefs(refp, modp, modName.c_str(), liveNodes);
            });
        }
    }
    return fixed;
}

int V3LinkDotIfaceCapture::resolveCapturedRefs() {
    int fixed = 0;

    // TARGET RESOLUTION.  By this point all cloning is complete and cell
    // pointers are wired to the correct interface clones.  For each tagged
    // reference we walk its cell path from its owner module to find the
    // correct target module, then locate the PARAMTYPEDTYPE / TYPEDEF by name.
    // See the ARCHITECTURE comment above for the full picture.

    v3Global.rootp()->foreach([&](AstRefDType* refp) {
        const VIfaceCaptureTag* const tagp = captureTag(refp);
        if (!tagp) return;
        AstNodeModule* const ownerModp = findOwnerModule(refp);
        if (!ownerModp || ownerModp->dead() || VN_IS(ownerModp, Package)) return;

        UINFO(9, "finalizeIfaceCapture Phase3 entry: refp="
                     << refp->name() << " (" << cvtToHex(refp) << ")" << " ownerMod="
                     << ownerModp->name() << " cellPath='" << tagp->m_cellPath << "' targetKind="
                     << (tagp->m_kind == VIfaceCaptureTag::Kind::PARAM_TYPE ? "param type"
                                                                            : "typedef"));

        // Prefer the owner itself when its stable template identity matches the
        // captured target owner.  Otherwise resolve and validate the cell path.
        AstNodeModule* correctModp = nullptr;
        if (moduleMatchesOwner(ownerModp, tagp->m_ownerModName)) {
            correctModp = ownerModp;
        } else {
            // A non-matching owner always carries a cell path to the target owner.
            UASSERT_OBJ(!tagp->m_cellPath.empty(), refp,
                        "captured ref '"
                            << refp->prettyNameQ() << "' owner '" << ownerModp->prettyNameQ()
                            << "' does not match target owner '" << tagp->m_ownerModName
                            << "' and has no cell path");
            correctModp = followCellPath(ownerModp, tagp->m_cellPath);
            UINFO(9, "  followCellPath('"
                         << ownerModp->name() << "', '" << tagp->m_cellPath
                         << "') = " << (correctModp ? correctModp->name() : "<null>")
                         << (correctModp ? (correctModp->dead() ? " (DEAD)" : " (live)") : ""));
            UASSERT_OBJ(correctModp && !correctModp->dead()
                            && moduleMatchesOwner(correctModp, tagp->m_ownerModName),
                        refp,
                        "captured ref '" << refp->prettyNameQ() << "' cell path '"
                                         << tagp->m_cellPath << "' did not resolve to live owner '"
                                         << tagp->m_ownerModName << "'");
        }
        UASSERT_OBJ(retargetRefToModule(refp, correctModp), refp,
                    "could not retarget captured "
                        << (tagp->m_kind == VIfaceCaptureTag::Kind::PARAM_TYPE ? "parameter type "
                                                                               : "typedef ")
                        << refp->prettyNameQ() << " in " << correctModp->prettyNameQ());
        refp->user3(true);
        ++fixed;
    });

    return fixed;
}

void V3LinkDotIfaceCapture::verifyNoDeadRefs(const LiveNodes& liveNodes) {
    // Assert: no REFDTYPE in any live module should have typedefp or refDTypep
    // pointing to a dead module.
    for (AstNode* nodep = v3Global.rootp()->modulesp(); nodep; nodep = nodep->nextp()) {
        if (AstNodeModule* const modp = VN_CAST(nodep, NodeModule)) {
            if (modp->dead()) continue;
            modp->foreach([&](AstRefDType* refp) {
                if (refp->typedefp()) {
                    UASSERT_OBJ(liveNodes.count(refp->typedefp()), refp,
                                "REFDTYPE '" << refp->prettyNameQ() << "' in live module '"
                                             << modp->prettyNameQ()
                                             << "' has a dangling typedefp");
                    AstNodeModule* const ownerModp
                        = findOwnerModuleIfLive(refp->typedefp(), liveNodes);
                    UASSERT_OBJ(!ownerModp || !ownerModp->dead(), refp,
                                "REFDTYPE '" << refp->prettyNameQ() << "' in live module '"
                                             << modp->prettyNameQ()
                                             << "' has typedefp pointing to dead module '"
                                             << ownerModp->prettyNameQ() << "'");
                }
                if (refp->refDTypep()) {
                    UASSERT_OBJ(liveNodes.count(refp->refDTypep()), refp,
                                "REFDTYPE '" << refp->prettyNameQ() << "' in live module '"
                                             << modp->prettyNameQ()
                                             << "' has a dangling refDTypep");
                    AstNodeModule* const ownerModp
                        = findOwnerModuleIfLive(refp->refDTypep(), liveNodes);
                    UASSERT_OBJ(!ownerModp || !ownerModp->dead(), refp,
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
                    UASSERT_OBJ(liveNodes.count(refp->typedefp()), refp,
                                "REFDTYPE '" << refp->prettyNameQ()
                                             << "' in type table has a dangling typedefp");
                    AstNodeModule* const ownerModp
                        = findOwnerModuleIfLive(refp->typedefp(), liveNodes);
                    UASSERT_OBJ(!ownerModp || !ownerModp->dead(), refp,
                                "REFDTYPE '"
                                    << refp->prettyNameQ()
                                    << "' in type table has typedefp pointing to dead module '"
                                    << ownerModp->prettyNameQ() << "'");
                }
                if (refp->refDTypep()) {
                    UASSERT_OBJ(liveNodes.count(refp->refDTypep()), refp,
                                "REFDTYPE '" << refp->prettyNameQ()
                                             << "' in type table has a dangling refDTypep");
                    AstNodeModule* const ownerModp
                        = findOwnerModuleIfLive(refp->refDTypep(), liveNodes);
                    UASSERT_OBJ(!ownerModp || !ownerModp->dead(), refp,
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

    // Snapshot the tree to guard every legacy cross-link inspection below.
    const LiveNodes liveNodes = collectLiveNodes();

    // Resolve live captured refs from stable path metadata before inspecting
    // any inherited target pointers, which may refer to replaced template nodes.
    const int capturedFixed = resolveCapturedRefs();
    UINFO(4, "finalizeIfaceCapture: structurally resolved " << capturedFixed << " captured refs");

    const int typeTableFixed = fixDeadRefsInTypeTable(liveNodes);
    const int moduleFixed = fixDeadRefsInModules(liveNodes);
    UINFO(4, "finalizeIfaceCapture: fixed " << typeTableFixed << " in type table, " << moduleFixed
                                            << " in modules (dead refs)");

    if (debug() >= 9) dumpEntries("after finalizeIfaceCapture");

    // Emit statistics for --stats
    V3Stats::addStat("IfaceCapture, Captured refs", s_tags.size());
    V3Stats::addStat("IfaceCapture, Dead refs fixed in type table", typeTableFixed);
    V3Stats::addStat("IfaceCapture, Dead refs fixed in modules", moduleFixed);
    V3Stats::addStat("IfaceCapture, Captured refs resolved", capturedFixed);

    // Independent debug-only audit of the repairs above; kept separate from the
    // repair traversal so it can catch omissions in that repair.
    if (debug() >= 9) verifyNoDeadRefs(liveNodes);
    // Drop every tag before its record is freed.
    v3Global.rootp()->foreach([](AstRefDType* refp) { refp->captureTagp(nullptr); });
    reset();
}
