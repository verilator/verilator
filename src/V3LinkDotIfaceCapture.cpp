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

#include "V3LinkDotIfaceCapture.h"

#include "V3Error.h"
#include "V3Global.h"

#include <unordered_map>

VL_DEFINE_DEBUG_FUNCTIONS;

V3LinkDotIfaceCapture::CapturedMap V3LinkDotIfaceCapture::s_map{};

bool V3LinkDotIfaceCapture::s_enabled = true;

AstNodeModule* V3LinkDotIfaceCapture::findOwnerModule(AstNode* nodep) {
    for (AstNode* curp = nodep; curp; curp = curp->backp()) {
        if (AstNodeModule* const modp = VN_CAST(curp, NodeModule)) return modp;
    }
    return nullptr;
}

bool V3LinkDotIfaceCapture::finalizeCapturedEntry(CapturedMap::iterator it, const char* reasonp) {
    CapturedIfaceTypedef& entry = it->second;
    AstRefDType* const pendingRefp = entry.pendingClonep;
    AstTypedef* const reboundTypedefp = entry.typedefp;
    if (!pendingRefp || !reboundTypedefp) return false;
    if (entry.cellp) pendingRefp->user2p(entry.cellp);
    pendingRefp->user3(false);
    pendingRefp->typedefp(reboundTypedefp);
    entry.pendingClonep = nullptr;
    return true;
}

void V3LinkDotIfaceCapture::add(AstRefDType* refp, AstCell* cellp, AstNodeModule* ownerModp, AstTypedef* typedefp, AstNodeModule* typedefOwnerModp, AstVar* ifacePortVarp) {
    if (!refp) return;

    if(!typedefp) typedefp = refp->typedefp();

    if (!typedefOwnerModp && typedefp)
        typedefOwnerModp = findOwnerModule(typedefp);

    s_map[refp] = CapturedIfaceTypedef{refp, cellp, ownerModp, typedefp, typedefOwnerModp, nullptr, ifacePortVarp};
}

const V3LinkDotIfaceCapture::CapturedIfaceTypedef* V3LinkDotIfaceCapture::find(const AstRefDType* refp) {
    if (!refp) return nullptr;
    const auto it = s_map.find(refp);
    if (VL_UNLIKELY(it == s_map.end())) return nullptr;
    return &it->second;
}

bool V3LinkDotIfaceCapture::erase(const AstRefDType* refp) {
    if (!refp) return false;
    const auto it = s_map.find(refp);
    if (it == s_map.end()) return false;
    s_map.erase(it);
    return true;
}

std::size_t V3LinkDotIfaceCapture::size() {
  return s_map.size();
}

bool V3LinkDotIfaceCapture::replaceRef(const AstRefDType* oldRefp, AstRefDType* newRefp) {
    if (!oldRefp || !newRefp) return false;
    const auto it = s_map.find(oldRefp);
    if (it == s_map.end()) return false;
    auto entry = it->second;
    entry.refp = newRefp;
    s_map.erase(it);
    s_map.emplace(newRefp, entry);
    return true;
}

bool V3LinkDotIfaceCapture::replaceTypedef(const AstRefDType* refp, AstTypedef* newTypedefp) {
    if (!refp || !newTypedefp) return false;
    auto it = s_map.find(refp);
    if (it == s_map.end()) return false;
    it->second.typedefp = newTypedefp;
    it->second.typedefOwnerModp = findOwnerModule(newTypedefp);
    finalizeCapturedEntry(it, "typedef clone");
    return true;
}

void V3LinkDotIfaceCapture::propagateClone(const AstRefDType* origRefp, AstRefDType* newRefp) {
    if (!origRefp || !newRefp) return;
    auto it = s_map.find(origRefp);
    if (it == s_map.end()) {
        const string msg
            = string{"iface capture propagateClone missing entry for orig="} + cvtToStr(origRefp);
        v3fatalSrc(msg);
    }
    CapturedIfaceTypedef& entry = it->second;

    if (entry.cellp) newRefp->user2p(entry.cellp);
    newRefp->user3(false);
    entry.pendingClonep = newRefp;

    // If replaceTypedef was already called (interface cloned before module),
    // entry.typedefp will differ from the original RefDType's typedef.
    // In that case, finalize now with the updated typedef.
    if (entry.typedefp && origRefp->typedefp() && entry.typedefp != origRefp->typedefp()) {
        finalizeCapturedEntry(it, "ref clone");
    }
}

template <typename FilterFn, typename Fn>
void V3LinkDotIfaceCapture::forEachImpl(FilterFn&& filter, Fn&& fn) {
    std::vector<const AstRefDType*> keys;
    keys.reserve(s_map.size());
    for (const auto& kv : s_map) keys.push_back(kv.first);

    for (const AstRefDType* key : keys) {
        const auto it = s_map.find(key);
        if (it == s_map.end()) continue;

        CapturedIfaceTypedef& entry = it->second;
        if (entry.cellp && entry.refp && entry.refp->user2p() != entry.cellp) {
            entry.refp->user2p(entry.cellp);
        }
        if (!filter(entry)) continue;
        fn(entry);
    }
}

void V3LinkDotIfaceCapture::forEach(const std::function<void(const CapturedIfaceTypedef&)>& fn) {
    if (!fn) return;
    forEachImpl([](const CapturedIfaceTypedef&) { return true; }, fn);
}

void V3LinkDotIfaceCapture::forEachOwned(const AstNodeModule* ownerModp, const std::function<void(const CapturedIfaceTypedef&)>& fn) {
    if (!ownerModp || !fn) return;
    forEachImpl(
        [ownerModp](const CapturedIfaceTypedef& e) {
            return e.ownerModp == ownerModp || e.typedefOwnerModp == ownerModp;
        },
        fn);
}
