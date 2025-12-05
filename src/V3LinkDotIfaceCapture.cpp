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

#include "V3Ast.h"
#include "V3Error.h"
#include "V3Global.h"
#include "V3SymTable.h"

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
    AstTypedef* const resolvedTypedefp = typedefp ? typedefp : refp->typedefp();
    AstNodeModule* resolvedTypedefOwner = typedefOwnerModp;
    if (!resolvedTypedefOwner && resolvedTypedefp)
        resolvedTypedefOwner = findOwnerModule(resolvedTypedefp);
    //capturedMap()[refp] = CapturedIfaceTypedef{
    s_map[refp] = CapturedIfaceTypedef{
        refp, cellp, ownerModp, resolvedTypedefp, resolvedTypedefOwner, nullptr, ifacePortVarp};
}

const V3LinkDotIfaceCapture::CapturedIfaceTypedef* V3LinkDotIfaceCapture::find(const AstRefDType* refp) {
    if (!refp) return nullptr;
    auto& map = s_map;
    const auto it = map.find(refp);
    if (VL_UNLIKELY(it == map.end())) return nullptr;
    return &it->second;
}

bool V3LinkDotIfaceCapture::erase(const AstRefDType* refp) {
    if (!refp) return false;
    auto& map = s_map;
    const auto it = map.find(refp);
    if (it == map.end()) return false;
    map.erase(it);
    return true;
}

std::size_t V3LinkDotIfaceCapture::size() {
  return s_map.size();
}

bool V3LinkDotIfaceCapture::replaceRef(const AstRefDType* oldRefp, AstRefDType* newRefp) {
    if (!oldRefp || !newRefp) return false;
    auto& map = s_map;
    const auto it = map.find(oldRefp);
    if (it == map.end()) return false;
    auto entry = it->second;
    entry.refp = newRefp;
    map.erase(it);
    map.emplace(newRefp, entry);
    return true;
}

bool V3LinkDotIfaceCapture::replaceTypedef(const AstRefDType* refp, AstTypedef* newTypedefp) {
    if (!refp || !newTypedefp) return false;
    auto& map = s_map;
    auto it = map.find(refp);
    if (it == map.end()) return false;
    it->second.typedefp = newTypedefp;
    it->second.typedefOwnerModp = findOwnerModule(newTypedefp);
    finalizeCapturedEntry(it, "typedef clone");
    return true;
}

void V3LinkDotIfaceCapture::propagateClone(const AstRefDType* origRefp, AstRefDType* newRefp) {
    if (!origRefp || !newRefp) return;
    auto& map = s_map;
    auto it = map.find(origRefp);
    if (it == map.end()) {
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
    auto& map = s_map;
    std::vector<const AstRefDType*> keys;
    keys.reserve(map.size());
    for (const auto& kv : map) keys.push_back(kv.first);

    for (const AstRefDType* key : keys) {
        const auto it = map.find(key);
        if (it == map.end()) continue;

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


/*
namespace LinkDotIfaceCapture {


template <typename FilterFn, typename Fn>
static void forEachImpl(FilterFn&& filter, Fn&& fn) {
    auto& map = capturedMap();
    std::vector<const AstRefDType*> keys;
    keys.reserve(map.size());
    for (const auto& kv : map) keys.push_back(kv.first);

    for (const AstRefDType* key : keys) {
        const auto it = map.find(key);
        if (it == map.end()) continue;

        CapturedIfaceTypedef& entry = it->second;
        if (entry.cellp && entry.refp && entry.refp->user2p() != entry.cellp) {
            entry.refp->user2p(entry.cellp);
        }
        if (!filter(entry)) continue;
        fn(entry);
    }
}

void forEach(const std::function<void(const CapturedIfaceTypedef&)>& fn) {
    if (!fn) return;
    forEachImpl([](const CapturedIfaceTypedef&) { return true; }, fn);
}

void forEachOwned(const AstNodeModule* ownerModp,
                  const std::function<void(const CapturedIfaceTypedef&)>& fn) {
    if (!ownerModp || !fn) return;
    forEachImpl(
        [ownerModp](const CapturedIfaceTypedef& e) {
            return e.ownerModp == ownerModp || e.typedefOwnerModp == ownerModp;
        },
        fn);
}







}  // namespace LinkDotIfaceCapture
*/