
// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Interface typedef capture helper: stores (refp, typedefp,
//    cellp, owners, pendingClone) so LinkDot can rebind refs when symbol
//    lookup fails, and V3Param clones can retarget typedefs without legacy
//    paths.
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

#ifndef VERILATOR_V3LINKDOTIFACECAPTURE_H_
#define VERILATOR_V3LINKDOTIFACECAPTURE_H_

#include "config_build.h"

#include <functional>
#include <cstddef>

class AstCell;
class AstNodeModule;
class AstRefDType;
class AstTypedef;
class VSymEnt;

namespace LinkDotIfaceCapture {

struct CapturedIfaceTypedef final {
    AstRefDType* refp = nullptr;
    AstCell* cellp = nullptr;
    // Module where the RefDType lives
    AstNodeModule* ownerModp = nullptr;
    VSymEnt* ownerSymp = nullptr;
    // Typedef definition being referenced
    AstTypedef* typedefp = nullptr;
    // Interface/module that owns typedefp
    AstNodeModule* typedefOwnerModp = nullptr;
    // Cloned RefDType awaiting typedef rebinding
    AstRefDType* pendingClonep = nullptr;
};

void enable(bool flag);
bool enabled();

void reset();
void add(AstRefDType* refp, AstCell* cellp, AstNodeModule* ownerModp, VSymEnt* ownerSymp,
         AstTypedef* typedefp = nullptr, AstNodeModule* typedefOwnerModp = nullptr);
void add(const CapturedIfaceTypedef& entry);
bool contains(const AstRefDType* refp);
const CapturedIfaceTypedef* find(const AstRefDType* refp);
AstTypedef* getCapturedTypedef(const AstRefDType* refp);
void forEach(const std::function<void(const CapturedIfaceTypedef&)>& fn);
bool replaceRef(const AstRefDType* oldRefp, AstRefDType* newRefp);
bool replaceTypedef(const AstRefDType* refp, AstTypedef* newTypedefp);
bool erase(const AstRefDType* refp);
std::size_t size();

void propagateClone(const AstRefDType* origRefp, AstRefDType* newRefp);


}  // namespace LinkDotIfaceCapture

#endif  // VERILATOR_V3LINKDOTIFACECAPTURE_H_
