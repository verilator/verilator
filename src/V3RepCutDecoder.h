// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Native decoder cache recognition
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//*************************************************************************

#ifndef VERILATOR_V3REPCUTDECODER_H_
#define VERILATOR_V3REPCUTDECODER_H_

#include "config_build.h"
#include "verilatedos.h"

class AstAlways;
class AstInitialStatic;

namespace V3RepCut {
// Recognize only marked, private DFG decoder caches with their original
// non-suspending update/initialization shapes. Native scheduling retains them.
bool isNativeDecoderUpdate(const AstAlways* nodep) VL_MT_DISABLED;
bool isNativeDecoderInitialization(const AstInitialStatic* nodep) VL_MT_DISABLED;
}  // namespace V3RepCut

#endif  // Guard
