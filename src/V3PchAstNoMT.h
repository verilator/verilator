// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// Code available from: https://verilator.org
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// DESCRIPTION: Verilator: Precompilable header of V3Ast, non-multithreaded
//
//*************************************************************************

#ifndef VERILATOR_V3PCHASTNOMT_H_
#define VERILATOR_V3PCHASTNOMT_H_

#ifdef VL_PCH_INCLUDED
#error "Including multiple V3Pch*.h flavors"
#endif
#define VL_PCH_INCLUDED

#define VL_MT_DISABLED_CODE_UNIT 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Broken.h"
#include "V3Error.h"
#include "V3FileLine.h"
#include "V3FunctionTraits.h"
#include "V3Global.h"
#include "V3Mutex.h"
#include "V3Number.h"
#include "V3Options.h"
#include "V3StdFuture.h"
#include "V3String.h"
#include "V3ThreadSafety.h"

#include <algorithm>
#include <map>
#include <utility>

#endif  // Guard
