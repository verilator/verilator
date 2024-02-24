// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Configure source; system configuration
//
// This file is part of Verilator.
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

//**********************************************************************
//**** Version and host name

#include "config_package.h"

//**********************************************************************
//**** Functions

//**********************************************************************
//**** Headers

//**********************************************************************
//**** Default environment

// Set defines to defaults for environment variables
// If set to "", this default is ignored and the user is expected
// to set them at Verilator runtime.

// clang-format off
#ifndef DEFENV_SYSTEMC
# define DEFENV_SYSTEMC ""
#endif
#ifndef DEFENV_SYSTEMC_ARCH
# define DEFENV_SYSTEMC_ARCH ""
#endif
#ifndef DEFENV_SYSTEMC_INCLUDE
# define DEFENV_SYSTEMC_INCLUDE ""
#endif
#ifndef DEFENV_SYSTEMC_LIBDIR
# define DEFENV_SYSTEMC_LIBDIR ""
#endif
#ifndef DEFENV_VERILATOR_ROOT
# define DEFENV_VERILATOR_ROOT ""
#endif
// clang-format on

//**********************************************************************
//**** Compile options

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <string>

#include <sys/types.h>

// Avoid needing std:: prefixes on some very common items
using string = std::string;
using std::cout;
using std::endl;
using namespace std::literals;  // "<std::string literal>"s; see SF.7 core guideline

//**********************************************************************
//**** OS and compiler specifics

#include "verilatedos.h"
