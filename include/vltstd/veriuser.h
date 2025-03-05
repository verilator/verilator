// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Code available from: https://verilator.org
//
// Copyright 2009-2025 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=========================================================================
///
/// \file
/// \brief Verilated user tf_routines
///
/// This file contains routines to interface user VPI/PLI C++ code with
/// Verilator.  Traditionally the veriuser.h code has been used for only
/// tf_ routines, which verilator does not implement, so this file is
/// empty.
///
/// User code relying on tf_ routines should migrate to VPI (vpi_user.h) or
/// DPI (svdpi.h) routines.
///
/// This file is only provided for backwards compatibility for applications
/// which include veriuser.h even though they use only vpi_ or dpi_
/// routines.
///
//=========================================================================

// Intentionally empty, see above.
