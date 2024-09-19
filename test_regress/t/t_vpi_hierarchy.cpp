// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2010-2011 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************


#include <iostream>
#include <string_view>

#include "vpi_user.h"

void iterate(vpiHandle root_handle) {
    vpiHandle module_iter = vpi_iterate(vpiModule, root_handle);
    for (vpiHandle handle = vpi_scan(module_iter); handle != nullptr;
         handle = vpi_scan(module_iter)) {
        iterate(handle);
    }

    vpiHandle reg_iter = vpi_iterate(vpiReg, root_handle);
    for (vpiHandle handle = vpi_scan(reg_iter); handle != nullptr;
         handle = vpi_scan(reg_iter)) {
        const std::string_view name = vpi_get_str(vpiFullName, handle);
        std::cout << name << std::endl;
    }
}
