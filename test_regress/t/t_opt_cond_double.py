#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile()

test.execute()

for filename in test.glob_some(test.obj_dir + "/" + test.vm_prefix + "___024root*.cpp"):
    test.file_grep_not(filename, r'// $c expression at')
test.file_grep_not(test.obj_dir + "/" + test.vm_prefix + "___024root__0__Slow.cpp", r'\?')
test.file_grep(test.obj_dir + "/" + test.vm_prefix + "___024root__0__Slow.cpp",
               r'VL_WRITEF_NX\(\"1.234000\\n\*-\* All Finished \*-\*\\n\"')

test.passes()
