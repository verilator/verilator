#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')

# Use --debug-protect to assist debug

test.compile()

test.execute()

if test.vlt_all:
    # Check for unused structs in any outputs
    for filename in test.glob_some(test.obj_dir + "/*.[ch]*"):
        test.file_grep_not(filename, r'useless')

test.passes()
