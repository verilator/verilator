#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('dist')

root = ".."

if not os.path.exists(root + "/.git"):
    test.skip("Not in a git repository")

test.run(cmd=[
    "cd " + root + "/src/obj_dbg && " + os.environ['MAKE'] +
    " -j 4 -k -f ../Makefile_obj VL_NOOPT=1 header_cc"
],
         check_finished=False)

test.passes()
