#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_make_gmake=False, verilator_make_cmake=True)

if not test.have_cmake:
    test.skip("cmake is not installed")

cmakecache = test.obj_dir + "/CMakeCache.txt"
if not os.path.exists(cmakecache):
    test.error(cmakecache + " does not exist")

test.execute()

test.passes()
