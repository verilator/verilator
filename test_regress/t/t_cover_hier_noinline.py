#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3,
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

# Exercise both user and generated coverage in duplicated hierarchy instances;
# the shared golden verifies inline and no-inline modules report the same
# per-hierarchy counts when forcePerInstance is used.
test.compile(top_filename="t/t_cover_hier.v",
             v_flags2=["--assert --coverage-line --coverage-user t/t_cover_hier.cpp"],
             verilator_flags2=["--exe --top-module t"],
             make_flags=['CPPFLAGS_ADD=-DTEST_OBJ_DIR="' + test.obj_dir + '"'],
             make_main=False)

test.execute()

test.files_identical_sorted(test.obj_dir + "/coverage.dat", "t/t_cover_hier.out")

test.passes()
