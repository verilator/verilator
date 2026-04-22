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
test.fourstate_capable = False

# Keep this paired with t_cover_hier_noinline.py: both tests use the same
# source and golden so inline and no-inline coverage are checked for parity.
test.compile(top_filename="t/t_cover_hier.v",
             v_flags2=[
                 "+define+INLINE_CHILD --assert --coverage-line --coverage-user "
                 "t/t_cover_hier.cpp"
             ],
             verilator_flags2=["--exe --top-module t"],
             make_flags=['CPPFLAGS_ADD=-DTEST_OBJ_DIR="' + test.obj_dir + '"'],
             make_main=False)

test.execute()

test.files_identical_sorted(test.obj_dir + "/coverage.dat", "t/t_cover_hier.out")

test.passes()
