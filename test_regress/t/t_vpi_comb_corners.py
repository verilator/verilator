#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')
test.pli_filename = "t/t_vpi_dump.cpp"

test.compile(make_top_shell=False,
             make_main=False,
             make_pli=True,
             verilator_flags2=[
                 "--exe --vpi --timing --public-flat-rw --no-l2name", test.pli_filename,
                 "t/TestVpiMain.cpp"
             ],
             make_flags=['CPPFLAGS_ADD=-DVL_NO_LEGACY'])

# Multiply-driven and impure signals resolve by how the model was optimised, so are not
# dumped
test.execute(use_libvpi=True,
             all_run_flags=[
                 "+dump_values", "+dump_skip=t.vec", "+dump_skip=t.obs_impureidx",
                 "+dump_skip=t.w", "+dump_skip=t.u_wdrv.y", "+dump_trigger=t.cyc",
                 "+dump_put=8:t.orphan:2a", "+dump_put=9:t.handle:2a",
                 "+dump_put=14:t.frc:55:force", "+dump_put=16:t.frc:55:release"
             ],
             expect_filename=test.golden_filename)

test.passes()
