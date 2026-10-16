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
test.top_filename = "t/t_vpi_comb_corners.v"
test.golden_filename = "t/t_vpi_comb_corners.out"
test.pli_filename = "t/t_vpi_dump.cpp"

# --x-initial unique: freshness stamps must start stale rather than seeded with garbage.
test.compile(make_top_shell=False,
             make_main=False,
             make_pli=True,
             verilator_flags2=[
                 "--exe --vpi --timing --vpi-lazy --no-l2name --stats --x-initial unique",
                 test.pli_filename, "t/TestVpiMain.cpp"
             ],
             make_flags=['CPPFLAGS_ADD=-DVL_NO_LEGACY'])

# Shadows reset as their signals would, so a read before the first eval() matches
test.execute(use_libvpi=True,
             all_run_flags=[
                 "+verilator+rand+reset+2", "+verilator+seed+7", "+t_vpi_dump_start=t.a",
                 "+t_vpi_dump_start=t.b", "+t_vpi_dump_start=t.pre_qc",
                 "+t_vpi_dump_start=t.pre_ic", "+t_vpi_dump_start=t.u_pre.x",
                 "+t_vpi_dump_start=t.u_pre.y"
             ],
             expect_filename=test.golden_filename)

test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 63)
test.file_grep(test.stats, r'VPI, lazy boundary storage pinned\s+(\d+)', 1)
test.file_grep(test.stats, r'Decompose, unpacked variables split\s+(\d+)', 6)

test.passes()
