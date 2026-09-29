#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.pli_filename = "t/t_vpi_dump.cpp"

# --savable excludes --timing, so the harness drives the clock
test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=[
                 "--exe --vpi --public-flat-rw --savable --no-l2name", "-CFLAGS -DTEST_SAVABLE",
                 test.pli_filename, "t/TestVpiMain.cpp"
             ],
             make_flags=['CPPFLAGS_ADD=-DVL_NO_LEGACY'])

# Each restore returns cyc to its value at the save, so the stimulus after it replays. The
# second save follows a bus write to ctrl_r that nothing has read since.
test.execute(all_run_flags=[
    "+dump_values", "+dump_clock=t.clk:5", "+dump_trigger=t.cyc", "+dump_put=8:t.ctrl_r:0c0c0001",
    "+dump_put=9:t.ctrl_r:0c0c0002", "+dump_save=10", "+dump_put=10:t.ctrl_r:0c0c0003",
    "+dump_restore=11", "+dump_save=12", "+dump_restore=14", "+dump_put=15:t.cnt:06",
    "+dump_put=15:t.flag_a:0", "+dump_restore=16"
],
             expect_filename=test.golden_filename)

test.passes()
