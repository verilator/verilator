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

test.compile(make_top_shell=False,
             make_main=False,
             make_pli=True,
             verilator_flags2=[
                 "--exe --vpi --timing --public-flat-rw --no-l2name", test.pli_filename,
                 "t/TestVpiMain.cpp"
             ],
             make_flags=['CPPFLAGS_ADD=-DVL_NO_LEGACY'])

test.execute(
    use_libvpi=True,
    all_run_flags=[
        "+dump_values", "+dump_cb=t.s_comb", "+dump_trigger=t.cyc", "+dump_put=2:t.in_a:11",
        "+dump_put=t.watched=0x0f:t.cin:40", "+dump_put=4:t.s:22", "+dump_put=4:t.in_a:33",
        "+dump_put=4:t.mem[1]:44", "+dump_put=4:t.r:real=4.0",
        "+dump_put=4:t.str:str=longer_than_any_short_string_buffer", "+dump_put=5:t.s:55:rw",
        "+dump_put=6:t.s:77:inertial", "+dump_put=7:t.f:55:force", "+dump_put=8:t.f:66:release",
        "+dump_put=9:t.s:5c", "+dump_put=11:t.init_only:31", "+dump_put=11:t.undriven:32",
        "+dump_put=11:t.once:33", "+dump_put=11:t.part:a3"
    ],
    expect_filename=test.golden_filename)

test.passes()
