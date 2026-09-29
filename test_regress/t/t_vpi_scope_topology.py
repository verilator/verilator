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

# $random and $time are impure, as is obs, which reads them; and any values with
# cyc_a ^ cyc_b == cyc_d close the comb cycle. None of these are dumped.
test.execute(use_libvpi=True,
             all_run_flags=[
                 "+dump_values", "+dump_at=t.clk:0", "+dump_skip=t.rndc", "+dump_skip=t.tstamp",
                 "+dump_skip=t.obs", "+dump_skip=t.cyc_a", "+dump_skip=t.cyc_b"
             ],
             expect_filename=test.golden_filename)

test.passes()
