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

# Shadows reset as their signals would, so a read before the first eval() matches
test.execute(use_libvpi=True,
             all_run_flags=[
                 "+verilator+rand+reset+2", "+verilator+seed+7", "+t_vpi_dump_start=t.a",
                 "+t_vpi_dump_start=t.b", "+t_vpi_dump_start=t.pre_qc",
                 "+t_vpi_dump_start=t.pre_ic", "+t_vpi_dump_start=t.u_pre.x",
                 "+t_vpi_dump_start=t.u_pre.y"
             ],
             expect_filename=test.golden_filename)

test.passes()
