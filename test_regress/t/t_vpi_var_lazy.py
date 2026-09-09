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

test.top_filename = "t/t_vpi_var.v"
test.pli_filename = "t/t_vpi_var.cpp"

# Every signal here is individually marked public_flat*, so --vpi-lazy must retain them all.
test.compile(make_top_shell=False,
             make_main=False,
             make_pli=True,
             sim_time=2100,
             v_flags2=["+define+USE_VPI_NOT_DPI"],
             verilator_flags2=[
                 "-Wno-SYMRSVDWORD --exe --vpi --vpi-lazy --no-l2name", test.pli_filename
             ])

test.execute(use_libvpi=True,
             all_run_flags=['+PLUS +INT=1234 +STRSTR'],
             expect_filename="t/t_vpi_var.out")

test.passes()
