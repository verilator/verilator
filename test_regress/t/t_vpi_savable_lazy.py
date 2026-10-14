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
test.top_filename = "t/t_vpi_savable.v"
test.golden_filename = "t/t_vpi_savable.out"
test.pli_filename = "t/t_vpi_dump.cpp"

# --savable: a restore must reach reconstructed rows as it does stored ones. It excludes
# --timing, so the harness drives the clock.
test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=[
                 "--exe --vpi --vpi-lazy --savable --no-l2name --stats", "-CFLAGS -DT_VPI_SAVABLE",
                 test.pli_filename, "t/TestVpiMain.cpp"
             ],
             make_flags=['CPPFLAGS_ADD=-DVL_NO_LEGACY'])

test.execute(expect_filename=test.golden_filename)

test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 9)

test.passes()
