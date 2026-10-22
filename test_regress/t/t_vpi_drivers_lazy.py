#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

# Not vltmt: the design calls VPI from an always block, which --threads may run off the main thread
test.scenarios('vlt')
test.top_filename = "t/t_vpi_drivers.v"
test.pli_filename = "t/t_vpi_drivers.cpp"

# --vpi-lazy implies --vpi. The split options spread the rebuilds over many functions and files;
# --stats covers the --vpi-lazy statistics. VL_DEBUG, as Makefile_obj sets for non---binary tests, runs the
# runtime's debug assertions.
test.compile(make_top_shell=False,
             verilator_flags2=[
                 "--binary --vpi-lazy --no-l2name --stats --output-split 200"
                 " --output-split-cfuncs 20 --comp-limit-blocks 3 -fno-inline-cfuncs",
                 "-CFLAGS -DT_VPI_DRIVERS_LAZY -CFLAGS -DVL_DEBUG=1",
                 test.pli_filename
             ])

test.execute(all_run_flags=["+verilator+rand+reset+1"], expect_filename=test.golden_filename)

test.passes()
