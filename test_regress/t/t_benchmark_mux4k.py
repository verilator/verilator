#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(v_flags2=["--stats", test.wno_unopthreads_for_few_cores])

test.execute()

# Check netlist was NOT released on shutdown
test.file_grep_not(test.stats, r"Stage, Elapsed time \(sec\), \d+_released")

test.passes()
