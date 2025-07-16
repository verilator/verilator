#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = 't/t_EXAMPLE.v'

test.run(cmd=["perl", os.environ["VERILATOR_ROOT"] + "/bin/verilator", "--threads-max-mtasks 0"],
         logfile=test.run_log_filename,
         fails=True,
         expect_filename=test.golden_filename,
         verilator_run=True)

test.passes()
