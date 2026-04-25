#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('dist')

# VERILATOR_RUNNING is the wrapper's re-entry sentinel. Setting it before
# the first invocation simulates the misconfiguration that used to fork-bomb
# (e.g. VERILATOR_BIN or PATH resolving back to bin/verilator). The wrapper
# must abort with a clear error instead of recursing.
os.environ['VERILATOR_RUNNING'] = '1'

test.run(fails=True,
         cmd=[os.environ["VERILATOR_ROOT"] + "/bin/verilator", "--version"],
         logfile=test.run_log_filename,
         expect_filename=test.golden_filename)

test.passes()
