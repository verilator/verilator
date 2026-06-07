#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2025 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

# Compile with --binary but WITHOUT --vpi.
# Passing +verilator+vpi+ at runtime should emit a warning, not load anything.
test.compile(top_filename='t/t_flag_main.v', verilator_flags2=["--binary"])

# Without --vpi there is no loader, so the plusarg is ignored with a warning (checked via
# the golden .out).  The plusarg value is fixed, so the warning text is portable.
test.execute(all_run_flags=["+verilator+vpi+/nonexistent.so"],
             check_finished=True,
             expect_filename=test.golden_filename)

test.passes()
