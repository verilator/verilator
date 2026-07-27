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
test.top_filename = "t/t_randomize_solver_fault.v"

if not test.have_solver:
    test.skip("No constraint solver installed")

test.compile()

# Error then silence with no timeout: must fail bounded, not hang
test.execute(run_env='VERILATOR_SOLVER=' + test.t_dir +
             '/randomize_solver_tamper.py TAMPER=silent_at TAMPER_AT=2')

test.file_grep(test.run_log_filename, r'Solver reported an error')
test.file_grep(test.run_log_filename, r'randomization disabled')
test.file_grep(test.run_log_filename, r'All Finished')

test.passes()
