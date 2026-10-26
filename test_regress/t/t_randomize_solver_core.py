#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

if not test.have_solver:
    test.skip("No constraint solver installed")

test.compile()

# The core is read from a second solve of the same constraints, so the only
# statuses here are that solve's and the one it repeats
test.execute()
test.file_grep(test.run_log_filename, r'NFAIL=(\d+)', 3)
test.file_grep(test.run_log_filename, r'Unsatisfied constraint')

# A solver that does not repeat its unsat leaves the constraints unnamed
logfile = test.obj_dir + '/sim_unsat_recheck.log'
test.execute(logfile=logfile,
             run_env='VERILATOR_SOLVER="' + test.t_dir + '/randomize_solver_tamper.py" ' +
             'TAMPER=unsat_recheck TAMPER_AT=1')
test.file_grep(logfile, r'NFAIL=(\d+)', 3)
test.file_grep_not(logfile, r'Unsatisfied constraint')

test.passes()
