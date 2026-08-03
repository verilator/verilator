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

test.compile(verilator_flags2=['+define+T_UNSAT'])

# Genuine UNSAT with wrapped replies: the unsat-core path consumes its whole reply
test.execute(run_env='VERILATOR_SOLVER=' + test.t_dir +
             '/randomize_solver_tamper.py TAMPER=multiline')

test.file_grep(test.run_log_filename, r'NFAIL=5')
test.file_grep(test.run_log_filename, r'All Finished')

# Error instead of the unsat-core reply
logfile = test.obj_dir + "/vlt_sim_err.log"
test.execute(logfile=logfile,
             run_env='VERILATOR_SOLVER=' + test.t_dir +
             '/randomize_solver_tamper.py TAMPER=err_reply TAMPER_AT=1')
test.file_grep(logfile, r'Solver reported an error')
test.file_grep(logfile, r'NFAIL=5')

# No solver at all: warn once, then disable after repeated spawn failures
logfile = test.obj_dir + "/vlt_sim_nosolver.log"
test.execute(logfile=logfile, run_env='VERILATOR_SOLVER=/nonexistent_solver_binary')
test.file_grep(logfile, r'Unable to communicate')
test.file_grep(logfile, r'randomization disabled')
test.file_grep(logfile, r'NFAIL=5')

test.passes()
