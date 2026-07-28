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

# Corrupted replies: error instead of model, junk before it, junk status, death after status
# Modes that desync the session respawn it, so the injection repeats on the next call
for mode, tamper_at, npass in (('err_reply', '1', 'NPASS=4'), ('garbage_reply', '2', 'NPASS=3'),
                               ('garbage_status', '3', 'NPASS=3'), ('epipe_at', '3', 'NPASS=3')):
    logfile = test.obj_dir + "/vlt_sim_" + mode + ".log"
    test.execute(logfile=logfile,
                 run_env='VERILATOR_SOLVER=' + test.t_dir + '/randomize_solver_tamper.py TAMPER=' +
                 mode + ' TAMPER_AT=' + tamper_at)
    test.file_grep(logfile, npass)

test.file_grep(test.obj_dir + "/vlt_sim_epipe_at.log", r'Solver died; restarting it')

test.passes()
