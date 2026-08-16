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

# Reply index picks which reply the runtime is waiting on when the solver goes
runs = [
    ('die_at', 3, 2),  # soft constraint and diversity assumption replies
    ('die_at', 10, 3),  # model and unsat core replies
    ('mute_at', 3, 2),  # solver stops answering but keeps running
]

for mode, at, npass in runs:
    logfile = test.obj_dir + '/sim_' + mode + '_' + str(at) + '.log'
    test.execute(logfile=logfile,
                 run_env='VERILATOR_SOLVER="' + test.t_dir + '/randomize_solver_tamper.py" ' +
                 'TAMPER=' + mode + ' TAMPER_AT=' + str(at))
    test.file_grep(logfile, r'NPASS=' + str(npass) + r'\n')

test.passes()
