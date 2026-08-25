#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_randomize_solver_fault.v"

if not test.have_solver:
    test.skip("No constraint solver installed")

test.compile()

# Every scenario acts on the first reply of its kind, so the counts do not
# depend on how many replies a particular solver sends per randomize() call.
# once=True acts one time in the whole run; the restarted solver then serves
# every later call. once=False acts again in every solver, so the runtime gives
# up and disables randomization.
runs = [
    ('die_at', True, 11),  # solver exits with a model reply pending
    ('die_status_at', True, 11),  # solver exits with a status pending
    ('mute_at', True, 11),  # solver stays running but stops answering
    ('garbage_at', True, 11),  # solver answers, but not with an S-expression
    ('garbage_at', False, 0),  # every solver answers the same way
]

for mode, once, npass in runs:
    tag = mode + ('_once' if once else '_always')
    logfile = test.obj_dir + '/sim_' + tag + '.log'
    latch = test.obj_dir + '/' + tag + '.latch'
    if os.path.exists(latch):
        os.unlink(latch)
    test.execute(logfile=logfile,
                 run_env='VERILATOR_SOLVER="' + test.t_dir + '/randomize_solver_tamper.py" ' +
                 'TAMPER=' + mode + ' TAMPER_AT=1 ' +
                 ('TAMPER_ONCE="' + latch + '" ' if once else ''))
    test.file_grep(logfile, r'NPASS=(\d+)', npass)
    test.file_grep(logfile, r'Solver died')

test.file_grep(test.obj_dir + '/sim_garbage_at_always.log', r'Solver failed repeatedly')

test.passes()
