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
    test.file_grep(logfile, r'Solver died or replied unreadably')

test.file_grep(test.obj_dir + '/sim_garbage_at_always.log', r'Solver failed repeatedly')

# A solver that never starts is not restarted, so it is never reported as dead
logfile = test.obj_dir + '/sim_nosolver.log'
test.execute(logfile=logfile, run_env='VERILATOR_SOLVER=someimaginarysolver ')
test.file_grep(logfile, r'NPASS=(\d+)', 0)
test.file_grep(logfile, r'Unable to communicate with SAT solver')
test.file_grep_not(logfile, r'Solver died')

# One rejected command must not count against the solver: the reply was
# complete, so the session stays and later calls keep working
logfile = test.obj_dir + '/sim_err_once.log'
latch = test.obj_dir + '/err_once.latch'
if os.path.exists(latch):
    os.unlink(latch)
test.execute(logfile=logfile,
             run_env='VERILATOR_SOLVER="' + test.t_dir + '/randomize_solver_tamper.py" ' +
             'TAMPER=err_once TAMPER_AT=2 TAMPER_ONCE="' + latch + '" ')
test.file_grep(logfile, r'NPASS=(\d+)', 11)
test.file_grep_not(logfile, r'Solver failed repeatedly')
test.file_grep_not(logfile, r'Solver died')

# A command rejected ahead of a status fails only that call, and the session stays
logfile = test.obj_dir + '/sim_err_extra.log'
latch = test.obj_dir + '/err_extra.latch'
if os.path.exists(latch):
    os.unlink(latch)
test.execute(logfile=logfile,
             run_env='VERILATOR_SOLVER="' + test.t_dir + '/randomize_solver_tamper.py" ' +
             'TAMPER=err_extra TAMPER_AT=2 TAMPER_ONCE="' + latch + '" ')
test.file_grep(logfile, r'NPASS=(\d+)', 11)
test.file_grep_not(logfile, r'Solver died')

# A solver that rejects a command and then stops answering is replaced
logfile = test.obj_dir + '/sim_err_mute.log'
latch = test.obj_dir + '/err_mute.latch'
if os.path.exists(latch):
    os.unlink(latch)
test.execute(logfile=logfile,
             run_env='VERILATOR_SOLVER="' + test.t_dir + '/randomize_solver_tamper.py" ' +
             'TAMPER=err_mute TAMPER_AT=2 TAMPER_ONCE="' + latch + '" ')
test.file_grep(logfile, r'NPASS=(\d+)', 11)
test.file_grep(logfile, r'Solver died or replied unreadably')

# A solver that rejects a phase diversity round and then stops answering fails that
# call, leaving its variables alone, and is replaced
logfile = test.obj_dir + '/sim_phase_mute.log'
latch = test.obj_dir + '/phase_mute.latch'
if os.path.exists(latch):
    os.unlink(latch)
test.execute(logfile=logfile,
             run_env='VERILATOR_SOLVER="' + test.t_dir + '/randomize_solver_tamper.py" ' +
             'TAMPER=err_mute TAMPER_AT=9 TAMPER_ONCE="' + latch + '" ')
test.file_grep(logfile, r'NPASS=(\d+)', 11)
test.file_grep(logfile, r'Solver died or replied unreadably')

# A reply the unigen2 sampler can't read while it measures the solution space.
# Falls back to the plain solve, so every randomize still succeeds
logfile = test.obj_dir + '/sim_ug2_estimate.log'
test.execute(logfile=logfile,
             run_env='VERILATOR_SOLVER="' + test.t_dir + '/randomize_solver_tamper.py" ' +
             'TAMPER=model_trunc TAMPER_AT=8 ')
test.file_grep(logfile, r'NPASS=(\d+)', 12)

# A value the sampler can't parse while it measures the solution space.
# Falls back to the plain solve, so every randomize still succeeds
logfile = test.obj_dir + '/sim_ug2_value.log'
test.execute(logfile=logfile,
             run_env='VERILATOR_SOLVER="' + test.t_dir + '/randomize_solver_tamper.py" ' +
             'TAMPER=bad_base TAMPER_AT=11 ')
test.file_grep(logfile, r'NPASS=(\d+)', 12)

# A status the sampler can't use while it measures the solution space, likewise
logfile = test.obj_dir + '/sim_ug2_status.log'
test.execute(logfile=logfile,
             run_env='VERILATOR_SOLVER="' + test.t_dir + '/randomize_solver_tamper.py" ' +
             'TAMPER=err_once TAMPER_AT=15 ')
test.file_grep(logfile, r'NPASS=(\d+)', 12)

# A command rejected at the first status of the sampler's cell enumeration fails it.
# Every randomize still succeeds, and the solver is not restarted
logfile = test.obj_dir + '/sim_ug2_error.log'
latch = test.obj_dir + '/ug2_error.latch'
if os.path.exists(latch):
    os.unlink(latch)
test.execute(logfile=logfile,
             run_env='VERILATOR_SOLVER="' + test.t_dir + '/randomize_solver_tamper.py" ' +
             'TAMPER=err_cell TAMPER_AT=1 TAMPER_ONCE="' + latch + '" ')
test.file_grep(logfile, r'NPASS=(\d+)', 12)
test.file_grep(logfile, r'Solver did not answer with a status')
test.file_grep_not(logfile, r'Solver died')

# A malformed phase value reply fails that one call; later calls still pass
logfile = test.obj_dir + '/sim_phase_value.log'
test.execute(logfile=logfile,
             run_env='VERILATOR_SOLVER="' + test.t_dir + '/randomize_solver_tamper.py" ' +
             'TAMPER=bad_base TAMPER_AT=5 ')
test.file_grep(logfile, r'NPASS=(\d+)', 11)

# A reply naming a variable the sampler didn't ask for.
logfile = test.obj_dir + '/sim_ug2_var.log'
test.execute(logfile=logfile,
             run_env='VERILATOR_SOLVER="' + test.t_dir + '/randomize_solver_tamper.py" ' +
             'TAMPER=unknown_var TAMPER_AT=10 ')
test.file_grep(logfile, r'NPASS=(\d+)', 12)

test.passes()
