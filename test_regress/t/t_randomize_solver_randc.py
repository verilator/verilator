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
test.top_filename = "t/t_constraint_randc_solve_before.v"

# Fixed-seed fault-injection test: the tamper positions and the pass/fail counts follow
# the permutation each srandom() seed produces, and are re-derived if Verilator's RNG
# usage changes. The seed-independent check of the randc-first draw is the FreshCycle case
# of t_constraint_randc_solve_before.

if not test.have_solver:
    test.skip("No constraint solver installed")

test.compile()

# TAMPER_AT counts one kind of reply from the start of the simulation, per the mode's
# entry in randomize_solver_tamper.py: unknown_once counts status lines, err_reply
# S-expression replies, err_assume unsat-assumptions replies, short_model and bare_hash
# model replies. Status 1 answers the check-sat sent when the session opens. To re-derive
# a constant, run the case's MODE without TAMPER, with VERILATOR_SOLVER set to a wrapper
# that logs the conversation, and count the replies up to the one its comment names.
SOLVER = 'VERILATOR_SOLVER="' + test.t_dir + '/randomize_solver_tamper.py" '


# Each case runs one fault_mode() scenario of the shared source, alone
def run_case(name, npass, nfail, tamper=None, mode='flat'):
    logfile = test.obj_dir + '/sim_' + name + '.log'
    flags = ['+verilator+wno+unsatconstr+1', '+MODE=' + mode]
    test.execute(logfile=logfile,
                 all_run_flags=flags,
                 run_env=(SOLVER + tamper + ' ') if tamper else '')
    test.file_grep(logfile, r'NPASS=(\d+)', npass)
    test.file_grep(logfile, r'NFAIL=(\d+)', nfail)


# A cyclic value that no x admits fails the call; the rest of the cycle recovers
run_case('plain', 5, 1)

# Every reply the draw and the tail depend on, answered unusably. None may be
# read as an exhausted cycle: the call fails and the permutation is left alone.
# Status 2: the draw check-sat of call 1
run_case('draw_unknown', 4, 2, 'TAMPER=unknown_once TAMPER_AT=2')
# S-expression reply 1: the draw get-value of call 1
run_case('draw_error', 4, 2, 'TAMPER=err_reply TAMPER_AT=1')
# Model reply 1: the draw get-value of call 1, answered naming another variable
run_case('draw_short', 4, 2, 'TAMPER=short_model TAMPER_AT=1')
# Model reply 1: the draw get-value of call 1, also naming a variable never requested.
# Only the drawn variable is pinned, so the call is unaffected.
run_case('draw_extra_var', 5, 1, 'TAMPER=extra_var TAMPER_AT=1')
# Status 15: the tail check-sat of call 3, which draws the c no x admits
run_case('tail_unknown', 4, 2, 'TAMPER=unknown_once TAMPER_AT=15')
# A draw pin round the solver cannot settle leaves no model, so the call fails.
# Unsat-assumptions reply 2: the draw pin round of call 3
run_case('draw_pin_error', 4, 2, 'TAMPER=err_assume TAMPER_AT=2')

# The diversity round after the main solve gives up instead, keeping the solved values.
# Status 5: the diversity check-sat-assuming of call 1
run_case('diversity_unknown', 5, 1, 'TAMPER=unknown_once TAMPER_AT=5')
# Unsat-assumptions reply 1: the diversity round of call 1
run_case('diversity_error', 5, 1, 'TAMPER=err_assume TAMPER_AT=1')

# Same through the solve...before layers
run_case('phased_plain', 9, 3, mode='phased')
# Status 32: the tail check-sat of call 4, which draws the c no x admits
run_case('phased_tail_unknown', 10, 2, 'TAMPER=unknown_once TAMPER_AT=32', mode='phased')

# A drawn value that is not a numeral fails the call before it is pinned or recorded.
# Model reply 1: the draw get-value of call 1
run_case('draw_bad_value', 5, 1, 'TAMPER=bare_hash TAMPER_AT=1', mode='bad_draw')

# Two cycling variables keep the joint solve, so no call fails
run_case('two_randc', 12, 0, mode='two')

# The solver sampler draws c from the seeded model, with no diversity pin round. The
# counts depend on the solver, so the scenario checks only what any draw order keeps.
# FreshCycle does not run here: its failure bound assumes Verilator's uniform draw, and a
# solver free to draw c == 3 last in every cycle never fails a call.
solver_log = test.obj_dir + '/solver_sampler.log'
test.execute(logfile=test.obj_dir + '/sim_sampler.log',
             all_run_flags=[
                 '+verilator+wno+unsatconstr+1', '+MODE=sampler', '+verilator+rand+sampler+solver',
                 '+verilator+solver+file+' + solver_log
             ])
test.file_grep(solver_log, r'; sampler: solver')
test.file_grep(solver_log, r':random-seed')
test.file_grep_not(solver_log, r'check-sat-assuming')

test.passes()
