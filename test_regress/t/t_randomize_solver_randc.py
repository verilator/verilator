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

# Fixed-seed fault-injection test: the tamper positions and the pass/fail counts follow
# the permutation each srandom() seed produces, and are re-derived if Verilator's RNG
# usage changes. Seed-independent randc coverage is in t_constraint_randc_solve_first.

if not test.have_solver:
    test.skip("No constraint solver installed")

test.compile()

# TAMPER_AT counts one kind of reply from the start of the simulation, per the mode's
# entry in randomize_solver_tamper.py: unknown_once counts status lines, err_reply
# S-expression replies, short_model and bare_hash model replies. Status 1 answers the
# check-sat sent when the session opens. To re-derive a constant, run the case's MODE
# without TAMPER, with VERILATOR_SOLVER set to a wrapper that logs the conversation, and
# count the replies up to the one its comment names.
SOLVER = 'VERILATOR_SOLVER="' + test.t_dir + '/randomize_solver_tamper.py" '


def run_case(name, npass, nfail, tamper=None, mode=None):
    logfile = test.obj_dir + '/sim_' + name + '.log'
    flags = ['+verilator+wno+unsatconstr+1']
    if mode:
        flags.append('+MODE=' + mode)
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
# Status 15: the tail check-sat of call 3, which draws the c no x admits
run_case('tail_unknown', 4, 2, 'TAMPER=unknown_once TAMPER_AT=15')

# Same through the solve...before layers
run_case('phased_plain', 9, 3, mode='phased')
# Status 32: the tail check-sat of call 4, which draws the c no x admits
run_case('phased_tail_unknown', 10, 2, 'TAMPER=unknown_once TAMPER_AT=32', mode='phased')

# A drawn value that is not a numeral fails the call before it is pinned or recorded.
# Model reply 1: the draw get-value of call 1
run_case('draw_bad_value', 5, 1, 'TAMPER=bare_hash TAMPER_AT=1', mode='bad_draw')

# Two cycling variables keep the joint solve, so no call fails
run_case('two_randc', 12, 0, mode='two')

test.passes()
