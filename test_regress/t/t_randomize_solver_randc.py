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

if not test.have_solver:
    test.skip("No constraint solver installed")

test.compile()

SOLVER = 'VERILATOR_SOLVER="' + test.t_dir + '/randomize_solver_tamper.py" '


def run(name, npass, nfail, tamper=None, phased=False):
    logfile = test.obj_dir + '/sim_' + name + '.log'
    flags = ['+verilator+wno+unsatconstr+1']
    if phased:
        flags.append('+PHASED')
    test.execute(logfile=logfile,
                 all_run_flags=flags,
                 run_env=(SOLVER + tamper + ' ') if tamper else '')
    test.file_grep(logfile, r'NPASS=(\d+)', npass)
    test.file_grep(logfile, r'NFAIL=(\d+)', nfail)


# A cyclic value that no x admits fails the call; the rest of the cycle recovers
run('plain', 5, 1)

# Every reply the draw and the tail depend on, answered unusably. None may be
# read as an exhausted cycle: the call fails and the permutation is left alone.
run('draw_unknown', 4, 2, 'TAMPER=unknown_once TAMPER_AT=2')  # draw check-sat
run('draw_error', 4, 2, 'TAMPER=err_reply TAMPER_AT=1')  # draw get-value
run('draw_short', 4, 2, 'TAMPER=short_model TAMPER_AT=1')  # reply names another var
run('tail_unknown', 4, 2, 'TAMPER=unknown_once TAMPER_AT=15')  # flat tail check-sat

# Same through the solve...before layers
run('phased_plain', 10, 2, phased=True)
run('phased_tail_unknown', 9, 3, 'TAMPER=unknown_once TAMPER_AT=34', phased=True)

test.passes()
