#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

if not test.have_solver:
    test.skip("No constraint solver installed")

test.compile()

# The third call draws a value admitting no x; the fifteenth status answers the
# query asking whether any value left in the cycle still does.
logfile = test.obj_dir + '/sim_plain.log'
test.execute(logfile=logfile, all_run_flags=['+verilator+wno+unsatconstr+1'])
test.file_grep(logfile, r'NPASS=(\d+)', 5)
test.file_grep(logfile, r'NFAIL=(\d+)', 1)

# An unreadable answer to that query is not evidence of an exhausted cycle:
# the call fails and the permutation is left alone.
logfile = test.obj_dir + '/sim_tail_unknown.log'
test.execute(logfile=logfile,
             all_run_flags=['+verilator+wno+unsatconstr+1'],
             run_env='VERILATOR_SOLVER="' + test.t_dir + '/randomize_solver_tamper.py" ' +
             'TAMPER=unknown_once TAMPER_AT=15 ')
test.file_grep(logfile, r'NPASS=(\d+)', 4)
test.file_grep(logfile, r'NFAIL=(\d+)', 2)

test.passes()
