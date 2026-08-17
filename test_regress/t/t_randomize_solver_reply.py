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
test.top_filename = "t/t_randomize_solver_fault.v"

if not test.have_solver:
    test.skip("No constraint solver installed")

test.compile()

# 12 randomize calls; each entry names the reply the solver mangles
runs = [
    ('success', 1, 12),  # print-success echo ahead of every reply
    ('crlf', 1, 12),  # CRLF line endings
    ('multiline', 1, 12),  # S-expression split one token per line
    ('err_once', 2, 11),  # solver rejects a command instead of answering
    ('err_multiline', 2, 11),  # same, with the error spanning two lines
    ('unsupported_once', 2, 11),  # command not supported, so no status ever comes
    ('unknown_once', 2, 11),  # unknown answers one check-sat
    ('garbage_status', 2, 11),  # a word that is not a status
    ('err_reply', 1, 11),  # error in place of an S-expression reply
    ('garbage_model', 1, 11),  # half-valid model must not reach the variables
    ('bad_value', 1, 11),  # a value with no base must not commit the earlier one
    ('bad_digits', 1, 11),  # digits outside the stated base are not a number
    ('short_model', 1, 11),  # a model missing a requested variable is not a model
    ('dup_model', 1, 11),  # the same variable answered twice
]

for mode, at, npass in runs:
    logfile = test.obj_dir + '/sim_' + mode + '.log'
    test.execute(logfile=logfile,
                 run_env='VERILATOR_SOLVER="' + test.t_dir + '/randomize_solver_tamper.py" ' +
                 'TAMPER=' + mode + ' TAMPER_AT=' + str(at))
    test.file_grep(logfile, r'NPASS=' + str(npass) + r'\n')

test.passes()
