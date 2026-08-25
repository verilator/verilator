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

if not test.have_solver:
    test.skip("No constraint solver installed")

test.compile()

# 16 randomize calls; each entry names the reply the solver mangles
runs = [
    ('bad_base', 1, 15),  # a base character that is not b, o, x or h
    ('bad_digits', 1, 15),  # digits outside the stated base are not a number
    ('bad_index', 1, 15),  # a malformed array select index
    ('bad_value', 1, 15),  # a value with no base must not commit the earlier one
    ('bare_hash', 1, 15),  # a value that is only "#"
    ('binary', 1, 16),  # binary values
    ('core_junk', 1, 16),  # garbage opens the core reply, then the pipe closes
    ('crlf', 1, 16),  # CRLF line endings
    ('dup_model', 1, 15),  # the same variable answered twice
    ('err_assume', 1, 16),  # error in place of the unsat assumptions
    ('err_core', 1, 16),  # error in place of the unsat core
    ('err_multiline', 2, 15),  # solver rejects a command with an error spanning two lines
    ('err_once', 2, 15),  # solver rejects a command instead of answering
    ('err_phase', 1, 15),  # error in place of an intermediate phase value reply
    ('err_reply', 1, 15),  # error in place of an S-expression reply
    ('err_trunc', 2, 0),  # unterminated error, then the pipe closes
    ('err_unbal', 2, 15),  # a rejection error closing more parens than it opens
    ('err_unbal_cont', 2, 15),  # a rejection error with the extra paren on a continuation line
    ('garbage_assume', 1, 16),  # a bare word in place of the unsat assumptions
    ('garbage_model', 1, 15),  # half-valid model must not reach the variables
    ('garbage_status', 2, 15),  # a word that is not a status
    ('garbage_status', 8, 15),  # a phased check-sat that does not answer with a status
    ('high_digit', 1, 15),  # a digit legal for some base but not the stated one
    ('indent', 1, 16),  # leading whitespace before every reply
    ('low_digit', 1, 15),  # a character below any digit or letter
    ('model_trunc', 1, 0),  # unterminated model, then the pipe closes
    ('multiline', 1, 16),  # S-expression split one token per line
    ('no_digits', 1, 15),  # a base marker with no digits after it
    ('octal', 1, 16),  # octal values
    ('oor_assume', 1, 16),  # unsat assumptions naming only an out-of-range literal
    ('phase_model', 1, 15),  # error in place of the final phased model
    ('phase_trunc', 1, 12),  # unterminated phase value reply, then the pipe closes
    ('short_model', 1, 15),  # a model missing a requested variable is not a model
    ('success', 1, 16),  # print-success echo ahead of every reply
    ('unknown_once', 2, 15),  # unknown answers one check-sat
    ('unknown_twice', 2, 15),  # a second unknown must not warn again
    ('unknown_var', 1, 15),  # a variable that was never requested
    ('unsupported_once', 2, 15),  # command not supported, so no status ever comes
    ('upper_hex', 1, 16),  # uppercase hex digits
]

for mode, at, npass in runs:
    logfile = test.obj_dir + '/sim_' + mode + '_' + str(at) + '.log'
    test.execute(logfile=logfile,
                 run_env='VERILATOR_SOLVER="' + test.t_dir + '/randomize_solver_tamper.py" ' +
                 'TAMPER=' + mode + ' TAMPER_AT=' + str(at))
    test.file_grep(logfile, r'NPASS=(\d+)', npass)

test.passes()
