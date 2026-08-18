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
    ('success', 1, 16),  # print-success echo ahead of every reply
    ('crlf', 1, 16),  # CRLF line endings
    ('multiline', 1, 16),  # S-expression split one token per line
    ('indent', 1, 16),  # leading whitespace before every reply
    ('octal', 1, 16),  # octal values
    ('binary', 1, 16),  # binary values
    ('upper_hex', 1, 16),  # uppercase hex digits
    ('err_once', 2, 15),  # solver rejects a command instead of answering
    ('err_multiline', 2, 15),  # same, with the error spanning two lines
    ('err_unbal', 2, 15),  # same, closing more parens than it opens
    ('err_unbal_cont', 2, 15),  # same, with the extra paren on a continuation line
    ('unsupported_once', 2, 15),  # command not supported, so no status ever comes
    ('unknown_once', 2, 15),  # unknown answers one check-sat
    ('unknown_twice', 2, 15),  # a second unknown must not warn again
    ('garbage_status', 2, 15),  # a word that is not a status
    ('err_reply', 1, 15),  # error in place of an S-expression reply
    ('garbage_model', 1, 15),  # half-valid model must not reach the variables
    ('bad_value', 1, 15),  # a value with no base must not commit the earlier one
    ('bad_digits', 1, 15),  # digits outside the stated base are not a number
    ('bare_hash', 1, 15),  # a value that is only "#"
    ('no_digits', 1, 15),  # a base marker with no digits after it
    ('high_digit', 1, 15),  # a digit legal for some base but not the stated one
    ('bad_base', 1, 15),  # a base character that is not b, o, x or h
    ('unknown_var', 1, 15),  # a variable that was never requested
    ('bad_index', 1, 15),  # a malformed array select index
    ('short_model', 1, 15),  # a model missing a requested variable is not a model
    ('dup_model', 1, 15),  # the same variable answered twice
    ('err_trunc', 2, 0),  # unterminated error, then the pipe closes
    ('model_trunc', 1, 0),  # unterminated model, then the pipe closes
    ('err_phase', 1, 15),  # error in place of an intermediate phase value reply
    ('phase_trunc', 1, 2),  # unterminated phase value reply, then the pipe closes
    ('err_core', 1, 16),  # error in place of the unsat core
    ('core_junk', 1, 4),  # garbage opens the core reply, then the pipe closes
    ('err_assume', 1, 16),  # error in place of the unsat assumptions
    ('oor_assume', 1, 16),  # unsat assumptions naming only an out-of-range literal
    ('garbage_assume', 1, 16),  # a bare word in place of the unsat assumptions
    ('garbage_status', 8, 15),  # a phased check-sat that does not answer with a status
    ('phase_model', 1, 15),  # error in place of the final phased model
]

for mode, at, npass in runs:
    logfile = test.obj_dir + '/sim_' + mode + '_' + str(at) + '.log'
    test.execute(logfile=logfile,
                 run_env='VERILATOR_SOLVER="' + test.t_dir + '/randomize_solver_tamper.py" ' +
                 'TAMPER=' + mode + ' TAMPER_AT=' + str(at))
    test.file_grep(logfile, r'NPASS=' + str(npass) + r'\n')

test.passes()
