#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import shutil

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_randomize_solver_fault.v"

if not test.have_solver:
    test.skip("No constraint solver installed")
if not shutil.which('z3'):
    test.skip("No z3 in PATH")

test.compile()

# Diversity-round unknown keeps the base solution, issues no get-unsat-assumptions
test.execute(run_env='VERILATOR_SOLVER=' + test.t_dir +
             '/randomize_solver_tamper.py TAMPER=unknown_once TAMPER_AT=3' +
             ' VERILATOR_SOLVER_TIMEOUT=10000')

test.file_grep(test.run_log_filename, r'Solver returned unknown')
test.file_grep(test.run_log_filename, r'NPASS=5')

test.passes()
