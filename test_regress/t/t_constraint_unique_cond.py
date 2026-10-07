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

# Deliberately unsatisfiable randomize() calls check that the guarded
# constraint is applied; their warnings are not of interest here
test.execute(all_run_flags=['+verilator+wno+unsatconstr+1'])

# The solver variables each hard() call names: plain names, a member path, and the
# array a unique under an if names in the folded constraint's text
cpp_files = test.glob_some(test.obj_dir + "/" + test.vm_prefix + "*.cpp")
test.file_grep_any(cpp_files, r'\{"sel", "x", "y", "z"\}')
test.file_grep_any(cpp_files, r'\{"arr", "sel"\}')
test.file_grep_any(cpp_files, r'\{"arr", "s\.on"\}')

test.passes()
