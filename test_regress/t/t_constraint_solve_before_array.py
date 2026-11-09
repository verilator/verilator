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

if test.vlt:
    solver_log = test.obj_dir + '/solver.log'
    test.execute(all_run_flags=['+verilator+solver+file+' + solver_log])
    # These get-value commands only appear when the named variables form an
    # intermediate solve-before layer, rather than when the edge is dropped.
    test.file_grep(solver_log, r'\(get-value \(n_before \)\)')
    test.file_grep(solver_log, r'\(get-value \(__Vdyn_before_size __Vque_before_size \)\)')
    test.file_grep(solver_log, r'\(get-value \(inline_n \)\)')
    test.file_grep(solver_log, r'\(get-value \(with_n \)\)')
    test.file_grep(solver_log, r'\(get-value \(first \)\)')
    test.file_grep(solver_log, r'\(get-value \(__Vd_size \)\)')
else:
    test.execute()

test.passes()
