#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import coverage_covergroup_common

test.scenarios('vlt_all')

test.compile(verilator_flags2=['--coverage'], threads=(2 if test.vltmt else 1))
test.execute(all_run_flags=['+verilator+error+limit+100'],
             expect_filename=test.golden_filename.replace('.out', '.error.out'))

coverage_covergroup_common.covergroup_coverage_report(test)
test.files_identical(test.obj_dir + '/covergroup_report.txt', test.golden_filename)

test.passes()
