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

threads = 2 if test.vltmt else 1
coverage_covergroup_common.run(test, threads=threads)

merged = test.obj_dir + '/merged.dat'
test.run(cmd=[
    os.environ['VERILATOR_ROOT'] + '/bin/verilator_coverage', '--write', merged,
    test.coverage_filename
],
         verilator_run=True)
test.file_grep(merged, r"cg_binsof\.all_products\.combined.*' 10")

test.passes()
