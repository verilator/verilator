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

test.scenarios('vlt_all', 'ms')

# The exclusion checks intentionally reference ignore/default bins.
test.ms_run_flags += ['-suppress', '13196']
test.compile(verilator_flags2=[
    '--coverage', '--debug-self-test', '--dump-tree', '--dump-tree-json', '--timing'
],
             ms_flags2=['-suppress', '13196'],
             timing_loop=True,
             threads=(2 if test.vltmt else 1))
test.execute()

if test.vlt_all:
    coverage_covergroup_common.covergroup_coverage_report(test)
    test.files_identical(test.obj_dir + '/covergroup_report.txt', test.golden_filename)

test.passes()
