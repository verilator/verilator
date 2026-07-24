#!/usr/bin/env python3
# DESCRIPTION: Verilator: Runtime hierarchy report with per-instance coverage data
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3,
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

from coverage_common import init_log, run_vlcov, vlcov_run_context

test.scenarios('simulator')
test.fourstate_capable = False

if not test.have_coroutines:
    test.skip("Test requires Coroutines; ignore error since not available")

test.compile(top_filename="t/t_vlcov_hier_report_runtime.v",
             verilator_flags2=[
                 "--binary",
                 "--coverage",
                 "--coverage-fsm",
                 "--coverage-per-instance",
                 "--top-module",
                 "tb",
                 "--timing",
             ])

test.execute(all_run_flags=[" +verilator+coverage+file+" + test.obj_dir + "/coverage.dat"])

summary_log = test.obj_dir + "/summary.log"
hier_log = test.obj_dir + "/hierarchy.log"
combined_log = test.obj_dir + "/vlcov.log"

init_log(combined_log)
run_vlcov(vlcov_run_context(test, combined_log, summary_log),
          "verilator_coverage --report summary coverage.dat",
          args=["--report", "summary", test.obj_dir + "/coverage.dat"])
run_vlcov(vlcov_run_context(test, combined_log, hier_log),
          "verilator_coverage --report hierarchy --levels 3 coverage.dat",
          args=["--report", "hierarchy", "--levels", "3", test.obj_dir + "/coverage.dat"])

test.files_identical(combined_log, test.golden_filename)

test.passes()
