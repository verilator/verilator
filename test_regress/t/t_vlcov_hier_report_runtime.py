#!/usr/bin/env python3
# DESCRIPTION: Verilator: Runtime hierarchy report with per-instance all-coverage data
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3,
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os

import vltest_bootstrap

test.scenarios('simulator')

test.compile(top_filename="t/t_vlcov_hier_report_runtime.v",
             verilator_flags2=[
                 '--binary',
                 '--coverage',
                 '--coverage-fsm',
                 '--coverage-per-instance',
                 '--top-module',
                 'tb',
                 '--timing',
             ])

test.execute(all_run_flags=[" +verilator+coverage+file+" + test.obj_dir + "/coverage.dat"])

summary_log = test.obj_dir + "/summary.log"
hier_log = test.obj_dir + "/hierarchy.log"
combined_log = test.obj_dir + "/vlcov.log"

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--report",
    "summary",
    test.obj_dir + "/coverage.dat",
],
         logfile=summary_log,
         tee=False,
         verilator_run=True)

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--report",
    "hierarchy",
    "--levels",
    "3",
    test.obj_dir + "/coverage.dat",
],
         logfile=hier_log,
         tee=False,
         verilator_run=True)

with open(combined_log, "w") as out:
    out.write("$ verilator_coverage --report summary coverage.dat\n")
    with open(summary_log) as fh:
        out.write(fh.read())
    out.write("\n$ verilator_coverage --report hierarchy --levels 3 coverage.dat\n")
    with open(hier_log) as fh:
        out.write(fh.read())

test.files_identical(combined_log, test.golden_filename)

test.passes()
