#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3,
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

from coverage_common import init_log, run_vlcov, vlcov_run_context

test.scenarios('dist')

log = test.obj_dir + "/vlcov.log"
tmp_log = test.obj_dir + "/vlcov.tmp"

init_log(log)
vlcov = vlcov_run_context(test, log, tmp_log)

missing_cov = test.obj_dir + "/missing.dat"
with open(missing_cov, "w", encoding="utf-8") as fh:
    fh.write("# SystemC::Coverage-3\n")
    fh.write("C '\001f\002t/missing.v\001l\0021\001t\002line\001page\002v_line/missing' 1\n")

run_vlcov(vlcov,
          "verilator_coverage --report unknown t/t_cover_hier.out",
          args=["--report", "unknown", "t/t_cover_hier.out"],
          fails=True,
          normalize_errors=True)
run_vlcov(vlcov,
          "verilator_coverage --report summary,unknown t/t_cover_hier.out",
          args=["--report", "summary,unknown", "t/t_cover_hier.out"],
          fails=True,
          normalize_errors=True)
run_vlcov(vlcov,
          "verilator_coverage --report hierarchy missing.dat",
          args=["--report", "hierarchy", missing_cov])

test.files_identical(log, test.golden_filename)

test.passes()
