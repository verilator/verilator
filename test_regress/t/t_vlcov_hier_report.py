#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3,
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

from coverage_common import init_log, run_vlcov

test.scenarios('dist')

log = test.obj_dir + "/vlcov.log"
tmp_log = test.obj_dir + "/vlcov.tmp"

init_log(log)

collapsed_cov = test.obj_dir + "/collapsed.dat"
with open(collapsed_cov, "w", encoding="utf-8") as fh:
    fh.write("# SystemC::Coverage-3\n")
    fh.write("C '\001f\002t/soc.v\001l\00210\001t\002line\001page\002v_line/core"
             "\001h\002tb.cluster*.u_core' 4\n")
    fh.write("C '\001f\002t/soc.v\001l\00211\001t\002line\001page\002v_line/core"
             "\001h\002tb.cluster*.u_core' 0\n")
    fh.write("C '\001f\002t/soc.v\001l\00212\001t\002branch\001page\002v_branch/core"
             "\001h\002tb.cluster*.u_core' 9\n")
    fh.write("C '\001f\002t/soc.v\001l\00213\001t\002branch\001page\002v_branch/core"
             "\001h\002tb.cluster?.u_core' 0\n")

empty_cov = test.obj_dir + "/empty.dat"
with open(empty_cov, "w", encoding="utf-8") as fh:
    fh.write("# SystemC::Coverage-3\n")

run_vlcov(test,
          log=log,
          tmp_log=tmp_log,
          label="verilator_coverage --report summary t/t_vlcov_data_e.dat",
          args=["--report", "summary", "t/t_vlcov_data_e.dat"])
run_vlcov(test,
          log=log,
          tmp_log=tmp_log,
          label="verilator_coverage t/t_cover_hier.out",
          args=["t/t_cover_hier.out"])
run_vlcov(test,
          log=log,
          tmp_log=tmp_log,
          label="verilator_coverage --report summary,hier t/t_cover_hier.out",
          args=["--report", "summary,hier", "t/t_cover_hier.out"])
run_vlcov(test,
          log=log,
          tmp_log=tmp_log,
          label="verilator_coverage --report hier,summary --levels 0 t/t_cover_hier.out",
          args=["--report", "hier,summary", "--levels", "0", "t/t_cover_hier.out"])
run_vlcov(test,
          log=log,
          tmp_log=tmp_log,
          label="verilator_coverage --report hier,summary --levels -4 t/t_cover_hier.out",
          args=["--report", "hier,summary", "--levels", "-4", "t/t_cover_hier.out"])
run_vlcov(test,
          log=log,
          tmp_log=tmp_log,
          label="verilator_coverage --report summary empty.dat",
          args=["--report", "summary", empty_cov])
run_vlcov(test,
          log=log,
          tmp_log=tmp_log,
          label="verilator_coverage --report hierarchy t/t_cover_hier.out",
          args=["--report", "hierarchy", "t/t_cover_hier.out"])
run_vlcov(test,
          log=log,
          tmp_log=tmp_log,
          label="verilator_coverage --report hierarchy --levels 2 t/t_cover_hier.out",
          args=["--report", "hierarchy", "--levels", "2", "t/t_cover_hier.out"])
run_vlcov(test,
          log=log,
          tmp_log=tmp_log,
          label="verilator_coverage --report hierarchy --levels -1 t/t_cover_hier.out",
          args=["--report", "hierarchy", "--levels", "-1", "t/t_cover_hier.out"])
run_vlcov(test,
          log=log,
          tmp_log=tmp_log,
          label="verilator_coverage --report hier --levels 2 t/t_cover_hier.out",
          args=["--report", "hier", "--levels", "2", "t/t_cover_hier.out"])
run_vlcov(test,
          log=log,
          tmp_log=tmp_log,
          label="verilator_coverage --report hierarchy collapsed.dat",
          args=["--report", "hierarchy", collapsed_cov])

test.files_identical(log, test.golden_filename)

test.passes()
