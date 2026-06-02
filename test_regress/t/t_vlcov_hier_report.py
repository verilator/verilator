#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3,
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('dist')

vlcov = os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage"
log = test.obj_dir + "/vlcov.log"
tmp_log = test.obj_dir + "/vlcov.tmp"

with open(log, "w", encoding="utf-8"):
    pass


def run_report(label, args):
    with open(log, "a", encoding="utf-8") as log_fh:
        if log_fh.tell():
            log_fh.write("\n")
        log_fh.write("$ " + label + "\n")

    test.run(cmd=[vlcov, *args], logfile=tmp_log, tee=False, verilator_run=True)

    with open(tmp_log, encoding="utf-8") as in_fh, open(log, "a", encoding="utf-8") as log_fh:
        log_fh.write(in_fh.read())


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

run_report("verilator_coverage --report summary t/t_vlcov_data_e.dat",
           ["--report", "summary", "t/t_vlcov_data_e.dat"])
run_report("verilator_coverage --report summary empty.dat", ["--report", "summary", empty_cov])
run_report("verilator_coverage --report hierarchy t/t_cover_hier.out",
           ["--report", "hierarchy", "t/t_cover_hier.out"])
run_report("verilator_coverage --report hierarchy --levels 2 t/t_cover_hier.out",
           ["--report", "hierarchy", "--levels", "2", "t/t_cover_hier.out"])
run_report("verilator_coverage --report hierarchy --levels -1 t/t_cover_hier.out",
           ["--report", "hierarchy", "--levels", "-1", "t/t_cover_hier.out"])
run_report("verilator_coverage --report hier --levels 2 t/t_cover_hier.out",
           ["--report", "hier", "--levels", "2", "t/t_cover_hier.out"])
run_report("verilator_coverage --report hierarchy collapsed.dat",
           ["--report", "hierarchy", collapsed_cov])

test.files_identical(log, test.golden_filename)

test.passes()
