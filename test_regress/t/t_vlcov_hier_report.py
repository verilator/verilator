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


all_types_cov = test.obj_dir + "/all_types.dat"
with open(all_types_cov, "w", encoding="utf-8") as fh:
    fh.write("# SystemC::Coverage-3\n")
    fh.write("C '\001f\002t/all_types.v\001l\00210\001n\0021\001t\002line"
             "\001page\002v_line/all_types\001o\002block\001S\00210"
             "\001h\002top.t.u_all' 1\n")
    fh.write("C '\001f\002t/all_types.v\001l\00211\001n\0021\001t\002line"
             "\001page\002v_line/all_types\001o\002block\001S\00211"
             "\001h\002top.t.u_all' 0\n")
    fh.write("C '\001f\002t/all_types.v\001l\00212\001n\0021\001t\002toggle"
             "\001page\002v_toggle/all_types\001o\002sig:0->1"
             "\001h\002top.t.u_all' 1\n")
    fh.write("C '\001f\002t/all_types.v\001l\00213\001n\0021\001t\002branch"
             "\001page\002v_branch/all_types\001o\002if\001S\00213"
             "\001h\002top.t.u_all' 1\n")
    fh.write("C '\001f\002t/all_types.v\001l\00213\001n\0022\001t\002branch"
             "\001page\002v_branch/all_types\001o\002else"
             "\001h\002top.t.u_all' 0\n")
    fh.write("C '\001f\002t/all_types.v\001l\00214\001n\0021\001t\002expr"
             "\001page\002v_expr/all_types\001o\002(a==0) => 1"
             "\001h\002top.t.u_all' 1\n")
    fh.write("C '\001f\002t/all_types.v\001l\00214\001n\0022\001t\002expr"
             "\001page\002v_expr/all_types\001o\002(a==1) => 1"
             "\001h\002top.t.u_all' 0\n")
    fh.write("C '\001f\002t/all_types.v\001l\00215\001n\0021\001t\002fsm_state"
             "\001page\002v_fsm_state/all_types\001o\002IDLE"
             "\001Fv\002state\001h\002top.t.u_all' 1\n")
    fh.write("C '\001f\002t/all_types.v\001l\00215\001n\0022\001t\002fsm_state"
             "\001page\002v_fsm_state/all_types\001o\002BUSY"
             "\001Fv\002state\001h\002top.t.u_all' 0\n")
    fh.write("C '\001f\002t/all_types.v\001l\00216\001n\0021\001t\002fsm_arc"
             "\001page\002v_fsm_arc/all_types\001o\002IDLE->BUSY"
             "\001Fv\002state\001Ff\002IDLE\001Ft\002BUSY\001h\002top.t.u_all' 1\n")
    fh.write("C '\001f\002t/all_types.v\001l\00216\001n\0022\001t\002fsm_arc"
             "\001page\002v_fsm_arc/all_types\001o\002BUSY->IDLE"
             "\001Fv\002state\001Ff\002BUSY\001Ft\002IDLE\001h\002top.t.u_all' 0\n")
    fh.write("C '\001f\002t/all_types.v\001l\00217\001n\0021\001t\002user"
             "\001page\002v_user/all_types\001o\002coverpoint\001S\00217"
             "\001h\002top.t.u_all' 1\n")

run_report("verilator_coverage --report summary t/t_vlcov_data_e.dat",
           ["--report", "summary", "t/t_vlcov_data_e.dat"])
run_report("verilator_coverage --report hierarchy t/t_cover_hier.out",
           ["--report", "hierarchy", "t/t_cover_hier.out"])
run_report("verilator_coverage --report hierarchy --levels 2 t/t_cover_hier.out",
           ["--report", "hierarchy", "--levels", "2", "t/t_cover_hier.out"])
run_report("verilator_coverage --report hier --levels 2 t/t_cover_hier.out",
           ["--report", "hier", "--levels", "2", "t/t_cover_hier.out"])
run_report("verilator_coverage --report hierarchy t/t_cover_lib__1.out",
           ["--report", "hierarchy", "t/t_cover_lib__1.out"])
run_report("verilator_coverage --report hierarchy --levels 3 all_types.dat",
           ["--report", "hierarchy", "--levels", "3", all_types_cov])

test.files_identical(log, test.golden_filename)

test.passes()
