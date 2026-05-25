#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3,
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

if not test.have_coroutines:
    test.skip("Test requires Coroutines; ignore error since not available")

source = "t/t_vlcov_hier_merge_three.v"


def build_and_run(top, prefix, dirname):
    obj_dir = test.obj_dir + "/" + dirname
    cov = obj_dir + "/coverage.dat"
    test.mkdir_ok(obj_dir)
    test.run(cmd=[
        "perl",
        os.environ["VERILATOR_ROOT"] + "/bin/verilator",
        "--binary",
        "--coverage",
        "--coverage-per-instance",
        "--top-module",
        top,
        "--timing",
        source,
        "--prefix",
        prefix,
        "-Mdir",
        obj_dir,
    ],
             logfile=test.obj_dir + "/vlt_compile_" + dirname + ".log",
             verilator_run=True)
    test.run(cmd=[
        obj_dir + "/" + prefix,
        "+verilator+coverage+file+" + cov,
    ],
             logfile=test.obj_dir + "/vlt_sim_" + dirname + ".log",
             check_finished=True,
             verilator_run=True)
    return cov


# Generate three concrete hierarchy coverage files.  The first two use the
# same design unit under different hierarchy paths; the third uses a different
# unit so --hier-merge must preserve both instance and design-unit identity.
same_a_cov = build_and_run("tb_same_a", "Vsame_a", "same_a")
same_b_cov = build_and_run("tb_same_b", "Vsame_b", "same_b")
other_cov = build_and_run("tb_other", "Vother", "other")

merged_cov = test.obj_dir + "/coverage.dat"
test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--hier-merge",
    "--write",
    merged_cov,
    same_a_cov,
    same_b_cov,
    other_cov,
],
         verilator_run=True)

test.files_identical(merged_cov, "t/t_vlcov_hier_merge_three.dat.out")

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--annotate",
    test.obj_dir + "/annotated",
    merged_cov,
],
         verilator_run=True)

test.files_identical(test.obj_dir + "/annotated/t_vlcov_hier_merge_three.v",
                     "t/t_vlcov_hier_merge_three_annotated.out")

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--report",
    "summary",
    merged_cov,
],
         logfile=test.obj_dir + "/summary.log",
         tee=False,
         verilator_run=True)

test.files_identical(test.obj_dir + "/summary.log", "t/t_vlcov_hier_merge_three_summary.out")

test.passes()
