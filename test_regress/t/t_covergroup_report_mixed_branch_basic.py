#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 OpenAI
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os
import shutil

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_covergroup_report_basic.v"

test.compile(verilator_flags2=['--cc', '--coverage-user'])
test.execute()

cg_cov = test.obj_dir + "/coverage_covergroup.dat"
shutil.copyfile(test.obj_dir + "/coverage.dat", cg_cov)

line_dir = test.obj_dir + "/linecov"
os.makedirs(line_dir, exist_ok=True)
line_cov = line_dir + "/coverage.dat"

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator",
    "--binary",
    "--cc",
    "--coverage-line",
    "--Mdir",
    line_dir + "/obj_dir",
    "t/t_cover_line.v",
],
         verilator_run=True)

test.run(cmd=[
    line_dir + "/obj_dir/Vt_cover_line",
    "+verilator+coverage+file+" + line_cov,
],
         verilator_run=True)

mixed_cov = test.obj_dir + "/coverage_mixed.dat"
mixed_branch_cov = test.obj_dir + "/coverage_mixed_branch.dat"
line_branch_cov = test.obj_dir + "/coverage_line_branch.dat"

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--write",
    mixed_cov,
    cg_cov,
    line_cov,
],
         verilator_run=True)

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--filter-type",
    "branch",
    "--write",
    mixed_branch_cov,
    mixed_cov,
],
         verilator_run=True)

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--filter-type",
    "branch",
    "--write",
    line_branch_cov,
    line_cov,
],
         verilator_run=True)

test.files_identical_sorted(mixed_branch_cov, line_branch_cov)

with open(mixed_branch_cov, encoding="latin-1") as fh:
    branch_text = fh.read()
if "\x01t\x02covergroup" in branch_text:
    raise RuntimeError(f"covergroup point leaked into branch-filtered output:\n{branch_text}")
if "\x01t\x02branch" not in branch_text:
    raise RuntimeError(f"branch-filtered output missing branch coverage:\n{branch_text}")

mixed_branch_annot = test.obj_dir + "/annotated_mixed_branch"
line_branch_annot = test.obj_dir + "/annotated_line_branch"
annotated_line = "/t_cover_line.v"

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--filter-type",
    "branch",
    "--annotate-points",
    "--annotate",
    mixed_branch_annot,
    mixed_cov,
],
         verilator_run=True)

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--filter-type",
    "branch",
    "--annotate-points",
    "--annotate",
    line_branch_annot,
    line_cov,
],
         verilator_run=True)

test.files_identical(f"{mixed_branch_annot}{annotated_line}",
                     f"{line_branch_annot}{annotated_line}")

with open(f"{mixed_branch_annot}{annotated_line}", encoding="latin-1") as fh:
    annot_text = fh.read()
if "type=covergroup" in annot_text:
    raise RuntimeError(f"covergroup point leaked into branch annotation output:\n{annot_text}")
if "type=branch" not in annot_text:
    raise RuntimeError(f"branch annotation output missing branch points:\n{annot_text}")

test.passes()
