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
from pathlib import Path

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
mixed_cg_cov = test.obj_dir + "/coverage_mixed_covergroup.dat"
mixed_line_cov = test.obj_dir + "/coverage_mixed_line.dat"

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
    "covergroup",
    "--write",
    mixed_cg_cov,
    mixed_cov,
],
         verilator_run=True)

test.files_identical_sorted(mixed_cg_cov, cg_cov)

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--filter-type",
    "line",
    "--write",
    mixed_line_cov,
    mixed_cov,
],
         verilator_run=True)

with open(mixed_line_cov, encoding="latin-1") as fh:
    line_text = fh.read()
if "\x01t\x02covergroup" in line_text:
    raise RuntimeError("covergroup point leaked into line-filtered mixed coverage output")
if "\x01t\x02line" not in line_text:
    raise RuntimeError(f"line-filtered mixed coverage output missing line coverage:\n{line_text}")

mixed_cg_annot = test.obj_dir + "/annotated_mixed_covergroup"
cg_annot = test.obj_dir + "/annotated_covergroup_only"

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--filter-type",
    "covergroup",
    "--annotate-points",
    "--annotate",
    mixed_cg_annot,
    mixed_cov,
],
         verilator_run=True)

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--annotate-points",
    "--annotate",
    cg_annot,
    cg_cov,
],
         verilator_run=True)

top = Path(test.top_filename)
test.files_identical(f"{mixed_cg_annot}/{top.name}", f"{cg_annot}/{top.name}")

test.passes()
