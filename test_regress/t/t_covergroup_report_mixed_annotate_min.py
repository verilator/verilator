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
test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--write",
    mixed_cov,
    cg_cov,
    line_cov,
],
         verilator_run=True)

mixed_annot = test.obj_dir + "/annotated_mixed_min2"
pure_annot = test.obj_dir + "/annotated_pure_min2"

for out_dir, cov_file in ((mixed_annot, mixed_cov), (pure_annot, cg_cov)):
    test.run(cmd=[
        os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
        "--filter-type",
        "covergroup",
        "--annotate-points",
        "--annotate-min",
        "2",
        "--annotate",
        out_dir,
        cov_file,
    ],
             verilator_run=True)

top = Path(test.top_filename)
annot_file = f"/{top.name}"
test.files_identical(f"{mixed_annot}{annot_file}", f"{pure_annot}{annot_file}")

with open(f"{mixed_annot}{annot_file}", encoding="latin-1") as fh:
    text = fh.read()

for expected in (
        "+000002  point: type=covergroup comment=cpa.zero",
        "+000002  point: type=covergroup comment=cpa.one",
        "+000002  point: type=covergroup comment=cpb.zero",
        "+000002  point: type=covergroup comment=cpb.one",
        "-000001  point: type=covergroup comment=ab.__auto[0]",
        "-000001  point: type=covergroup comment=ab.__auto[1]",
        "-000001  point: type=covergroup comment=ab.__auto[2]",
        "-000001  point: type=covergroup comment=ab.__auto[3]",
):
    if expected not in text:
        raise RuntimeError(f"Missing expected annotate-min classification:\n{expected}\n---\n{text}")

if "type=line" in text or "type=branch" in text:
    raise RuntimeError(f"Structural coverage leaked into covergroup annotate-min output:\n{text}")

test.passes()
