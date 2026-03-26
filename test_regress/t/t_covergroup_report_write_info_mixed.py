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
line_info = line_dir + "/coverage.info"

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
mixed_info = test.obj_dir + "/coverage_mixed.info"

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
    "--write-info",
    line_info,
    line_cov,
],
         verilator_run=True)

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--write-info",
    mixed_info,
    mixed_cov,
],
         verilator_run=True)

test.files_identical(mixed_info, line_info)

with open(mixed_info, encoding="latin-1") as fh:
    mixed_text = fh.read()
if "covergroup" in mixed_text:
    raise RuntimeError(f"Functional coverage leaked into LCOV output:\n{mixed_text}")
if "SF:t/t_cover_line.v" not in mixed_text or "DA:" not in mixed_text:
    raise RuntimeError(f"LCOV output missing expected structural coverage records:\n{mixed_text}")

test.passes()
