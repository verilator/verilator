#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 OpenAI
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os
from pathlib import Path

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = "t/t_covergroup_report_basic.v"

test.compile(verilator_flags2=['--cc', '--coverage-user'])

test.execute()

cov_full = test.obj_dir + "/coverage.dat"
cov_covergroup = test.obj_dir + "/coverage_covergroup.dat"
cov_block = test.obj_dir + "/coverage_block.dat"

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--filter-type",
    "covergroup",
    "--write",
    cov_covergroup,
    cov_full,
],
         verilator_run=True)

test.files_identical_sorted(cov_covergroup, cov_full)

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--filter-type",
    "block",
    "--write",
    cov_block,
    cov_full,
],
         verilator_run=True)

with open(cov_block, encoding="latin-1") as fh:
    block_text = fh.read()
if block_text != "# SystemC::Coverage-3\n":
    raise RuntimeError(f"Unexpected non-empty block filter output:\n{block_text}")

filtered_annot = test.obj_dir + "/annotated_covergroup"
full_annot = test.obj_dir + "/annotated_full"

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--filter-type",
    "covergroup",
    "--annotate-points",
    "--annotate",
    filtered_annot,
    cov_full,
],
         verilator_run=True)

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--annotate-points",
    "--annotate",
    full_annot,
    cov_full,
],
         verilator_run=True)

top = Path(test.top_filename)
test.files_identical(f"{filtered_annot}/{top.name}", f"{full_annot}/{top.name}")

test.passes()
