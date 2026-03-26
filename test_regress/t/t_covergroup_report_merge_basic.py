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

test.compile(verilator_flags2=['--cc', '--coverage-user'])

cov1 = test.obj_dir + "/coverage_mode1.dat"
cov2 = test.obj_dir + "/coverage_mode2.dat"
cov_full = test.obj_dir + "/coverage_full.dat"
cov_merged = test.obj_dir + "/coverage_merged.dat"
cov_default = test.obj_dir + "/coverage.dat"

test.execute(all_run_flags=["+MODE=1"])
shutil.copyfile(cov_default, cov1)

test.execute(all_run_flags=["+MODE=2"])
shutil.copyfile(cov_default, cov2)

test.execute(all_run_flags=["+MODE=0"])
shutil.copyfile(cov_default, cov_full)

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--write",
    cov_merged,
    cov1,
    cov2,
],
         verilator_run=True)

test.files_identical_sorted(cov_merged, cov_full)

merged_annot = test.obj_dir + "/annotated_merged"
full_annot = test.obj_dir + "/annotated_full"

test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--annotate-points",
    "--annotate",
    merged_annot,
    cov_merged,
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
test.files_identical(f"{merged_annot}/{top.name}", f"{full_annot}/{top.name}")

test.passes()
