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

test.compile(verilator_flags2=['--cc', '--coverage-user'])
test.execute()

annot_dir = test.obj_dir + "/annotated"
test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--annotate-all",
    "--annotate-min",
    "1",
    "--annotate-points",
    "--annotate",
    annot_dir,
    test.obj_dir + "/coverage.dat",
],
         verilator_run=True)

top = Path(test.top_filename)
annot_path = Path(annot_dir) / top.name
text = annot_path.read_text(encoding="latin-1")

missing_lines = [
    line for line in text.splitlines()
    if "point: type=covergroup comment=ab.__auto[" in line and line.startswith("-")
]
if len(missing_lines) != 2:
    raise RuntimeError(f"Expected exactly 2 printed missing cross bins, got {len(missing_lines)}:\n{text}")

if "-000000  point: type=covergroup comment=<suppressed missing cross bins>" not in text:
    raise RuntimeError(f"Missing suppressed cross-bin summary line:\n{text}")
if "suppressed=1 cross_num_print_missing=2" not in text:
    raise RuntimeError(f"Incorrect suppressed cross-bin summary metadata:\n{text}")
if "+000001  point: type=covergroup comment=ab.__auto[0]" not in text:
    raise RuntimeError(f"Covered cross bin missing from annotate output:\n{text}")

test.passes()
