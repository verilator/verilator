#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 OpenAI
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os
import re
import shutil

import vltest_bootstrap


def parse_rank_log(filename):
    rows = {}
    with open(filename, encoding="latin-1") as fh:
        for line in fh:
            match = re.match(r'^\s*(\d+),\s*(\d+),\s*(\d+),\s*"(.*)"\n?$', line.strip())
            if match:
                rows[match.group(4)] = {
                    "covered": int(match.group(1)),
                    "rank": int(match.group(2)),
                    "rankpts": int(match.group(3)),
                }
    if not rows:
        raise RuntimeError(f"No rank rows parsed from output:\n{open(filename, encoding='latin-1').read()}")
    return rows


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

expectations = {
    "covergroup": (cg_cov, line_cov),
    "line": (line_cov, cg_cov),
    "branch": (line_cov, cg_cov),
}

for filter_type, (winner, loser) in expectations.items():
    logfile = test.obj_dir + f"/rank_{filter_type}.log"
    test.run(cmd=[
        os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
        "--rank",
        "--filter-type",
        filter_type,
        cg_cov,
        line_cov,
    ],
             logfile=logfile,
             tee=False,
             verilator_run=True)

    rows = parse_rank_log(logfile)
    if winner not in rows or loser not in rows:
        raise RuntimeError(f"Missing expected files in {filter_type} rank output:\n{rows}")
    if rows[winner]["covered"] <= 0:
        raise RuntimeError(f"{filter_type} winner had no covered points:\n{rows}")
    if rows[winner]["rank"] != 1 or rows[winner]["rankpts"] <= 0:
        raise RuntimeError(f"{filter_type} winner was not ranked first:\n{rows}")
    if rows[loser]["covered"] != 0 or rows[loser]["rank"] != 0 or rows[loser]["rankpts"] != 0:
        raise RuntimeError(f"{filter_type} loser was not fully filtered out:\n{rows}")

test.passes()
