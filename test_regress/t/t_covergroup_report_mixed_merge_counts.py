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


def parse_counts(filename):
    counts = {}
    with open(filename, encoding="latin-1") as fh:
        for line in fh:
            match = re.match(r"^C '(.*)' (\d+)\n?$", line)
            if match:
                counts[match.group(1)] = int(match.group(2))
    return counts


def assert_doubled(single_file, doubled_file, label):
    single = parse_counts(single_file)
    doubled = parse_counts(doubled_file)
    if set(single) != set(doubled):
        raise RuntimeError(f"{label} point sets differ between single and doubled outputs")
    nonzero = 0
    for name, count in single.items():
        doubled_count = doubled[name]
        if doubled_count != 2 * count:
            raise RuntimeError(
                f"{label} point did not double as expected:\n{name}\n"
                f"single={count} doubled={doubled_count}")
        if count:
            nonzero += 1
    if nonzero == 0:
        raise RuntimeError(f"{label} output unexpectedly had no hit counts to validate")


test.scenarios('simulator')
test.top_filename = "t/t_covergroup_report_basic.v"

test.compile(verilator_flags2=['--cc', '--coverage-user'])
test.execute()

cg_cov = test.obj_dir + "/coverage_covergroup.dat"
shutil.copyfile(test.obj_dir + "/coverage.dat", cg_cov)
cg_cov_dup = test.obj_dir + "/coverage_covergroup_dup.dat"
shutil.copyfile(cg_cov, cg_cov_dup)

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
line_cov_dup = test.obj_dir + "/coverage_line_dup.dat"
shutil.copyfile(line_cov, line_cov_dup)

cg_twice = test.obj_dir + "/coverage_covergroup_twice.dat"
line_twice = test.obj_dir + "/coverage_line_twice.dat"
mixed_once = test.obj_dir + "/coverage_mixed_once.dat"
mixed_twice = test.obj_dir + "/coverage_mixed_twice.dat"

for out_file, inputs in ((cg_twice, [cg_cov, cg_cov_dup]), (line_twice, [line_cov, line_cov_dup]),
                         (mixed_once, [cg_cov, line_cov])):
    test.run(cmd=[
        os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
        "--write",
        out_file,
        *inputs,
    ],
             verilator_run=True)

mixed_once_dup = test.obj_dir + "/coverage_mixed_once_dup.dat"
shutil.copyfile(mixed_once, mixed_once_dup)
test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--write",
    mixed_twice,
    mixed_once,
    mixed_once_dup,
],
         verilator_run=True)

cg_single_filtered = test.obj_dir + "/coverage_covergroup_single_filtered.dat"
cg_twice_filtered = test.obj_dir + "/coverage_covergroup_twice_filtered.dat"
mixed_twice_cg = test.obj_dir + "/coverage_mixed_twice_covergroup.dat"
line_single_filtered = test.obj_dir + "/coverage_line_single_filtered.dat"
line_twice_filtered = test.obj_dir + "/coverage_line_twice_filtered.dat"
mixed_twice_line = test.obj_dir + "/coverage_mixed_twice_line.dat"
branch_single_filtered = test.obj_dir + "/coverage_branch_single_filtered.dat"
branch_twice_filtered = test.obj_dir + "/coverage_branch_twice_filtered.dat"
mixed_twice_branch = test.obj_dir + "/coverage_mixed_twice_branch.dat"

for filter_type, src, dst in (
        ("covergroup", cg_cov, cg_single_filtered),
        ("covergroup", cg_twice, cg_twice_filtered),
        ("covergroup", mixed_twice, mixed_twice_cg),
        ("line", line_cov, line_single_filtered),
        ("line", line_twice, line_twice_filtered),
        ("line", mixed_twice, mixed_twice_line),
        ("branch", line_cov, branch_single_filtered),
        ("branch", line_twice, branch_twice_filtered),
        ("branch", mixed_twice, mixed_twice_branch),
):
    test.run(cmd=[
        os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
        "--filter-type",
        filter_type,
        "--write",
        dst,
        src,
    ],
             verilator_run=True)

assert_doubled(cg_single_filtered, cg_twice_filtered, "covergroup")
assert_doubled(line_single_filtered, line_twice_filtered, "line")
assert_doubled(branch_single_filtered, branch_twice_filtered, "branch")

test.files_identical_sorted(mixed_twice_cg, cg_twice_filtered)
test.files_identical_sorted(mixed_twice_line, line_twice_filtered)
test.files_identical_sorted(mixed_twice_branch, branch_twice_filtered)

line_twice_info = test.obj_dir + "/coverage_line_twice.info"
mixed_twice_info = test.obj_dir + "/coverage_mixed_twice.info"
test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--write-info",
    line_twice_info,
    line_twice,
],
         verilator_run=True)
test.run(cmd=[
    os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
    "--write-info",
    mixed_twice_info,
    mixed_twice,
],
         verilator_run=True)
test.files_identical(mixed_twice_info, line_twice_info)

test.passes()
