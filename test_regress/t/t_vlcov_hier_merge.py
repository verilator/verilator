#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3,
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import re

import vltest_bootstrap

test.scenarios('dist')

vlcov = os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage"
log = test.obj_dir + "/vlcov.log"
tmp_log = test.obj_dir + "/vlcov.tmp"

with open(log, "w", encoding="utf-8"):
    pass

test.run(cmd=[
    vlcov,
    "--hier-merge",
    "--write",
    test.obj_dir + "/coverage.dat",
    "t/t_cover_hier.out",
],
         verilator_run=True)

test.files_identical_sorted(test.obj_dir + "/coverage.dat", "t/t_cover_hier.out")

extra_cov = test.obj_dir + "/extra_key.dat"
with open(extra_cov, "w", encoding="utf-8") as fh:
    fh.write("# SystemC::Coverage-3\n")
    # Verify --hier-merge preserves deterministic identity when a coverage
    # point contains an unknown encoded key. Known keys should be emitted in
    # canonical order, and the unknown key should be retained afterward.
    fh.write("C '\001Z\002extra\001f\002t/edge.v\001l\0021\001t\002line"
             "\001page\002v_line/edge\001h\002top.u' 1\n")

test.run(cmd=[
    vlcov,
    "--hier-merge",
    "--write",
    test.obj_dir + "/extra_key_merged.dat",
    extra_cov,
],
         verilator_run=True)

extra_expected = test.obj_dir + "/extra_key_expected.dat"
with open(extra_expected, "w", encoding="utf-8") as fh:
    fh.write("# SystemC::Coverage-3\n")
    fh.write("C '\001f\002t/edge.v\001l\0021\001t\002line\001page\002v_line/edge"
             "\001h\002top.u\001Z\002extra' 1\n")

test.files_identical(test.obj_dir + "/extra_key_merged.dat", extra_expected)

missing_cov = test.obj_dir + "/missing.dat"
with open(missing_cov, "w", encoding="utf-8") as fh:
    fh.write("# SystemC::Coverage-3\n")
    # --hier-merge must reject missing hierarchy just as strictly as collapsed
    # hierarchy, because there is no instance identity to preserve.
    fh.write("C '\001f\002t/missing.v\001l\0021\001t\002line\001page\002v_line/missing' 1\n")


def append_bad_log(label, cmd):
    with open(log, "a", encoding="utf-8") as log_fh:
        if log_fh.tell():
            log_fh.write("\n")
        log_fh.write("$ " + label + "\n")

    test.run(cmd=cmd, logfile=tmp_log, fails=True, tee=False, verilator_run=True)

    with open(tmp_log, encoding="utf-8") as in_fh:
        text = in_fh.read()
    text = re.sub(r"verilator_doc[.]html[?]v=[^ ]+", "verilator_doc.html?v=latest", text)
    with open(log, "a", encoding="utf-8") as log_fh:
        log_fh.write(text)


def run_bad(label, args):
    append_bad_log(label, [vlcov, *args])


run_bad("verilator_coverage --hier-merge t/t_cover_hier.out",
        ["--hier-merge", "t/t_cover_hier.out"])
run_bad("verilator_coverage --hier-merge --write coverage.dat t/t_cover_lib__1.out",
        ["--hier-merge", "--write", test.obj_dir + "/bad_collapsed.dat", "t/t_cover_lib__1.out"])
append_bad_log(
    "verilator_coverage --hier-merge --write coverage.dat missing.dat",
    ["cd", test.obj_dir, "&&", vlcov, "--hier-merge", "--write", "bad_missing.dat", "missing.dat"])

test.files_identical(log, test.golden_filename)

test.passes()
