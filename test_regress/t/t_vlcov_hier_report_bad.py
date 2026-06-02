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

missing_cov = test.obj_dir + "/missing.dat"
with open(missing_cov, "w", encoding="utf-8") as fh:
    fh.write("# SystemC::Coverage-3\n")
    fh.write("C '\001f\002t/missing.v\001l\0021\001t\002line\001page\002v_line/missing' 1\n")


def run_bad(label, args):
    with open(log, "a", encoding="utf-8") as log_fh:
        if log_fh.tell():
            log_fh.write("\n")
        log_fh.write("$ " + label + "\n")

    test.run(cmd=[vlcov, *args], logfile=tmp_log, fails=True, tee=False, verilator_run=True)

    with open(tmp_log, encoding="utf-8") as in_fh:
        text = in_fh.read()
    text = re.sub(r"verilator_doc[.]html[?]v=[^ ]+", "verilator_doc.html?v=latest", text)
    with open(log, "a", encoding="utf-8") as log_fh:
        log_fh.write(text)


def run_ok(label, args):
    with open(log, "a", encoding="utf-8") as log_fh:
        if log_fh.tell():
            log_fh.write("\n")
        log_fh.write("$ " + label + "\n")

    test.run(cmd=[vlcov, *args], logfile=tmp_log, tee=False, verilator_run=True)

    with open(tmp_log, encoding="utf-8") as in_fh:
        text = in_fh.read()
    with open(log, "a", encoding="utf-8") as log_fh:
        log_fh.write(text)


run_bad("verilator_coverage --report unknown t/t_cover_hier.out",
        ["--report", "unknown", "t/t_cover_hier.out"])
run_ok("verilator_coverage --report hierarchy missing.dat", ["--report", "hierarchy", missing_cov])

test.files_identical(log, test.golden_filename)

test.passes()
