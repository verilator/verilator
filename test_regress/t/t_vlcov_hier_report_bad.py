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

open(log, "w").close()


def run_bad(label, args):
    with open(log, "a") as log_fh:
        if log_fh.tell():
            log_fh.write("\n")
        log_fh.write("$ " + label + "\n")

    test.run(cmd=[vlcov, *args], logfile=tmp_log, fails=True, tee=False, verilator_run=True)

    with open(tmp_log) as in_fh:
        text = in_fh.read()
    text = re.sub(r"verilator_doc[.]html[?]v=[^ ]+", "verilator_doc.html?v=latest", text)
    with open(log, "a") as log_fh:
        log_fh.write(text)


run_bad("verilator_coverage --report hierarchy t/t_vlcov_merge.out",
        ["--report", "hierarchy", "t/t_vlcov_merge.out"])
run_bad("verilator_coverage --report html t/t_cover_hier.out",
        ["--report", "html", "t/t_cover_hier.out"])
run_bad("verilator_coverage --report hierarchy --levels -1 t/t_cover_hier.out",
        ["--report", "hierarchy", "--levels", "-1", "t/t_cover_hier.out"])

test.files_identical(log, test.golden_filename)

test.passes()
