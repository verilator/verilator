# DESCRIPTION: Verilator: coverage test helpers
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3,
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os
import re


def vlcov_bin():
    return os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage"


def vlcov_run_context(test, log, tmp_log):
    return test, log, tmp_log


def init_log(log):
    with open(log, "w", encoding="utf-8"):
        pass


def run_vlcov(context, label, args, fails=False, normalize_errors=False):
    test, log, tmp_log = context
    with open(log, "a", encoding="utf-8") as log_fh:
        if log_fh.tell():
            log_fh.write("\n")
        log_fh.write("$ " + label + "\n")

    test.run(cmd=[vlcov_bin(), *args], logfile=tmp_log, fails=fails, tee=False, verilator_run=True)

    with open(tmp_log, encoding="utf-8") as in_fh:
        text = in_fh.read()
    if normalize_errors:
        text = re.sub(r"verilator_doc[.]html[?]v=[^ ]+", "verilator_doc.html?v=latest", text)
    with open(log, "a", encoding="utf-8") as log_fh:
        log_fh.write(text)
