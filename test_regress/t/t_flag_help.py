#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('dist')

# See also t_flag_version.py


def check(prog):
    logfile = test.obj_dir + "/t_help__" + os.path.basename(prog) + ".log"

    # Not using logfile=logfile as would invoke PAGER
    test.run(fails=False,
             cmd=[prog, "--help", ">", logfile, "2>&1"],
             tee=False,
             verilator_run=True)

    test.file_grep(logfile, r'(DISTRIBUTION|usage:)')


check(os.environ["VERILATOR_ROOT"] + "/bin/verilator")
check(os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage")

check(os.environ["VERILATOR_ROOT"] + "/bin/verilator_ccache_report")
check(os.environ["VERILATOR_ROOT"] + "/bin/verilator_gantt")
check(os.environ["VERILATOR_ROOT"] + "/bin/verilator_profcfunc")

if os.path.exists(os.environ["VERILATOR_ROOT"] + "/bin/verilator_difftree"):
    check(os.environ["VERILATOR_ROOT"] + "/bin/verilator_difftree")

test.passes()
