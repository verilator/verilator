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

n = 0

for prog in [
        # See also t_flag_help.py
        os.environ["VERILATOR_ROOT"] + "/bin/verilator",
        os.environ["VERILATOR_ROOT"] + "/bin/verilator_coverage",
        #os.environ["VERILATOR_ROOT"] + "/bin/verilator_difftree",
        #os.environ["VERILATOR_ROOT"] + "/bin/verilator_gantt",
        #os.environ["VERILATOR_ROOT"] + "/bin/verilator_profcfunc",
]:
    n += 1
    log_filename = test.obj_dir + "/vlt_" + str(n) + ".log"
    test.run(fails=False,
             cmd=["perl", prog, "--version"],
             tee=test.verbose,
             logfile=log_filename,
             verilator_run=True)
    test.file_grep(log_filename, r'Verilator')

    n += 1
    log_filename = test.obj_dir + "/vlt_" + str(n) + ".log"
    test.run(fails=False,
             cmd=["perl", prog, "-V"],
             tee=test.verbose,
             logfile=log_filename,
             verilator_run=True)
    test.file_grep(log_filename, r'Verilator')

test.passes()
