#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('dist')


def check(prog):
    logfile = test.obj_dir + "/t_logfile__" + os.path.basename(prog) + ".log"

    test.run(fails=False,
             cmd=[prog, "--version", "--logfile", logfile],
             tee=False,
             verilator_run=True)

    test.file_grep(logfile, r'(Verilator [0-9]+\.[0-9]+)')


check(os.environ["VERILATOR_ROOT"] + "/bin/verilator")

test.passes()
