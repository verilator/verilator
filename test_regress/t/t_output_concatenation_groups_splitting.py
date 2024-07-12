#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.run(
    cmd=[
        os.environ['VERILATOR_ROOT'] + "/bin/verilator", "--output-concatenation-groups", "10",
        "--debug-test-concatenation", test.t_dir + "/t_output_concatenation_groups_splitting.dat"
    ],
    logfile=test.obj_dir + "/output_concatenation_groups.log",
    expect_filename=test.golden_filename,
    tee=False,
    verilator_run=True,
    fails=False,
)

test.passes()
