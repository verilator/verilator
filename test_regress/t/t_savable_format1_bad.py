#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import time

test.scenarios('vlt')
test.top_filename = "t/t_savable.v"

test.compile(v_flags2=["--savable"], save_time=500)

test.execute(check_finished=False, all_run_flags=['+save_time=500'])

if not os.path.exists(test.obj_dir + "/saved.vltsv"):
    test.error("Saved.vltsv not created")

time.sleep(1)
# Avoid make getting confused by very fast build

test.compile(v_flags2=["--savable -GMODEL_WIDTH=40"], save_time=500)

test.execute(all_run_flags=['+save_restore=1'], fails=True, expect_filename=test.golden_filename)

test.passes()
