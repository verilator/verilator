#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')

test.compile(verilator_flags2=["--binary --quiet"])

test.execute(all_run_flags=["+verilator+quiet"], logfile=test.obj_dir + "/sim__quiet.log")

test.file_grep_not(test.obj_dir + "/sim__quiet.log", r'S i m u l a t')

#---

test.execute(all_run_flags=[""], logfile=test.obj_dir + "/sim__noquiet.log")

test.file_grep(test.obj_dir + "/sim__noquiet.log", r'S i m u l a t')

test.passes()
