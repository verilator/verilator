#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile(verilator_flags2=['--binary --coverage-line'])

test.execute(all_run_flags=[" +verilator+coverage+file+" + test.obj_dir + "/coverage_renamed.dat"])

test.files_identical_sorted(test.obj_dir + "/coverage_renamed.dat", "t/t_cover_main.out")
test.passes()
