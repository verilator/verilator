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
test.top_filename = "t/t_stack_check.v"

test.compile(
    verilator_flags2=['--binary --debug-stack-check', '--CFLAGS', '"-D_VL_TEST_RLIMIT_FAIL"'])

test.execute()

test.file_grep(test.run_log_filename, r'.*%Warning: System has stack size')
test.passes()
