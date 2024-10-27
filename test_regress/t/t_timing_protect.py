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
test.top_filename = "t/t_timing_fork_join.v"  # Contains all relevant constructs

if not test.have_coroutines:
    test.skip("No coroutine support")

test.compile(verilator_flags2=["--exe --main --timing --protect-ids", "--protect-key SECRET_KEY"])

test.execute()

if test.vlt_all:
    # Check for secret in any outputs
    for filename in test.glob_some(test.obj_dir + "/*.[ch]*"):
        test.file_grep_not(filename, r'event[123]')
        test.file_grep_not(filename, r't_timing_fork_join')

test.passes()
