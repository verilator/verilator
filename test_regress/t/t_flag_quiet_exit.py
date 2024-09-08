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
test.top_filename = "t/t_file_does_not_exist.v"

# Tests for the error message and then the absence of the
# "Command Failed" line
test.compile(v_flags2=["--quiet-exit"], fails=True)

test.file_grep_not(test.obj_dir + "/vlt_compile.log", r'Exiting due to')
test.file_grep_not(test.obj_dir + "/vlt_compile.log", r'Command Failed')

test.passes()
