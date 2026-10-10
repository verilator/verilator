#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vltmt')
test.top_filename = "t/t_threads_trigger_word.v"
test.sim_time = 3000

# This test makes randomly named .cpp/.h files, which tend to collect, so remove them first
for filename in (glob.glob(test.obj_dir + "/*_PS*.cpp") + glob.glob(test.obj_dir + "/*_PS*.h") +
                 glob.glob(test.obj_dir + "/*.d")):
    test.unlink_ok(filename)

test.compile(make_flags=['VM_PARALLEL_BUILDS=1'],
             verilator_flags2=["--protect-ids", "--protect-key SECRET_KEY"],
             threads=2)

# The exec graph refers to the model's functions by their protected names
for filename in test.glob_some(test.obj_dir + "/*.cpp"):
    test.file_grep_not(filename, r'runExecGraph|nba_mtask')

test.execute()

test.passes()
