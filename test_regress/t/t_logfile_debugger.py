#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

have_gdb = 'VERILATOR_GDB' in os.environ
if not have_gdb:
    if 'VERILATOR_TEST_NO_GDB' in os.environ:
        test.skip("Skipping due to VERILATOR_TEST_NO_GDB")
    if not test.have_gdb:
        test.skip("No gdb installed")

test.compile()

logfile = test.obj_dir + "/t_logfile.log"

test.execute(all_run_flags=['+verilator+log+file+' + logfile])

# $display checks
test.file_grep(logfile, r'Hello World!')
test.file_grep(logfile, r'system\(echo In a shell now\)') # Line being run
test.file_grep(logfile, r'Hello 3rd rock!')

# $fdisplay checks
test.file_grep(logfile, r'Hello Mars!')
test.file_grep(logfile, r'system\(echo In another shell now\)') # Line being run
test.file_grep(logfile, r'Hello Pluto!')

test.passes()
