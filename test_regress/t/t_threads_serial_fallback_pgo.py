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
test.top_filename = "t/t_threads_serial_fallback.v"

# Profile MTasks also when the falling-edge passes run them sequentially
test.compile(verilator_flags2=["--stats", "--prof-pgo", "--threads-serial-cost", "100"], threads=2)

test.file_grep(test.stats, r'Optimizations, Thread serial fallbacks\s+(\d+)', 1)

# Each MTask is profiled both by its worker thread and when run sequentially
counters = {}
for filename in test.glob_some(test.obj_dir + "/" + test.vm_prefix + "___024root*.cpp"):
    for call in re.findall(r'\b(?:start|stop)Counter\(\d+\)', test.file_contents(filename)):
        counters[call] = counters.get(call, 0) + 1
if not counters or any(count != 2 for count in counters.values()):
    test.error("Expected each MTask counter in both parallel and serial code: " + str(counters))

test.execute(all_run_flags=[
    "+verilator+prof+exec+start+0",
    " +verilator+prof+exec+file+/dev/null",
    " +verilator+prof+vlt+file+" + test.obj_dir + "/profile.vlt"])  # yapf:disable

test.file_grep(test.obj_dir + "/profile.vlt", r'profile_data -model .* -mtask')

test.passes()
