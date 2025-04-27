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

# CI environment offers 2 VCPUs, 2 thread setting causes the following warning.
# %Warning-UNOPTTHREADS: Thread scheduler is unable to provide requested parallelism; consider asking for fewer threads.
# So use 6 threads here though it's not optimal in performance, but ok.
test.compile(verilator_flags2=['--stats', test.t_dir + "/t_split_var_0.vlt"],
             threads=(6 if test.vltmt else 1))

test.execute()

test.file_grep(test.stats, r'SplitVar,\s+packed variables split automatically\s+(\d+)', 0)
test.file_grep(test.stats, r'SplitVar,\s+packed variables split due to attribute\s+(\d+)', 15)
test.file_grep(test.stats, r'SplitVar,\s+unpacked arrays split due to attribute\s+(\d+)', 27)
test.passes()
