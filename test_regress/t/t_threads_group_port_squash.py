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

prefix = test.vm_prefix
combined = {}
# Configuration, and the number of input ports of 'tile' kept, or None for no statistic
# (a braced thread list limits a squash to those counts; this test uses 2 threads)
for vlt, kept in [(None, 3), ("t/t_threads_group_port_squash.vlt", 1),
                  ("t/t_threads_group_port_squash_threads.vlt", 2),
                  ("t/t_threads_group_port_squash_all.vlt", None)]:
    test.clean_objs()
    test.vm_prefix = prefix + f"_{kept}"
    test.stats = f"{test.obj_dir}/{test.vm_prefix}__stats.txt"
    test.compile(verilator_flags2=["--binary", "--stats"] + ([vlt] if vlt else []), threads=2)
    test.execute()
    if kept is None:
        test.file_grep_not(test.stats, r'Threads group, kept input ports')
    else:
        test.file_grep(test.stats, r'Threads group, kept input ports\s+(\d+)', kept)
    combined[kept] = int(test.file_grep(test.stats, r'Optimizations, Combined CFuncs\s+(\d+)')[0])

# Kept ports make the instances' code identical, so more of it is shared
assert combined[3] > combined[None], combined

test.passes()
