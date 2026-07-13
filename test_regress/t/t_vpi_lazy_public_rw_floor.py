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

# -Wno-UNUSED: 'orphan' is deliberately undriven and unread.
test.compile(
    make_top_shell=False,
    make_main=False,
    verilator_flags2=["--exe --vpi --vpi-lazy-public-rw --stats -Wno-UNUSED", test.pli_filename])

test.execute()

syms = test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp"

# Floor retains orphan with read-write entry.
test.file_grep(test.stats, r'VPI, lazy floor retained\s+(\d+)', 1)
test.file_grep(syms, r'"orphan",.*VLVF_PUB_RW')

# Perf win preserved: recon still reconstructed.
test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 1)
# No fallback retention.
test.file_grep(test.stats, r'VPI, lazy fallback retained\s+(\d+)', 0)

test.passes()
