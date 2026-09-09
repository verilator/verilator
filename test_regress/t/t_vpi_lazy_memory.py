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

test.compile(
    make_top_shell=False,
    make_main=False,
    verilator_flags2=["--exe --vpi --vpi-lazy --no-l2name --stats", test.pli_filename])

test.execute()

# RAM and regs: write-only retention (no reconstruction).
test.file_grep(test.stats, r'VPI, lazy write-only retained\s+(\d+)', 3)
# Three comb unpacked arrays plus their variable-index consumer, one group each.
test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 8)
test.file_grep(test.stats, r'VPI, lazy groups\s+(\d+)', 8)
# The four top-level port aliases (t.clk/t.we/t.addr/t.wdata) are retained with storage of
# their own, so a deposit into one cannot clobber the port the testbench drives.
test.file_grep(test.stats, r'VPI, lazy fallback retained\s+(\d+)', 0)
# Per-element array writes are reconstructed, not bailed as unmirrorable lvalues.
test.file_grep_not(test.stats, r'VPI, lazy group bail, unsupported lvalue')

test.passes()
