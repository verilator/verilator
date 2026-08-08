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
    verilator_flags2=["--exe --vpi --vpi-lazy-public-rw --no-l2name --stats", test.pli_filename])

test.execute()

# frc has a pure full-width continuous driver, so absent the forceable
# metacomment it would be lazily reconstructed; retainableKind() excludes
# forceable vars, so it must take its own (pre-existing) residual path.
test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 0)
test.file_grep(test.stats, r'VPI, lazy fallback retained\s+(\d+)', 0)

syms_slow = test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp"
test.file_grep(syms_slow, r'forceableVarInsert\("frc",.*VLVF_FORCEABLE')
test.file_grep_not(syms_slow, r'VLVF_LAZY_PUBLIC_RW')

test.passes()
