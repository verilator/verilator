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

# Phase 1: comb reconstructed (3), boundary (1), floor (1).
test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 3)
test.file_grep(test.stats, r'VPI, lazy fallback retained\s+(\d+)', 1)
test.file_grep(test.stats, r'VPI, lazy floor retained\s+(\d+)', 1)
test.file_grep(test.stats, r'VPI, lazy public rw variables\s+(\d+)', 3)
test.file_grep(test.stats, r'VPI, lazy write-only retained\s+(\d+)', 1)

# Phase 2: alias nets retargeted.
test.file_grep(test.stats, r'VPI, lazy alias retargeted\s+(\d+)', 8)

test.file_grep(test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp", r'VLVF_LAZY_PUBLIC_RW')
test.file_grep(test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp",
               r'__Vm_lazyReconstructDatap')
test.file_grep(test.obj_dir + "/" + test.vm_prefix + "__Syms.h", r'__Vlazy_reconstruct')

test.passes()
