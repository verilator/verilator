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

for size in (31, 32, 33, 256):
    obj_dir = f"{test.obj_dir}/n{size}"
    test.lint(verilator_flags2=[
        "--stats", "-fdfg-synthesize-all", "-fno-split", f"-GN={size}", "-Mdir", obj_dir
    ])
    stats = f"{obj_dir}/{test.vm_prefix}__stats.txt"
    synthesized = int(size <= 32)
    test.file_grep(stats, r'DFG, Synthesis, synt / always blocks considered\s+(\d+)$', 1)
    test.file_grep(stats, r'DFG, Synthesis, synt / always blocks synthesized\s+(\d+)$',
                   synthesized)
    test.file_grep(stats, r'DFG, Synthesis, synt / non-synthesizable \(array\)\s+(\d+)$',
                   1 - synthesized)
    test.file_grep(stats, r'DFG, Synthesis, synt / reverted \(non-synthesizable\)\s+(\d+)$',
                   1 - synthesized)

test.passes()
