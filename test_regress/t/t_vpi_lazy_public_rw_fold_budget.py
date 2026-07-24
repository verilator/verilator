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
test.vm_prefix = "Vt_vpi_lazy_public_rw_accuracy"
test.top_filename = "t/t_vpi_lazy_public_rw_accuracy.v"
test.pli_filename = "t/t_vpi_lazy_public_rw_accuracy.cpp"

# Same design, fold budget=1
test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=[
                 "--exe --vpi --vpi-lazy-public-rw --vpi-lazy-fold-budget 1"
                 " --prefix Vt_vpi_lazy_public_rw_accuracy --no-l2name --stats"
                 " -Wno-MULTIDRIVEN", test.pli_filename
             ])

test.execute(all_run_flags=["+lazy-fold-retained"])

stats = test.obj_dir + "/" + test.vm_prefix + "__stats.txt"

# 7 comb reconstructed (budget=1)
test.file_grep(stats, r'VPI, lazy comb reconstructed\s+(\d+)', 7)
test.file_grep(stats, r'VPI, lazy fallback retained\s+(\d+)', 16)
# 14 reconstructed (unaffected by fold budget)
test.file_grep(stats, r'VPI, lazy reconstructed\s+(\d+)', 14)

test.passes()
