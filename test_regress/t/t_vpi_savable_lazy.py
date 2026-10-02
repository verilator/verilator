#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')
test.top_filename = "t/t_vpi_savable.v"
test.golden_filename = "t/t_vpi_savable.out"
test.pli_filename = "t/t_vpi_dump.cpp"

# --savable: a restore must reach reconstructed rows as it does stored ones. It excludes
# --timing, so the harness drives the clock.
test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=[
                 "--exe --vpi --vpi-lazy --savable --no-l2name --stats", "-CFLAGS -DT_VPI_SAVABLE",
                 test.pli_filename, "t/TestVpiMain.cpp"
             ],
             make_flags=['CPPFLAGS_ADD=-DVL_NO_LEGACY'])

syms = test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp"
# The deposited flops keep their own storage
for reg in ("ctrl_r", "flag_a", "cnt"):
    test.file_grep(
        syms, r'\{"' + reg + r'", offsetof\(\S+ t__DOT__' + reg + r'\),[^\n]*VLVF_LAZY_RETAINED')
# The comb status net and tree (per-element continuous assigns, read back through a variable
# index) reconstruct, not retain.
for sig in ("status", "lvl0", "lvl1", "lvl2", "picked", "ctrl_dup"):
    test.file_grep(syms, r'\{"' + sig + r'", offsetof\(\S+ __Vlazyrecon__\d+_\d+\)')

test.file_grep(syms, r'\{&\S+__Vlazy_reconstruct\S*, 0, 0\}')
# 'ctrl_dup' is a copy row, whose memo stamp is held outside the model
test.file_grep(syms, r'offsetof\(\S+ t__DOT__ctrl_r\), VLVF_LAZY_COPY\}')
# Per-element array writes (lvl0/lvl1/lvl2) reconstruct rather than bailing as unmirrorable
# lvalues.
test.file_grep_not(test.stats, r'VPI, lazy group bail, unsupported lvalue')
test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 9)
test.file_grep(test.stats, r'VPI, lazy groups\s+(\d+)', 6)

test.execute(expect_filename=test.golden_filename)

test.passes()
