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

test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=["--exe --vpi --vpi-lazy --no-l2name --stats", test.pli_filename])

test.execute()

test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 14)
test.file_grep(test.stats, r'VPI, lazy groups\s+(\d+)', 9)
test.file_grep(test.stats, r'VPI, lazy deposit guards\s+(\d+)', 11)

syms = test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp"

# The three 'pair' rows are one cone, which is what the testbench's sibling checks rest on: a
# deposit into the middle row leaves a row on each side of it in the same reconstruction.
test.file_grep(syms, r'\{"pair_a", offsetof\(\S+ __Vlazyrecon__\d+_0\)')
test.file_grep(syms, r'\{"pair_b", offsetof\(\S+ __Vlazyrecon__\d+_1\)')
test.file_grep(syms, r'\{"pair_c", offsetof\(\S+ __Vlazyrecon__\d+_2\)')

# Every row the testbench deposits into must be a reconstructed cone row, not retained storage:
# retained, the puts would stick for reasons that have nothing to do with the deposit word and
# the whole file would be vacuous.
test.file_grep(syms, r'\{"bin_row", offsetof\(\S+ __Vlazyrecon__\d+_\d+\)')
test.file_grep(syms, r'\{"bin_dep", offsetof\(\S+ __Vlazyrecon__\d+_\d+\)')
test.file_grep(syms, r'\{"r_row", offsetof\(\S+ __Vlazyrecon__\d+_\d+\), VLVT_REAL')
test.file_grep(syms, r'\{"r_dep", offsetof\(\S+ __Vlazyrecon__\d+_\d+\), VLVT_REAL')
test.file_grep(syms, r'\{"arr", offsetof\(\S+ __Vlazyrecon__\d+_\d+\)')
# t.keep is the storage the testbench bumps the epoch with
test.file_grep(syms, r'"keep",[^\n]*VLVF_LAZY_RETAINED')

srcs = test.glob_some(test.obj_dir + "/" + test.vm_prefix + "*__Slow.cpp")

# Per row, not per function: a row that is not its cone's first still carries its own deposit
# guard, so a deposit into one row cannot freeze the rows around it.
test.file_grep_any(
    srcs, r'if \(+vlSelfRef.__Vlazydep\[\d+U?\] != vlSymsp->__Vm_lazyDepStamp\)+ \{\n'
    r'\s*vlSelfRef.__Vlazyrecon__\d+_1 =')
test.file_grep_any(
    srcs, r'if \(+vlSelfRef.__Vlazydep\[\d+U?\] != vlSymsp->__Vm_lazyDepStamp\)+ \{\n'
    r'\s*vlSelfRef.__Vlazyrecon__\d+_2 =')

test.passes()
