#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

# Not vltmt: t_vpi_dump_value from always @(cnt) runs on a worker thread under --threads
test.scenarios('vlt')
test.top_filename = "t/t_vpi_put_order.v"
test.golden_filename = "t/t_vpi_put_order.out"
test.pli_filename = "t/t_vpi_dump.cpp"

test.compile(make_top_shell=False,
             make_main=False,
             make_pli=True,
             verilator_flags2=[
                 "--exe --vpi --timing --vpi-lazy --no-l2name --stats", test.pli_filename,
                 "t/TestVpiMain.cpp"
             ],
             make_flags=['CPPFLAGS_ADD=-DVL_NO_LEGACY'])

syms = test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp"
# The checks are vacuous unless 'dep' and 's_sum' are retained-but-comb (read-only), the other
# named rows rebuilt on read, and among those 's_copy' a copy of 's' and 's_dup' a fold
for name in ["dep", "s_sum", "init_sum", "und_sum"]:
    test.file_grep(syms, r'"' + name + r'",[^\n]*VLVF_LAZY_COMB')
# Section 6 is vacuous unless the signals no process drives are retained and writable
for name in ["init_only", "undriven", "once", "mid", "mid_seen", "cmid", "cmid_seen", "mcnd"]:
    test.file_grep(syms, r'"' + name + r'",[^\n]*VLVF_PUB_RW\|VLVF_LAZY_RETAINED\)')
for name in [
        "tri3", "watched", "s_comb", "s_copy", "s_dup", "s_mix", "in_comb", "mem_comb", "r_comb",
        "str_comb", "f_comb", "init_comb", "und_comb", "once_comb", "part_comb"
]:
    test.file_grep(syms, r'\{"' + name + r'", offsetof\(\S+ __Vlazyrecon__\d+_\d+\)')
test.file_grep(syms, r'offsetof\(\S+ t__DOT__s\), VLVF_LAZY_COPY\}')
# The fold shares its source cone's shadow; the copy of a flop may not share the flop's storage
shadow = r'", offsetof\(\S+ (__Vlazyrecon__\d+_\d+)\)'
cone = test.file_grep(syms, r'\{"s_comb' + shadow)
if cone:
    test.file_grep(syms, r'\{"s_dup' + shadow, cone[0])
# The DPI export reading mc_b pins its storage
test.file_grep(test.stats, r'VPI, lazy floor residual, storage pinned \(DPI\)\s+(\d+)', 1)

test.execute(use_libvpi=True, expect_filename=test.golden_filename)

test.passes()
