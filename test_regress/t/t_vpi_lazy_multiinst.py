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

syms = test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp"

# Interface member `val` is driven from the parent scope, so all three instances retain.
test.file_grep(test.stats, r'VPI, lazy group bail, cross-scope write\s+(\d+)', 7)
test.file_grep(test.obj_dir + "/" + test.vm_prefix + "__Syms.h", r'__Vlazy_reconstruct')

# The `__Vcellinp__` port temps root visible ports' alias chains: helper targets, not rows.
test.file_grep(test.stats, r'VPI, lazy helper targets\s+(\d+)', 2)
test.file_grep_not(syms, r'__Vcellinp__')
test.file_grep(syms, r'"din",[^\n]*VLVF_LAZY_PUBLIC_RW')
test.file_grep(syms, r'"din_copy",[^\n]*VLVF_LAZY_PUBLIC_RW')

# xscope: a same-scope driver reconstructs; a cross-scope one cannot, as one loose function
# serves every instance, so it retains.
# A cross-scope alias of a boundary keeps its own per-instance storage: an entry over the
# canonical's could not be named from this module at all, or would hit the wrong instance.
test.file_grep(syms, r'\{"xali", offsetof\(\S+_parent, __PVT__xali\).*VLVF_LAZY_RETAINED')
test.file_grep(syms, r'\{"cflop", offsetof\(\S+_child, __PVT__cflop\).*VLVF_LAZY_RETAINED')
test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 14)
test.file_grep(test.stats, r'VPI, lazy reconstructed members\s+(\d+)', 13)
test.file_grep(test.stats, r'VPI, lazy cross-scope retained\s+(\d+)', 4)

test.passes()
