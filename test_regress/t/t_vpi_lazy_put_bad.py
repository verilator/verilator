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

test.file_grep(test.stats, r'VPI, lazy comb masked\s+(\d+)', 17)
test.file_grep(test.stats, r'VPI, lazy group bail, partial gap\s+(\d+)', 2)
# Dead stores are pruned from a reconstruction, and an unpacked struct member lvalue bails
test.file_grep(test.stats, r'VPI, lazy pruned statements\s+(\d+)', 3)
test.file_grep(test.stats, r'VPI, lazy group bail, unsupported statement\s+(\d+)', 1)
test.file_grep(test.stats, r'VPI, lazy localized temps\s+(\d+)', 5)

syms = test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp"
# An alias of a flop, which keeps its storage, copies it through a descriptor: no func, no thunk
test.file_grep(syms, r'\{nullptr, offsetof\(\S+ t__DOT__k_q\), VLVF_LAZY_COPY\}')
# Alias rows keep their own net-ness and packed dimensions
test.file_grep(syms, r'\{"al_nw",[^\n]*VLVF_NET')
test.file_grep_not(syms, r'\{"al_sw",[^\n]*VLVF_NET')
test.file_grep(syms, r'\{"pk_al",[^\n]*, 0, 2, \{1, 0, 7, 0, 0, 0\}, \d+\}')
# A one-statement comb copy of a cone, and each sibling alias of one, reads that cone's shadow
shadow = r'", offsetof\(\S+ (__Vlazyrecon__\d+_\d+)\)'
for src, copies in (("fold_c", ("fmid_c", )), ("ch1", ("sib_b", "sib_c"))):
    cone = test.file_grep(syms, r'\{"' + src + shadow)
    if cone:
        for name in copies:
            test.file_grep(syms, r'\{"' + name + shadow, cone[0])

# Vacuous unless 'ret_c' keeps its storage and 'mid_c' is rebuilt on read
test.file_grep(syms, r'"ret_c",[^\n]*VLVF_LAZY_COMB')
test.file_grep(syms, r'\{"mid_c", offsetof\(\S+ __Vlazyrecon__\d+_\d+\)')

test.execute(expect_filename=test.golden_filename)

test.passes()
