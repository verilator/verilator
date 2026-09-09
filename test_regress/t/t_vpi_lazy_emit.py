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
             verilator_flags2=[
                 "--exe --vpi --vpi-lazy --no-l2name --stats -Wno-MULTIDRIVEN -Wno-UNOPTFLAT",
                 test.pli_filename
             ])

test.execute()

syms = test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp"
root = test.obj_dir + "/" + test.vm_prefix + "___024root.h"

test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 27)
test.file_grep(test.stats, r'VPI, lazy alias to reconstructed\s+(\d+)', 6)
test.file_grep(test.stats, r'VPI, lazy group bail, boundary comb \(alias\)\s+(\d+)', 1)

# __Vlazyepoch is sized to the module's group count (26 here).
test.file_grep(root, r'VlUnpacked<QData/\*63:0\*/,\s*27>\s*__Vlazyepoch;')

# Unpacked aggregates emitted via residual per-member expansion.
test.file_grep(syms,
               r'varInsert\("us_sig\.m", &\(TOP\.t__DOT__us_sig\.__PVT__m\), false, VLVT_UINT8')
test.file_grep(syms,
               r'varInsert\("us_sig\.n", &\(TOP\.t__DOT__us_sig\.__PVT__n\), false, VLVT_UINT8')
test.file_grep(
    syms, r'varInsert\("usarr\.m", &\(TOP\.t__DOT__usarr\[0\]\.__PVT__m\), false, VLVT_UINT8')

# 'sub_o' reconstructs into a shadow member...
test.file_grep(
    syms, r'\{"sub_o", offsetof\([^,]+, __Vlazyrecon__\d+_\d+\), VLVT_UINT8, '
    r'\(\(VLVD_NODIR\)\|VLVF_PUB_RW\|VLVF_LAZY_PUBLIC_RW\)')
# ...and its inlined port alias 'subi.o' shares that descriptor.
test.file_grep(
    syms, r'\{"o", offsetof\([^,]+, __Vlazyrecon__\d+_\d+\), VLVT_UINT8, '
    r'.*\|VLVF_PUB_RW\|VLVF_LAZY_PUBLIC_RW\)')

# aliasmeta: an alias of a flop reconstructs into a shadow of its own rather than pointing at
# the canonical's storage, and its row still reports its own declared bounds and net-ness.
test.file_grep(syms, r'\{"a_wide", offsetof\(\S+ __Vlazyrecon__\d+_\d+\).*VLVF_LAZY_PUBLIC_RW')
test.file_grep(syms, r'\{"a_net", offsetof\(\S+ __Vlazyrecon__\d+_\d+\).*VLVF_LAZY_PUBLIC_RW')
test.file_grep(syms, r'\{"a_net",[^\n]*VLVF_NET')
# A packed-array alias keeps both of its packed dimensions in the row
test.file_grep(syms, r'\{"pa_ali",[^\n]*, 0, 2, \d+, \{1, 0, 7, 0, 0, 0\}\}')
test.file_grep_not(syms, r'\{"a_wide",[^\n]*VLVF_NET')

# alias_dtype: only the sign-mismatched alias is pinned with storage.
test.file_grep(root, r't__DOT__a_diff;')
test.file_grep_not(root, r't__DOT__a_same;')

# Each retained alias reports its own sign/bitvar flags, not the canonical's
test.file_grep(syms, r'\{"a_ssign",[^\n]*VLVF_SIGNED')
test.file_grep(syms, r'\{"a_bit",[^\n]*VLVF_BITVAR')
test.file_grep_not(syms, r'\{"a_sign",[^\n]*VLVF_SIGNED')
test.file_grep_not(syms, r'\{"a_enum",[^\n]*VLVF_BITVAR')

# An alias sharing the reconstructed canonical's descriptor is the one retargeted row left,
# and it too must carry its own metadata rather than the shadow's
test.file_grep(syms, r'\{"s_sign",[^\n]*& ~VLVF_SIGNED\)\|VLVF_SIGNED')
test.file_grep(syms, r'\{"s_bit",[^\n]*& ~VLVF_BITVAR\)\|VLVF_BITVAR')
test.file_grep(syms, r'\{"s_net",[^\n]*& ~VLVF_NET\)\|VLVF_NET')
test.file_grep_not(syms, r'\{"a_same",[^\n]*& ~VLVF_SIGNED\)\|VLVF_SIGNED')

test.passes()
