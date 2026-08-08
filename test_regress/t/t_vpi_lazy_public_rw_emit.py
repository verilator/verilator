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

# Unpacked aggregates emitted via residual per-statement member expansion.
test.compile(
    verilator_flags2=["--vpi --vpi-lazy-public-rw --stats -Wno-MULTIDRIVEN -Wno-UNOPTFLAT"])

syms = test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp"
test.file_grep(syms,
               r'varInsert\("us_sig\.m", &\(TOP\.top__DOT__us_sig\.__PVT__m\), false, VLVT_UINT8')
test.file_grep(syms,
               r'varInsert\("us_sig\.n", &\(TOP\.top__DOT__us_sig\.__PVT__n\), false, VLVT_UINT8')
test.file_grep(
    syms, r'varInsert\("usarr\.m", &\(TOP\.top__DOT__usarr\[0\]\.__PVT__m\), false, VLVT_UINT8')

test.file_grep(
    syms, r'"o", offsetof\([^,]+, __Vlazyrecon__\S*__DOT__o\), VLVT_UINT8, '
    r'\(\(VLVD_NODIR\)\|VLVF_PUB_RD\|VLVF_LAZY_PUBLIC_RW\)')

test.passes()
