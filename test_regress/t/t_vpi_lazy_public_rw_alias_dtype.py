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

syms = test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp"

# 12 retargeted aliases
test.file_grep(test.stats, r'VPI, lazy alias retargeted\s+(\d+)', 12)
test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 0)
test.file_grep(test.stats, r'VPI, lazy fallback retained\s+(\d+)', 0)

test.file_grep(syms, r'"a_sign",.*VLVF_PUB_RW')
test.file_grep(syms, r'"a_enum",.*VLVF_PUB_RW')
test.file_grep(syms, r'"a_ii",.*VLVF_PUB_RW')
test.file_grep(syms, r'"a_ssign",.*VLVF_PUB_RW')
test.file_grep(syms, r'"a_bit",.*VLVF_PUB_RW')

# Alias reports own metadata flags (sign/bitvar), not canonical's
test.file_grep_not(syms, r'"a_sign",[^\n]*& ~VLVF_SIGNED\)\|VLVF_SIGNED')
test.file_grep(syms, r'"a_ssign",[^\n]*& ~VLVF_SIGNED\)\|VLVF_SIGNED')
test.file_grep(syms, r'"a_bit",[^\n]*& ~VLVF_BITVAR\)\|VLVF_BITVAR')
test.file_grep_not(syms, r'"a_enum",[^\n]*& ~VLVF_BITVAR\)\|VLVF_BITVAR')

test.passes()
