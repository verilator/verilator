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
                 "--exe --vpi --vpi-lazy --no-l2name --stats --no-timing"
                 " -Wno-MULTIDRIVEN -Wno-UNOPTFLAT -Wno-WIDTHTRUNC -Wno-WIDTHEXPAND"
                 " -Wno-UNUSEDSIGNAL -Wno-BLKANDNBLK -Wno-ALWCOMBORDER -Wno-UNUSED"
                 " -Wno-SPLITVAR", test.pli_filename
             ])

test.execute()

syms = test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp"
root = test.obj_dir + "/" + test.vm_prefix + "___024root.h"

# Totals across all bail/retain corners in this file.
test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 49)
test.file_grep(test.stats, r'VPI, lazy fallback retained\s+(\d+)', 25)

# __Vlazyepoch is sized to the module's group count (42 here).
test.file_grep(root, r'VlUnpacked<QData/\*63:0\*/,\s*43>\s*__Vlazyepoch;')

# dimcap: 'wide' is over the VPI table cap so must retain; 'narrow' is a table row.
test.file_grep(syms, r'varInsert\("wide",.*VLVF_LAZY_RETAINED')
test.file_grep(syms, r'\{"narrow", offsetof\(\S+ __Vlazyrecon__\d+_\d+\).*VLVF_LAZY_PUBLIC_RW')

# chandle: write-only retention.
test.file_grep(test.stats, r'VPI, lazy write-only retained\s+(\d+)', 1)

# floor: retains orphan with read-write entry; 'p' survives split_var refusal.
test.file_grep(test.stats, r'VPI, lazy floor retained\s+(\d+)', 5)
test.file_grep(syms, r'"orphan",.*VLVF_PUB_RW')
test.file_grep(syms, r'"p",.*VLVF_PUB_RW')
test.file_grep(test.stats, r'VPI, lazy group bail, partial mixed write\s+(\d+)', 2)

# walkcorners: dead temp stores are pruned from the reconstruction, and the two statement
# shapes the ordered walk refuses (a kept delay, an unpacked struct member lvalue) bail.
test.file_grep(test.stats, r'VPI, lazy pruned statements\s+(\d+)', 1)
test.file_grep(test.stats, r'VPI, lazy group bail, unsupported statement\s+(\d+)', 2)
test.file_grep(test.stats, r'VPI, lazy localized temps\s+(\d+)', 1)

# multidriven: 'w' multidriven and retained; 'r' reconstructed.
test.file_grep(syms, r'"w",.*VLVF_PUB_RW')
test.file_grep(syms, r'"r", offsetof\(\S+ __Vlazyrecon__\d+_\d+\).*VLVF_CONTINUOUSLY')

# forceable: excluded from lazy handling, keeps the residual path.
test.file_grep(syms, r'forceableVarInsert\("frc",.*VLVF_FORCEABLE')
test.file_grep(syms, r'forceableVarInsert\("frc2",.*VLVF_FORCEABLE')
test.file_grep_not(syms, r'"frc",[^\n]*VLVF_LAZY_PUBLIC_RW')
test.file_grep_not(syms, r'"frc2",[^\n]*VLVF_LAZY_PUBLIC_RW')

# An explicit public_flat_rd cone operand is pinned read-only, never PUB_RW
test.file_grep(syms, r'"rdpin",[^\n]*VLVF_PUB_RD')
test.file_grep_not(syms, r'"rdpin",[^\n]*VLVF_PUB_RW')

test.passes()
