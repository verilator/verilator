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

lazy_flags = ("--exe --vpi --vpi-lazy --no-l2name --no-timing"
              " -Wno-MULTIDRIVEN -Wno-UNOPTFLAT -Wno-WIDTHTRUNC -Wno-WIDTHEXPAND"
              " -Wno-UNUSEDSIGNAL -Wno-BLKANDNBLK -Wno-ALWCOMBORDER -Wno-UNUSED"
              " -Wno-SPLITVAR")

test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=[lazy_flags + " --stats", test.pli_filename],
             make_flags=["-B"])

test.execute()

syms = test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp"
root = test.obj_dir + "/" + test.vm_prefix + "___024root.h"

# Totals across all bail/retain corners in this file.
test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 59)
test.file_grep(test.stats, r'VPI, lazy copy descriptors\s+(\d+)', 19)
test.file_grep(test.stats, r'VPI, lazy folded copy cones\s+(\d+)', 3)
test.file_grep(test.stats, r'VPI, lazy fallback retained\s+(\d+)', 31)

# __Vlazyepoch is sized to the module's cone count; copy and folded rows take no slot.
test.file_grep(root, r'VlUnpacked<QData/\*63:0\*/,\s*31>\s*__Vlazyepoch;')

# dimcap: 'wide' is over the VPI table cap so must retain; 'narrow' is a table row.
test.file_grep(syms, r'varInsert\("wide",.*VLVF_LAZY_RETAINED')
test.file_grep(syms, r'\{"narrow", offsetof\(\S+ __Vlazyrecon__\d+_\d+\).*VLVF_LAZY_PUBLIC_RW')

# foldcopy: the folded row calls its source cone's func, then copies that cone's shadow.
test.file_grep(
    syms, r'\{&\S+__Vlazy_reconstruct\S*, offsetof\(\S+ \S*__Vlazyrecon__\d+_\d+\),'
    r' VLVF_LAZY_FOLD\}')

# copyalias: a pure alias of a flop emits a copy descriptor - no func, no thunk.
test.file_grep(syms, r'\{nullptr, offsetof\(\S+ \S*cpy_src\), VLVF_LAZY_COPY\}')

# realcopy: a real or string row has no memcpy width, so it stays a cone whatever its source -
# neither the copy of a stored flop nor the fold of another cone may take a descriptor.
test.file_grep(syms, r'\{"rc_alias", offsetof\(\S+ __Vlazyrecon__\d+_\d+\).*VLVF_LAZY_PUBLIC_RW')
test.file_grep(syms, r'\{"sc_alias", offsetof\(\S+ __Vlazyrecon__\d+_\d+\).*VLVF_LAZY_PUBLIC_RW')
test.file_grep(syms, r'\{"rf_mid", offsetof\(\S+ __Vlazyrecon__\d+_\d+\).*VLVF_LAZY_PUBLIC_RW')
test.file_grep(syms, r'\{"sf_mid", offsetof\(\S+ __Vlazyrecon__\d+_\d+\).*VLVF_LAZY_PUBLIC_RW')
test.file_grep_not(syms, r'\{nullptr, offsetof\(\S+ \S*[rs]c_src\), VLVF_LAZY_COPY\}')

# partialmem: element 0 alone leaves the rest unproven, so the array keeps its own storage
test.file_grep(syms, r'"mem_part",.*VLVF_LAZY_RETAINED')

# mdcover: unequal, mixed-direction, non-zero-based dims whose every element is covered - one of
# them by two adjacent packed slices - reconstruct; one uncovered byte anywhere sends the whole
# array back to its own storage, rather than have a seeded zero stand in for an undriven bit.
test.file_grep(syms, r'\{"md_full", offsetof\(\S+ __Vlazyrecon__\d+_\d+\).*VLVF_LAZY_PUBLIC_RW')
test.file_grep(syms, r'"md_gap",.*VLVF_LAZY_RETAINED')

# chandle: write-only retention, via the floor.
test.file_grep(test.stats, r'VPI, lazy floor residual, sequential\s+(\d+)', 2)

# floor: retains orphan with read-write entry; 'p' survives split_var refusal.
test.file_grep(test.stats, r'VPI, lazy floor retained\s+(\d+)', 6)
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

# Freshness stamps must start stale, so the same testbench passes under --x-initial, which
# otherwise seeds them with garbage.
test.vm_prefix = "Vt_vpi_lazy_corners_xinitial"
test.compile(make_top_shell=False,
             make_main=False,
             verilator_flags2=[lazy_flags + " --x-initial unique", test.pli_filename],
             make_flags=["-B"])
test.execute(executable=test.obj_dir + "/" + test.vm_prefix)

test.passes()
