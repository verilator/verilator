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
test.top_filename = "t/t_vpi_comb_corners.v"
test.golden_filename = "t/t_vpi_comb_corners.out"
test.pli_filename = "t/t_vpi_dump.cpp"

# --x-initial unique: freshness stamps must start stale rather than seeded with garbage.
test.compile(make_top_shell=False,
             make_main=False,
             make_pli=True,
             verilator_flags2=[
                 "--exe --vpi --timing --vpi-lazy --no-l2name --stats --x-initial unique",
                 test.pli_filename, "t/TestVpiMain.cpp"
             ],
             make_flags=['CPPFLAGS_ADD=-DVL_NO_LEGACY'])

test.execute(use_libvpi=True, expect_filename=test.golden_filename)

syms = test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp"
root = test.obj_dir + "/" + test.vm_prefix + "___024root.h"

test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 25)
test.file_grep(test.stats, r'VPI, lazy fallback retained\s+(\d+)', 13)

# __Vlazyepoch is sized to the module's cone count; copy and folded rows take no slot.
test.file_grep(root, r'VlUnpacked<QData/\*63:0\*/,\s*22>\s*__Vlazyepoch;')

# 'wide' is over the VPI table cap so keeps its storage, read-only as it is comb-driven;
# 'narrow' is a table row.
test.file_grep(syms, r'varInsert\("wide",.*VLVF_PUB_RD\|VLVF_LAZY_COMB')
test.file_grep(syms, r'\{"narrow", offsetof\(\S+ __Vlazyrecon__\d+_\d+\).*VLVF_LAZY_REMAT')

# A real or string row has no memcpy width, so it stays a cone whatever its source - neither
# the copy of a stored flop nor the fold of another cone may take a descriptor.
test.file_grep(syms, r'\{"rc_alias", offsetof\(\S+ __Vlazyrecon__\d+_\d+\).*VLVF_LAZY_REMAT')
test.file_grep(syms, r'\{"sc_alias", offsetof\(\S+ __Vlazyrecon__\d+_\d+\).*VLVF_LAZY_REMAT')
test.file_grep(syms, r'\{"rf_mid", offsetof\(\S+ __Vlazyrecon__\d+_\d+\).*VLVF_LAZY_REMAT')
test.file_grep(syms, r'\{"sf_mid", offsetof\(\S+ __Vlazyrecon__\d+_\d+\).*VLVF_LAZY_REMAT')
test.file_grep_not(syms, r'\{nullptr, offsetof\(\S+ \S*[rs]c_src\), VLVF_LAZY_COPY\}')

# Element 0 alone leaves the rest of 'mem_part' unproven, so the array keeps its own storage
test.file_grep(syms, r'"mem_part",.*VLVF_LAZY_RETAINED')

# Unequal, mixed-direction, non-zero-based dims whose every element is covered - one of them by
# two adjacent packed slices - reconstruct; one uncovered byte anywhere sends the whole array
# back to its own storage, rather than have a seeded zero stand in for an undriven bit.
test.file_grep(syms, r'\{"md_full", offsetof\(\S+ __Vlazyrecon__\d+_\d+\).*VLVF_LAZY_REMAT')
test.file_grep(syms, r'"md_gap",.*VLVF_LAZY_RETAINED')

# Full coverage over differing select depths reconstructs (V3Slice clones the whole-row assign
# into per-element assigns before the seeder ever sees it).
test.file_grep(syms, r'\{"mixdep", offsetof\(\S+ __Vlazyrecon__\d+_\d+\).*VLVF_LAZY_REMAT')

# Write-only state, the chandle among it, is retained via the floor.
test.file_grep(test.stats, r'VPI, lazy floor residual, sequential\s+(\d+)', 3)

# The floor retains 'orphan' with a read-write entry; 'p' survives split_var refusal, read-only.
test.file_grep(test.stats, r'VPI, lazy floor retained\s+(\d+)', 13)
test.file_grep(syms, r'"orphan",.*VLVF_PUB_RW')
test.file_grep(syms, r'"p",.*VLVF_PUB_RD\|VLVF_LAZY_COMB')
test.file_grep(test.stats, r'VPI, lazy group bail, partial mixed write\s+(\d+)', 1)

# The port net inlining leaves with both drivers is retained read-only; 'w' copies it, and 'r'
# is reconstructed.
test.file_grep(syms, r'"y", offsetof\(\S+ t__DOT__u_wdrv__DOT__y\).*VLVF_PUB_RD\|VLVF_LAZY_COMB')
test.file_grep(syms, r'"w", offsetof\(\S+ __Vlazyrecon__\d+_\d+\).*VLVF_NET')
test.file_grep(syms, r'"r", offsetof\(\S+ __Vlazyrecon__\d+_\d+\).*VLVF_CONTINUOUSLY')

# Forceable signals are excluded from lazy handling, and keep the residual path.
test.file_grep(syms, r'forceableVarInsert\("frc",.*VLVF_FORCEABLE')
test.file_grep(syms, r'forceableVarInsert\("frc2",.*VLVF_FORCEABLE')
test.file_grep_not(syms, r'"frc",[^\n]*VLVF_LAZY_REMAT')
test.file_grep_not(syms, r'"frc2",[^\n]*VLVF_LAZY_REMAT')

# An explicit public_flat_rd cone operand is pinned read-only, never PUB_RW
test.file_grep(syms, r'"rdpin",[^\n]*VLVF_PUB_RD')
test.file_grep_not(syms, r'"rdpin",[^\n]*VLVF_PUB_RW')

test.passes()
