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

# Multi-instance: iface and sub classes dedup shadow storage per-instance.
test.file_grep_count(test.obj_dir + "/" + test.vm_prefix + "_iface_t.h", r'__Vlazyrecon__', 2)
test.file_grep_count(test.obj_dir + "/" + test.vm_prefix + "_sub.h", r'__Vlazyrecon__', 2)

# Reconstructed: 10 total (iface+sub instances), 6 members per-module, 0 comb.
test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 10)
test.file_grep(test.stats, r'VPI, lazy reconstructed members\s+(\d+)', 6)
test.file_grep(test.stats, r'VPI, lazy comb reconstructed\s+(\d+)', 0)

test.file_grep(test.stats, r'VPI, lazy write-only retained\s+(\d+)', 2)
test.file_grep(test.stats, r'VPI, lazy fallback retained\s+(\d+)', 6)
test.file_grep(test.stats, r'VPI, lazy floor retained\s+(\d+)', 1)
test.file_grep(test.stats, r'VPI, lazy public rw variables\s+(\d+)', 4)

test.file_grep(test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp", r'VLVF_LAZY_PUBLIC_RW')

# One reconstruct func per (module, var), shared by both 'sub' instances: the
# sub class emits exactly the two funcs for s1 and s2, not two per instance.
sub_slow = test.obj_dir + "/" + test.vm_prefix + "_sub__0__Slow.cpp"
test.file_grep_count(sub_slow, r'void \S*__Vlazy_reconstruct____PVT__s\d+\(', 2)
# Per-instance dispatch: the two 'sub' instances get two recon-fn arrays in the
# symbol table, each pointing at that one shared pair of funcs.
syms_slow = test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp"
test.file_grep_count(syms_slow, r'_sub__VlazyReconFns\d+\[\]', 2)

test.passes()
