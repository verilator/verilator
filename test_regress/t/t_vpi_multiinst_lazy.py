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
test.top_filename = "t/t_vpi_multiinst.v"
test.golden_filename = "t/t_vpi_multiinst.out"
test.pli_filename = "t/t_vpi_dump.cpp"

# No --vpi: the lazy tables are reachable only through VPI, so --vpi-lazy alone must build a VPI
# model rather than self-disabling. Under vltmt, reads from the thread that calls eval() behave
# as they do single-threaded.
test.compile(make_top_shell=False,
             make_main=False,
             make_pli=True,
             verilator_flags2=[
                 "--exe --timing --vpi-lazy --no-l2name --stats", test.pli_filename,
                 "t/TestVpiMain.cpp"
             ],
             make_flags=['CPPFLAGS_ADD=-DVL_NO_LEGACY'])

test.execute(use_libvpi=True, expect_filename=test.golden_filename)

syms = test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp"

# SCOPE_MODULE rows are emitted only for a VPI model.
test.file_grep(syms, r'VerilatedScope::SCOPE_MODULE')

# Interface members if_a/b/c.val and if0/if1.a/b are driven from the parent scope, so every
# instance retains. Plain-variable port connections are aliased instead (V3Inst::tryAliasPin):
# each child port is a mirror assigned in its own scope, which as a port is never a cone target.
test.file_grep(test.stats, r'VPI, lazy group bail, cross-scope write\s+(\d+)', 7)
test.file_grep(test.obj_dir + "/" + test.vm_prefix + "__Syms.h", r'__Vlazy_reconstruct')

# The `__Vcellinp__` port temps root visible ports' alias chains: helper targets, not rows.
test.file_grep(test.stats, r'VPI, lazy helper targets\s+(\d+)', 2)
test.file_grep_not(syms, r'__Vcellinp__')
test.file_grep(syms, r'"din",[^\n]*VLVF_LAZY_REMAT')
test.file_grep(syms, r'"din_copy",[^\n]*VLVF_LAZY_REMAT')

# A same-scope driver reconstructs; a cross-scope one cannot, as one loose function serves every
# instance, so it retains. xali is a plain comb alias of a cross-scope boundary: read-only under
# --vpi-lazy, so it needs no per-instance write storage and is reconstructed like any other comb
# signal. cflop is a flop, so its cross-scope alias keeps its own per-instance retained storage
# to stay writable (--public-flat-rw semantics): an entry over the canonical's could not be
# named from this module at all, or would hit the wrong instance.
test.file_grep(syms, r'\{"xali", offsetof\(\S+_parent, __PVT__xali\).*VLVF_LAZY_COMB')
test.file_grep(syms, r'\{"cflop", offsetof\(\S+_child, __PVT__cflop\).*VLVF_LAZY_RETAINED')

# canon is a same-scope comb cone (reconstructs); canonr is a same-scope flop that its xsubr
# instances' 'p' ports alias. rcanonr/scanonr are the same shape but real/string, so no memcpy
# shape exists and they stay retained.
test.file_grep(syms, r'"rcanonr",.*VLVF_LAZY_RETAINED')
test.file_grep(syms, r'"scanonr",.*VLVF_LAZY_RETAINED')

# An aliased input port is read from the parent's storage, so a cone of a multi-instance module
# reading one (uc.cy) reaches across scopes and retains, as py and xali already did.
test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 28)
test.file_grep(test.stats, r'VPI, lazy reconstructed members\s+(\d+)', 33)
test.file_grep(test.stats, r'VPI, lazy group bail, cross-scope cone\s+(\d+)', 6)
test.file_grep_not(test.stats, r'VPI, lazy floor residual, port \(comb-driven\)')

# Every port copy is now an alias, so no row is Syms-relative; the offset guard is still emitted
test.file_grep(test.stats, r'VPI, lazy cross-scope copy descriptors\s+(\d+)', 0)
test.file_grep_not(syms, r'offsetof\(\S+__Syms, [^\n]*VLVF_LAZY_COPY')
test.file_grep(syms, r'Symbol table too large for 32 bit --vpi-lazy offsets')

# bc0.bc/bc1.bc are driven only by the cross-scope assign from bflop0/bflop1, so each is a copy
# target; but bd reads bc from within the multi-instance bcell scope, where retargeting to the
# flop would reach across scopes from a function shared by every instance, so bc is pinned.
test.file_grep(test.stats, r'VPI, lazy group bail, boundary comb \(copy\)\s+(\d+)', 2)

test.passes()
