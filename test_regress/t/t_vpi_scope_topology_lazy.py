#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap
import glob
import re

test.scenarios('vlt_all')
test.top_filename = "t/t_vpi_scope_topology.v"
test.golden_filename = "t/t_vpi_scope_topology.out"
test.pli_filename = "t/t_vpi_dump.cpp"

test.compile(make_top_shell=False,
             make_main=False,
             make_pli=True,
             verilator_flags2=[
                 "--exe --vpi --timing --vpi-lazy --no-l2name --stats", test.pli_filename,
                 "t/TestVpiMain.cpp"
             ],
             make_flags=['CPPFLAGS_ADD=-DVL_NO_LEGACY'])

test.execute(use_libvpi=True, expect_filename=test.golden_filename)

syms = test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp"

# if0/if1.a and u0/u1.s1/s2 read their aliased input ports from the parent's storage, a
# cross-scope cone in a multi-instance module, so they retain.
test.file_grep(test.stats, r'VPI, lazy reconstructed\s+(\d+)', 37)
test.file_grep(test.stats, r'VPI, lazy fallback retained\s+(\d+)', 39)
test.file_grep(test.stats, r'VPI, lazy group bail, cross-scope cone\s+(\d+)', 6)
# intf.wdata = d is a hierarchical assign, not a port connection, so it is the one copy row
# addressed relative to the Syms object.
test.file_grep(test.stats, r'VPI, lazy cross-scope copy descriptors\s+(\d+)', 1)
test.file_grep_count(
    syms, r'\{nullptr, \(int32_t\)\(\(std::ptrdiff_t\)offsetof\(\S+__Syms, \S+\)'
    r' \+ \(std::ptrdiff_t\)offsetof\(\S+ t__DOT__d\)'
    r' - \(std::ptrdiff_t\)offsetof\(\S+__Syms, \S+__intf\)\), VLVF_LAZY_COPY\}', 1)
test.file_grep(syms, r'Symbol table too large for 32 bit --vpi-lazy offsets')
test.file_grep(test.stats, r'VPI, lazy floor residual, multidriven\s+(\d+)', 3)
test.file_grep(test.stats, r'VPI, lazy group bail, impure\s+(\d+)', 2)
# The rotated pair, plus alc_x/alc_y through u_pass1/u_pass2: two genuine comb loops. Only
# the cycle members are retained - the inlined port copies hanging off alc_x/alc_y are
# downstream of it, so they reconstruct from the retained cores.
test.file_grep(test.stats, r'VPI, lazy group bail, comb cycle\s+(\d+)', 6)
test.file_grep(test.stats, r'VPI, lazy group bail, cross-scope write\s+(\d+)', 2)
# xscope_bus.v keeps its own storage, a comb row
test.file_grep(syms, r'\{"v", offsetof\(\S+_xscope_if, v\),[^\n]*VLVF_LAZY_COMB')
# chain_tap's chain resolves past the retained pin link, so it shares chain_deep's shadow, and
# chain_use's cone must still be ordered after chain_deep's.
test.file_grep(syms, r'"chain_tap", offsetof\([^,]+, __Vlazyrecon__\d+_\d+\)')

# crbase, rndc and tstamp are all comb (variable-index write, always_comb), so under
# --vpi-lazy they are read-only, not public_flat_rw.
test.file_grep(syms, r'"crbase",.*VLVF_LAZY_COMB')
test.file_grep(syms, r'"rndc",.*VLVF_LAZY_COMB')
test.file_grep(syms, r'"tstamp",.*VLVF_LAZY_COMB')

# 'o' is a port of portsrc, no reconstruction, ordinary storage, never a group target.
test.file_grep(syms, r'\{"o", offsetof\(\S+_portsrc, o\),[^\n]*VLVD_OUT')
test.file_grep_not(syms, r'\{"o", offsetof\(\S+_portsrc, o\),[^\n]*VLVF_LAZY_REMAT')

# It is a solely written temp of the group reconstructing 'mix', with a shadow of its own -
# without that shadow a fold onto it would abort rather than emit a wrong value.
test.file_grep(test.obj_dir + "/" + test.vm_prefix + "_portsrc.h", r'__Vlazyrecon__t\d+;')

# Both copies of it keep cones of their own. Folding either onto that temp shadow would
# give a row that no func refreshes.
test.file_grep(syms, r'\{"cpy_a", offsetof\(\S+ __Vlazyrecon__\d+_\d+\)[^\n]*VLVF_LAZY_REMAT')
test.file_grep(syms, r'\{"cpy_c", offsetof\(\S+ __Vlazyrecon__\d+_\d+\)[^\n]*VLVF_LAZY_REMAT')

for filename in glob.glob(test.obj_dir + "/*Slow*.cpp"):
    with open(filename, 'r', encoding="utf8") as fh:
        infunc = False
        for line in fh:
            if re.match(r'^\S.*__Vlazy_reconstruct__', line):
                infunc = True
            elif re.match(r'^\}', line):
                infunc = False
            elif infunc and re.search(r'VL_RANDOM|VL_TIME', line):
                test.error(filename + ": reconstruct function re-executes: " + line.strip())

test.passes()
