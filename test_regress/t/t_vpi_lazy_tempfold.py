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

test.execute()

syms = test.obj_dir + "/" + test.vm_prefix + "__Syms__Slow.cpp"

# 'o' is a port: no reconstruction, ordinary storage, and so never a group target.
test.file_grep(syms, r'\{"o", offsetof\(\S+_tempsrc, o\),[^\n]*VLVD_OUT')
test.file_grep_not(syms, r'"o",[^\n]*VLVF_LAZY_PUBLIC_RW')

# It is a solely written temp of the group reconstructing 'mix', with a shadow of its own -
# without that shadow a fold onto it would abort rather than emit a wrong value.
test.file_grep(test.obj_dir + "/" + test.vm_prefix + "_tempsrc.h", r'__Vlazyrecon__t\d+;')

# Both copies of it keep cones of their own. Folding either onto that temp shadow would
# emit '{nullptr, offsetof(shadow)}': a row refreshed by nothing.
test.file_grep(syms, r'\{"cpy_a", offsetof\(\S+ __Vlazyrecon__\d+_\d+\)[^\n]*VLVF_LAZY_PUBLIC_RW')
test.file_grep(syms, r'\{"cpy_c", offsetof\(\S+ __Vlazyrecon__\d+_\d+\)[^\n]*VLVF_LAZY_PUBLIC_RW')
test.file_grep(test.stats, r'VPI, lazy folded copy cones\s+(\d+)', 0)

test.passes()
