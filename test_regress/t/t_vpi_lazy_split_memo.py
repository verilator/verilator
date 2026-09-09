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
                 "--exe --vpi --vpi-lazy --no-l2name --output-split-cfuncs 1",
                 test.pli_filename
             ])

test.execute()

srcs = test.glob_some(test.obj_dir + "/" + test.vm_prefix + "*.cpp")

# The reconstruct body was split, so the memo must not live inside it.
test.file_grep_any(srcs, r'void ' + test.vm_prefix + r'___024root__' +
                   r'__Vlazy_reconstruct_body__\d+__\d+\(')

# Epoch stamp compared and restamped in the entry function, so no body split bypasses it.
test.file_grep_any(
    srcs, r'void ' + test.vm_prefix + r'___024root____Vlazy_reconstruct__\d+\([^)]*\) \{\n'
    r'(?:.*\n)*?\s*if \(+(vlSelf->|vlSelfRef\.)__Vlazyepoch\[(\d+)U?\]'
    r' != vlSymsp->__Vm_lazyEpoch\)+ \{\n'
    r'\s*\1__Vlazyepoch\[\2U?\] = vlSymsp->__Vm_lazyEpoch;\n')

test.passes()
