#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
import vltest_bootstrap

test.scenarios('simulator')
test.clean_objs()
if not test.have_cxx_module_scan:
    test.skip('Requires a compiler with P1689 C++ module dependency scanning')
# -CFLAGS -fmodules enables the C++ module flow, so the compiler include must
# still reach the generated PCH and the model must still build.
flags = [
    '--compiler-include',
    test.t_dir + '/t_flag_cxx_modules_compiler_include.h',
    '-CFLAGS',
    '-std=c++23',
    '-CFLAGS',
    '-fmodules',
]
test.compile(verilator_flags2=flags, make_flags=['VM_PARALLEL_BUILDS=1'])
test.glob_some(test.obj_dir + '/*__pch.h.fast.gch')
test.execute()
test.passes()
