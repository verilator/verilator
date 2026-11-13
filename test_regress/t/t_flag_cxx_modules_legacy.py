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
test.top_filename = test.t_dir + '/t_flag_cxx_modules.v'

if 'clang' in test.cxx_version.lower() or 'microsoft' in test.cxx_version.lower():
    test.skip('Requires GCC for -fmodules')
if not test.have_cxx_module_scan:
    test.skip('Requires a compiler with -fmodules')

test.compile(verilator_flags2=[
    '--compiler-include',
    test.t_dir + '/t_flag_cxx_modules_compiler_include.h',
    '-CFLAGS "-std=c++23 -fmodules"',
],
             make_flags=['VM_PARALLEL_BUILDS=1'])

test.file_grep_not(test.obj_dir + '/' + test.vm_prefix + '.mk', r'__modules\.mk')
test.glob_some(test.obj_dir + '/*__pch.h.fast.gch')

test.execute()

test.passes()
