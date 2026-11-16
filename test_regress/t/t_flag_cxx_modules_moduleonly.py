#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os
import vltest_bootstrap

test.scenarios('vlt')

test.clean_objs()
test.top_filename = test.t_dir + '/t_flag_cxx_modules.v'
if 'clang' in test.cxx_version.lower() or 'microsoft' in test.cxx_version.lower():
    test.skip('Requires GCC for C++ module builds')
if not test.have_cxx_module_scan:
    test.skip('Requires a compiler with P1689 C++ module dependency scanning')
flags = [
    '--exe',
    '--main',
    '--cxx-modules',
    '-CFLAGS',
    '-std=c++23',
    '-CFLAGS',
    '-fmodule-only',
    test.t_dir + '/t_flag_cxx_modules_moduleonly.cppm',
]
test.compile(make_main=False, verilator_flags2=flags, make_flags=['VM_PARALLEL_BUILDS=1'])
test.glob_some(test.obj_dir + '/gcm.cache/*.gcm')
if os.path.exists(test.obj_dir + '/t_flag_cxx_modules_moduleonly.o'):
    test.error('-fmodule-only generated a module interface object file')
test.passes()
