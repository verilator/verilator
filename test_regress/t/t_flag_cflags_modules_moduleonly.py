#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
import os
import re
import vltest_bootstrap

test.scenarios('simulator')
test.clean_objs()
cxx = os.environ.get('CXX', 'c++')
if not re.search(r'\(GCC\) (\d+)', test.cxx_version):
    test.skip('Requires GCC for C++ module builds')
with open(test.obj_dir + '/empty.cpp', 'w', encoding='utf8'):
    pass
test.run_capture('cd ' + test.obj_dir + ' && ' + cxx + ' -std=c++23 -fmodules -MM'
                 ' -fdeps-format=p1689r5 -fdeps-file=empty.deps.json'
                 ' -fdeps-target=empty.o -fsyntax-only empty.cpp',
                 check=False)
if not os.path.exists(test.obj_dir + '/empty.deps.json'):
    test.skip('Requires a compiler with P1689 C++ module dependency scanning')
flags = [
    '--exe',
    '--main',
    test.t_dir + '/t_flag_cflags_modules_moduleonly.cppm',
    '-CFLAGS',
    '-std=c++23',
    '-CFLAGS',
    '-fmodules',
    '-CFLAGS',
    '-fmodule-only',
]
test.compile(make_main=False,
             verilator_flags2=flags,
             make_flags=['VM_PARALLEL_BUILDS=1'])
test.glob_some(test.obj_dir + '/gcm.cache/*.gcm')
if os.path.exists(test.obj_dir + '/t_flag_cflags_modules_moduleonly.o'):
    test.error('-fmodule-only generated a module interface object file')
test.passes()
