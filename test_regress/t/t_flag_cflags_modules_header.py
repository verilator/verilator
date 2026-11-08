#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
import glob
import os
import re
import vltest_bootstrap

test.scenarios('simulator')
test.clean_objs()
cxx = os.environ.get('CXX', 'c++')
if not re.search(r'\(GCC\) (\d+)', test.cxx_version):
    test.skip('Requires GCC for C++ header units')
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
    test.t_dir + '/t_flag_cflags_modules_header.cpp',
    '-CFLAGS',
    '-std=c++23',
    '-CFLAGS',
    '-fmodules',
    '-CFLAGS',
    '-fmodule-header',
]
test.compile(make_main=False,
             verilator_flags2=flags,
             make_flags=['VM_PARALLEL_BUILDS=1'])
if not glob.glob(test.obj_dir + '/gcm.cache/**/t_flag_cflags_modules_header.h.gcm',
                 recursive=True):
    test.error('No C++ header unit CMI generated')
test.execute()
test.passes()
