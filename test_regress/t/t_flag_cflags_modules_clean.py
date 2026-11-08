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
import vltest_bootstrap

test.scenarios('simulator')
test.clean_objs()
cxx = os.environ.get('CXX', 'c++')
with open(test.obj_dir + '/empty.cpp', 'w', encoding='utf8'):
    pass
test.run_capture('cd ' + test.obj_dir + ' && ' + cxx + ' -std=c++23 -fmodules -MM'
                 ' -fdeps-format=p1689r5 -fdeps-file=empty.deps.json'
                 ' -fdeps-target=empty.o -fsyntax-only empty.cpp',
                 check=False)
if not os.path.exists(test.obj_dir + '/empty.deps.json'):
    test.skip('Requires a compiler with P1689 C++ module dependency scanning')
test.vm_prefix = 'Vt_flag_cflags_modules_build'
test.top_filename = test.t_dir + '/t_flag_cflags_modules_build.v'
flags = [
    '--exe',
    test.t_dir + '/t_flag_cflags_modules_build_main.cpp',
    '-CFLAGS',
    '-std=c++23',
    '-CFLAGS',
    '-fmodules',
    test.t_dir + '/t_flag_cflags_modules_build.cppm',
]
test.compile(make_main=False, verilator_flags2=flags)
test.glob_some(test.obj_dir + '/gcm.cache/*.gcm')
with open(test.obj_dir + '/unused.pcm', 'w', encoding='utf8'):
    pass
test.run_capture('cd ' + test.obj_dir + ' && ' + os.environ['MAKE'] + ' -f ' + test.vm_prefix +
                 '.mk clean')
if os.path.exists(test.obj_dir + '/gcm.cache'):
    test.error('make clean did not remove gcm.cache')
if glob.glob(test.obj_dir + '/*.pcm'):
    test.error('make clean did not remove .pcm files')
test.passes()
