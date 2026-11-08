#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
import os
import shutil
import vltest_bootstrap

test.scenarios('simulator')
test.clean_objs()
cxx = os.path.basename(os.environ.get('CXX', 'c++'))
if cxx.lower() not in ('cl', 'cl.exe'):
    test.skip('Requires MSVC')
if not test.have_cmake:
    test.skip('Requires CMake')
cmake_version = tuple(int(part) for part in test.cmake_version.split('.'))
if cmake_version < (3, 28):
    test.skip('Requires CMake 3.28 or newer for CXX_MODULES file sets')
if not shutil.which('ninja'):
    test.skip('Requires Ninja for CMake C++ module scanning')
test.run(logfile=test.obj_dir + '/cmake.log',
         cmd=[
             'cd "' + test.obj_dir + '" && cmake -G Ninja ' + test.t_dir +
             '/t_flag_cflags_modules_msvc', '-DCMAKE_PREFIX_PATH=' + os.environ['VERILATOR_ROOT']
         ])
test.run(logfile=test.obj_dir + '/build.log',
         cmd=[
             'cd "' + test.obj_dir + '" && cmake --build', '.', '-j ' + str(test.max_procs)
         ])
test.run(logfile=test.obj_dir + '/run.log',
         cmd=['cd "' + test.obj_dir + '" && .\\t_flag_cflags_modules_msvc.exe'])
test.passes()
