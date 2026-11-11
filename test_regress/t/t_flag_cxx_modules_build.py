#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
import glob
import vltest_bootstrap

test.scenarios('simulator')
test.clean_objs()
if not test.have_cxx_module_scan:
    test.skip('Requires a compiler with C++ module dependency scanning')
flags = [
    '--exe',
    test.t_dir + '/t_flag_cxx_modules_build_main.cpp',
    '--build',
    '--cxx-modules',
    '-CFLAGS',
    '-std=c++23',
    '-CFLAGS',
    "-DSTR=\\'x\\'",
    test.t_dir + '/t_flag_cxx_modules_build.cppm',
]
test.compile(make_main=False, verilator_flags2=flags)
test.file_grep(test.obj_dir + '/' + test.vm_prefix + '.mk', r'export VK_SCAN_CXXFLAGS')
artifacts = (glob.glob(test.obj_dir + '/gcm.cache/*.gcm')
             + glob.glob(test.obj_dir + '/*.pcm'))
if not artifacts:
    test.error('No C++ module artifacts were generated')
test.execute()
test.passes()
