#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
import re
import vltest_bootstrap

test.scenarios('simulator')
test.clean_objs()
if not test.have_cxx_module_scan:
    test.skip('Requires a compiler with P1689 C++ module dependency scanning')
flags = [
    '--exe',
    '--cxx-modules',
    test.t_dir + '/t_flag_cxx_modules_chain_main.cpp',
    '-CFLAGS',
    '-std=c++23',
    test.t_dir + '/t_flag_cxx_modules_chain_m1.cppm',
    test.t_dir + '/t_flag_cxx_modules_chain_m2.cppm',
]
test.compile(make_main=False, verilator_flags2=flags, make_flags=['VM_PARALLEL_BUILDS=1'])
if re.search(r'\(GCC\)', test.cxx_version):
    test.glob_some(test.obj_dir + '/gcm.cache/*.gcm')
else:
    test.glob_some(test.obj_dir + '/*.pcm')
test.execute()
test.passes()
