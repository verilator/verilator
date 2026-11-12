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
test.top_filename = test.t_dir + '/t_flag_cxx_modules.v'
if not test.have_cxx_module_scan:
    test.skip('Requires a compiler with P1689 C++ module dependency scanning')
flags = [
    '--exe',
    '--cxx-modules',
    '--build',
    test.t_dir + '/t_flag_cxx_modules_chain_main.cpp',
    '-CFLAGS',
    '-std=c++23',
    '-CFLAGS',
    "-DSTR=\\'x\\'",
    test.t_dir + '/t_flag_cxx_modules_chain_m1.cppm',
    test.t_dir + '/t_flag_cxx_modules_chain_m2.cppm',
    test.t_dir + '/t_flag_cxx_modules_build.ixx',
]
test.compile(make_main=False, verilator_flags2=flags, make_flags=['VM_PARALLEL_BUILDS=1'])
test.file_grep(test.obj_dir + '/' + test.vm_prefix + '.mk', r'--backend')
test.file_grep(test.obj_dir + '/' + test.vm_prefix + '.mk', r'--cxx ')
test.file_grep(test.obj_dir + '/' + test.vm_prefix + '.mk', r'--cxxflags')
test.file_grep(test.obj_dir + '/' + test.vm_prefix + '.mk', r'--cppflags')
test.file_grep(test.obj_dir + '/' + test.vm_prefix + '.mk', r'--opt-fast')
test.file_grep(test.obj_dir + '/' + test.vm_prefix + '.mk', r'--objdir')
artifacts = (glob.glob(test.obj_dir + '/gcm.cache/*.gcm')
             + glob.glob(test.obj_dir + '/*.pcm'))
if not artifacts:
    test.error('No C++ module artifacts were generated')
if 'clang' in test.cxx_version.lower():
    artifact = test.obj_dir + '/t_flag_cxx_modules_chain_m1.pcm'
else:
    artifact = test.obj_dir + '/gcm.cache/m1.gcm'
module_obj = test.obj_dir + '/t_flag_cxx_modules_chain_m1.o'
if not os.path.exists(artifact):
    test.error('Missing C++ module artifact: ' + artifact)
if not os.path.exists(module_obj):
    test.error('Missing C++ module object: ' + module_obj)
os.remove(artifact)
test.run_capture('cd ' + test.obj_dir + ' && ' + os.environ['MAKE'] + ' -f ' + test.vm_prefix +
                 '.mk VM_PARALLEL_BUILDS=1')
if not os.path.exists(artifact):
    test.error('C++ module artifact was not rebuilt after deletion: ' + artifact)
test.execute()
test.passes()
