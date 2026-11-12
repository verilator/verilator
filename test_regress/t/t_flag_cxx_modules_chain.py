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

test.scenarios('vlt')

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
artifacts = (glob.glob(test.obj_dir + '/gcm.cache/*.gcm') + glob.glob(test.obj_dir + '/*.pcm'))
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
make_out = test.run_capture('cd ' + test.obj_dir + ' && ' + os.environ['MAKE'] + ' -f ' +
                            test.vm_prefix + '.mk VM_PARALLEL_BUILDS=1 2>&1')
if 'Circular' in make_out:
    test.error('Circular dependency in C++ module make rules')
if not os.path.exists(artifact):
    test.error('C++ module artifact was not rebuilt after deletion: ' + artifact)

deps_1 = test.obj_dir + '/t_flag_cxx_modules_chain_m1.deps.json'
deps_2 = test.obj_dir + '/t_flag_cxx_modules_chain_m2.deps.json'
scan_cache = test.obj_dir + '/t_flag_cxx_modules_chain_m1.scan.json'
for path in (deps_1, deps_2, scan_cache):
    if not os.path.exists(path):
        test.error('Missing C++ module scan file: ' + path)
deps_1_time = os.stat(deps_1).st_mtime_ns
deps_2_time = os.stat(deps_2).st_mtime_ns
os.remove(test.obj_dir + '/' + test.vm_prefix + '__modules.mk')
test.run_capture('cd ' + test.obj_dir + ' && ' + os.environ['MAKE'] + ' -f ' + test.vm_prefix +
                 '.mk VM_PARALLEL_BUILDS=1 2>&1')
if os.stat(deps_1).st_mtime_ns != deps_1_time or os.stat(deps_2).st_mtime_ns != deps_2_time:
    test.error('C++ module scan was not reused from cache')

os.utime(test.t_dir + '/t_flag_cxx_modules_chain_m2.cppm', None)
test.run_capture('cd ' + test.obj_dir + ' && ' + os.environ['MAKE'] + ' -f ' + test.vm_prefix +
                 '.mk VM_PARALLEL_BUILDS=1 2>&1')
if os.stat(deps_2).st_mtime_ns == deps_2_time:
    test.error('C++ module scan cache was not invalidated by a source change')
if os.stat(deps_1).st_mtime_ns != deps_1_time:
    test.error('C++ module scan cache was not reused for an unchanged source')

test.execute()
test.passes()
