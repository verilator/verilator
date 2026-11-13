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
import sys
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


def run_make(extra=''):
    return test.run_capture('cd ' + test.obj_dir + ' && ' + os.environ['MAKE'] + ' -f ' +
                            test.vm_prefix + '.mk VM_PARALLEL_BUILDS=1' + extra + ' 2>&1')


stamp = test.obj_dir + '/' + test.vm_prefix + '__modules.stamp'
modules_json = test.obj_dir + '/' + test.vm_prefix + '__modules.json'
modules_dot = test.obj_dir + '/' + test.vm_prefix + '__modules.dot'
module_obj = test.obj_dir + '/t_flag_cxx_modules_chain_m1.o'
if 'clang' in test.cxx_version.lower():
    artifact = test.obj_dir + '/t_flag_cxx_modules_chain_m1.pcm'
else:
    artifact = test.obj_dir + '/gcm.cache/m1.gcm'
test.file_grep(modules_json, r'"m1"')
test.file_grep(modules_json, r'"m2"')
test.file_grep(modules_json, r'"buildmod"')
test.file_grep(modules_dot, r'm2 -> m1')

direct_dir = test.obj_dir + '/direct'
test.run(
    logfile=test.obj_dir + '/direct.log',
    cmd=[
        sys.executable,
        test.root + '/bin/verilator_module_deps',
        '--backend',
        'clang' if 'clang' in test.cxx_version.lower() else 'gcc',
        '--cxx',
        os.environ.get('CXX', 'c++'),
        '--cxxflags=-std=c++23',
        '--cppflags=',
        '--opt-fast=-O0',
        '--objdir',
        direct_dir,
        '--json',
        direct_dir + '/graph.json',
        '--dot',
        direct_dir + '/graph.dot',
        '--stamp',
        direct_dir + '/graph.stamp',
        '--output',
        direct_dir + '/graph.mk',
        '--source',
        test.t_dir + '/t_flag_cxx_modules_chain_m1.cppm',
    ])
test.file_grep(direct_dir + '/graph.json', r'"m1"')
test.file_grep(direct_dir + '/graph.dot', r'digraph modules')
if not os.path.exists(direct_dir + '/graph.stamp'):
    test.error('Missing C++ module graph stamp')

run_make()
if not os.path.exists(stamp):
    test.error('Missing C++ module build stamp: ' + stamp)
if not os.path.exists(artifact):
    test.error('Missing C++ module artifact: ' + artifact)
if not os.path.exists(module_obj):
    test.error('Missing C++ module object: ' + module_obj)
stamp_time = os.stat(stamp).st_mtime_ns
obj_time = os.stat(module_obj).st_mtime_ns
artifact_time = os.stat(artifact).st_mtime_ns

run_make()
if os.stat(stamp).st_mtime_ns != stamp_time:
    test.error('C++ module build stamp changed without input changes')
if os.stat(module_obj).st_mtime_ns != obj_time or os.stat(artifact).st_mtime_ns != artifact_time:
    test.error('C++ module outputs were rebuilt without input changes')

extra = ' OPT_FAST=-O1'
run_make(extra)
if os.stat(stamp).st_mtime_ns == stamp_time:
    test.error('C++ module build stamp did not change after OPT_FAST changed')
if os.stat(module_obj).st_mtime_ns == obj_time or os.stat(artifact).st_mtime_ns == artifact_time:
    test.error('C++ module outputs were not rebuilt after OPT_FAST changed')
stamp_time = os.stat(stamp).st_mtime_ns
obj_time = os.stat(module_obj).st_mtime_ns
artifact_time = os.stat(artifact).st_mtime_ns

run_make(extra)
if os.stat(stamp).st_mtime_ns != stamp_time:
    test.error('C++ module build stamp changed without input changes')
if os.stat(module_obj).st_mtime_ns != obj_time or os.stat(artifact).st_mtime_ns != artifact_time:
    test.error('C++ module outputs were rebuilt without input changes')

extra += ' CXXFLAGS=-DTEST_STAMP=1'
run_make(extra)
if os.stat(stamp).st_mtime_ns == stamp_time:
    test.error('C++ module build stamp did not change after CXXFLAGS changed')
if os.stat(module_obj).st_mtime_ns == obj_time or os.stat(artifact).st_mtime_ns == artifact_time:
    test.error('C++ module outputs were not rebuilt after CXXFLAGS changed')
stamp_time = os.stat(stamp).st_mtime_ns

std_gcm = test.obj_dir + '/gcm.cache/std.gcm'
test.write_wholefile(std_gcm, 'std\n')
run_make(extra)
if os.stat(stamp).st_mtime_ns == stamp_time:
    test.error('C++ module build stamp did not change after the std module appeared')
stamp_time = os.stat(stamp).st_mtime_ns
std_stat = os.stat(std_gcm)
os.utime(std_gcm, ns=(std_stat.st_atime_ns, std_stat.st_mtime_ns + 1000000000))
run_make(extra)
if os.stat(stamp).st_mtime_ns == stamp_time:
    test.error('C++ module build stamp did not change after the std module changed')
stamp_time = os.stat(stamp).st_mtime_ns

os.remove(stamp)
run_make(extra)
if not os.path.exists(stamp) or os.stat(stamp).st_mtime_ns == stamp_time:
    test.error('C++ module build stamp was not rebuilt after deletion')
test.file_grep(test.obj_dir + '/' + test.vm_prefix + '.mk', r'--backend')
test.file_grep(test.obj_dir + '/' + test.vm_prefix + '.mk', r'--cxx ')
test.file_grep(test.obj_dir + '/' + test.vm_prefix + '.mk', r'--cxxflags')
test.file_grep(test.obj_dir + '/' + test.vm_prefix + '.mk', r'--cppflags')
test.file_grep(test.obj_dir + '/' + test.vm_prefix + '.mk', r'--opt-fast')
test.file_grep(test.obj_dir + '/' + test.vm_prefix + '.mk', r'--objdir')
artifacts = (glob.glob(test.obj_dir + '/gcm.cache/*.gcm') + glob.glob(test.obj_dir + '/*.pcm'))
if not artifacts:
    test.error('No C++ module artifacts were generated')
os.remove(artifact)
make_out = run_make(extra)
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
run_make(extra)
if os.stat(deps_1).st_mtime_ns != deps_1_time or os.stat(deps_2).st_mtime_ns != deps_2_time:
    test.error('C++ module scan was not reused from cache')

os.utime(test.t_dir + '/t_flag_cxx_modules_chain_m2.cppm', None)
run_make(extra)
if os.stat(deps_2).st_mtime_ns == deps_2_time:
    test.error('C++ module scan cache was not invalidated by a source change')
if os.stat(deps_1).st_mtime_ns != deps_1_time:
    test.error('C++ module scan cache was not reused for an unchanged source')

test.execute()
test.passes()
