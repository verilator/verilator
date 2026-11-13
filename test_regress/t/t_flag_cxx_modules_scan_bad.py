#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import os
import shlex
import shutil
import sys
import vltest_bootstrap

test.scenarios('vlt')
test.clean_objs()
if 'clang' in test.cxx_version.lower() or 'microsoft' in test.cxx_version.lower():
    test.skip('Requires GCC for C++ module dependency scanning')
if not test.have_cxx_module_scan:
    test.skip('Requires a compiler with P1689 C++ module dependency scanning')


def run_scan(sources, logfile, extra=(), fails=True):
    cmd = [
        sys.executable,
        test.root + '/bin/verilator_module_deps',
        '--backend',
        'gcc',
        '--cxx',
        shlex.quote(os.environ.get('CXX', 'c++')),
        '--cxxflags=-std=c++23',
        '--cppflags=',
        '--opt-fast=-O0',
        '--objdir',
        test.obj_dir,
        '--output',
        test.obj_dir + '/scan.mk',
    ]
    cmd += list(extra)
    for source in sources:
        cmd += ['--source', source]
    test.run(logfile=logfile, cmd=cmd, fails=fails)


dup_a = test.obj_dir + '/dup_a.cppm'
dup_b = test.obj_dir + '/dup_b.cppm'
test.write_wholefile(dup_a, 'export module dup;\n')
test.write_wholefile(dup_b, 'export module dup;\n')
run_scan([dup_a, dup_b], test.obj_dir + '/dup.log')
test.file_grep(test.obj_dir + '/dup.log', r'Duplicate C\+\+ module provider')

missing = test.obj_dir + '/missing.cppm'
test.write_wholefile(missing, 'export module a;\nimport missing_module;\n')
run_scan([missing], test.obj_dir + '/missing.log')
test.file_grep(test.obj_dir + '/missing.log', r'has no provider')

std_missing = test.obj_dir + '/std_missing.cppm'
test.write_wholefile(std_missing, 'export module usestd;\nimport std;\n')
run_scan([std_missing], test.obj_dir + '/std.log')
test.file_grep(test.obj_dir + '/std.log', r"gcc backend cannot find")
test.file_grep(test.obj_dir + '/std.log', r'gcm.cache/std.gcm')
test.file_grep(test.obj_dir + '/std.log', r'Precompile')

clang = shutil.which('clang++')
if clang is not None and shutil.which('clang-scan-deps') is not None:
    clang_std = test.obj_dir + '/clang_std.cppm'
    test.write_wholefile(clang_std, 'export module usestd;\nimport std;\n')

    def run_clang_scan(logfile, cxxflags):
        test.run(
            logfile=logfile,
            cmd=[
                sys.executable,
                test.root + '/bin/verilator_module_deps',
                '--backend',
                'clang',
                '--cxx',
                shlex.quote(clang),
                '--cxxflags=' + cxxflags,
                '--cppflags=',
                '--opt-fast=-O0',
                '--objdir',
                test.obj_dir,
                '--output',
                test.obj_dir + '/scan_clang.mk',
                '--source',
                clang_std,
            ],
            fails=True)

    run_clang_scan(test.obj_dir + '/clang_std.log', '-std=c++23')
    test.file_grep(test.obj_dir + '/clang_std.log', r'clang backend has no std PCM')
    run_clang_scan(test.obj_dir + '/clang_std_missing.log',
                   '"-std=c++23 -fmodule-file=std=nope.pcm"')
    test.file_grep(test.obj_dir + '/clang_std_missing.log', r'does not exist')

test.run(logfile=test.obj_dir + '/no_action.log',
         cmd=[sys.executable, test.root + '/bin/verilator_module_deps', '--backend', 'gcc', '--cxx',
              shlex.quote(os.environ.get('CXX', 'c++'))],
         fails=True)
test.file_grep(test.obj_dir + '/no_action.log', r'required: --output')

test.passes()
