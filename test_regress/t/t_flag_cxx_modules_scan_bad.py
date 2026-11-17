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
import sys
import vltest_bootstrap

test.scenarios('vlt')
test.clean_objs()
if 'clang' in test.cxx_version.lower() or 'microsoft' in test.cxx_version.lower():
    test.skip('Requires GCC for C++ module dependency scanning')
if not test.have_cxx_module_scan:
    test.skip('Requires a compiler with P1689 C++ module dependency scanning')


def run_scan(sources, logfile):
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
    for source in sources:
        cmd += ['--source', source]
    test.run(logfile=logfile, cmd=cmd, fails=True)


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

test.passes()
