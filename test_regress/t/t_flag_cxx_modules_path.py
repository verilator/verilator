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

test.scenarios('vlt')

test.clean_objs()
test.top_filename = test.t_dir + '/t_flag_cxx_modules.v'
if 'clang' in test.cxx_version.lower() or 'microsoft' in test.cxx_version.lower():
    test.skip('Requires GCC for C++ module builds')
if not test.have_cxx_module_scan:
    test.skip('Requires a compiler with P1689 C++ module dependency scanning')


def shell_quote(path):
    return "'" + path.replace("'", "'\\''") + "'"


# Module sources in paths that make and the shell must neither split nor expand
copies = [
    ('module sources/m1 \'quoted\'.cppm', 't_flag_cxx_modules_chain_m1.cppm'),
    ('module $dir/t_flag_cxx_modules_chain_m2.cppm', 't_flag_cxx_modules_chain_m2.cppm'),
    ('module #dir/t_flag_cxx_modules_build.ixx', 't_flag_cxx_modules_build.ixx'),
]
source_paths = []
for copy_path, source in copies:
    os.makedirs(test.obj_dir + '/' + os.path.dirname(copy_path), exist_ok=True)
    shutil.copy(test.t_dir + '/' + source, test.obj_dir + '/' + copy_path)
    source_paths.append(test.obj_dir + '/' + copy_path)

flags = [
    '--exe',
    '--cxx-modules',
    '--build',
    test.t_dir + '/t_flag_cxx_modules_chain_main.cpp',
    '-CFLAGS',
    '-std=c++23',
    '-CFLAGS',
    "-DSTR=\\'x\\'",
] + [shell_quote(path) for path in source_paths]
test.compile(make_main=False, verilator_flags2=flags, make_flags=['VM_PARALLEL_BUILDS=1'])

verilator_mk = test.obj_dir + '/' + test.vm_prefix + '.mk'
modules_mk = test.obj_dir + '/' + test.vm_prefix + '__modules.mk'
# Quoted shell arguments in the recipe
test.file_grep(verilator_mk, r"--source 'module sources/m1 ")
test.file_grep(verilator_mk, r"--source 'module \$\$dir/")
test.file_grep(verilator_mk, r"--source 'module #dir/")
# Escaped names in the prerequisites
test.file_grep(verilator_mk, r"__modules\.mk: .*module\\ sources/m1\\ 'quoted'\.cppm")
test.file_grep(modules_mk, r"module\\ sources/m1\\ 'quoted'\.cppm")
test.file_grep(modules_mk, r"module\\ \$\$dir/")
test.file_grep(modules_mk, r"module\\ \\#dir/")
# Object names with unsafe characters get sanitized, plus a hash of the path
test.file_grep(modules_mk, r'VM_USER_CLASSES \+= m1__quoted__[0-9a-f]{8}')
test.glob_some(test.obj_dir + '/m1__quoted__*.o')

test.execute()
test.passes()
