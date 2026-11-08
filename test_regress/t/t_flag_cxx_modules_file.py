#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = test.t_dir + '/t_flag_cxx_modules_opt.v'
test.clean_objs()
gcc_dir = test.obj_dir + '/gcc'
clang_dir = test.obj_dir + '/clang'
common = [
    '--cc',
    '--exe',
    '--cxx-modules',
    test.t_dir + '/t_flag_cxx_modules_opt.cppm',
]
test.compile(make_main=False,
             verilator_make_gmake=False,
             verilator_make_cmake=False,
             verilator_flags2=['--Mdir', gcc_dir] + common + [
                 '--cxx-module-backend',
                 'gcc',
                 '--cxx-module-file',
                 'foo=/tmp/foo.gcm',
                 '--cxx-module-std',
                 '/tmp/std.pcm',
             ])
test.file_grep(gcc_dir + '/' + test.vm_prefix + '.mk', r'VM_USER_BACKEND = gcc')
test.file_grep(gcc_dir + '/' + test.vm_prefix + '.mk', r'-fmodule-file=foo=/tmp/foo\.gcm')
test.file_grep(gcc_dir + '/' + test.vm_prefix + '.mk', r'-fmodule-file=std=/tmp/std\.pcm')
test.compile(make_main=False,
             verilator_make_gmake=False,
             verilator_make_cmake=False,
             verilator_flags2=['--Mdir', clang_dir] + common + [
                 '--cxx-module-backend',
                 'clang',
             ])
test.file_grep(clang_dir + '/' + test.vm_prefix + '.mk', r'VM_USER_BACKEND = clang')
test.passes()
