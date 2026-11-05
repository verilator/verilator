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
import re
import vltest_bootstrap

test.scenarios('simulator')
test.clean_objs()
cxx = os.environ.get('CXX', 'c++')
cxx_version = test.cxx_version
gcc_match = re.search(r'\(GCC\) (\d+)', cxx_version)
is_clang = re.search(r'clang', cxx_version)
flags = [
    '--exe',
    test.t_dir + '/t_flag_cflags_modules_main.cpp',
]
make_flags = ['VM_PARALLEL_BUILDS=1']
if gcc_match:
    if int(gcc_match.group(1)) < 16:
        test.skip('Requires GCC 16 or newer for --compile-std-module')
    with open(test.obj_dir + '/empty.cpp', 'w', encoding='utf8'):
        pass
    test.run_capture('cd ' + test.obj_dir + ' && ' + cxx + ' -std=c++23 -fmodules'
                     ' --compile-std-module -c empty.cpp -o empty.o',
                     check=False)
    if not os.path.exists(test.obj_dir + '/gcm.cache/std.gcm'):
        test.skip('GCC --compile-std-module is not available')
    flags += ['-CFLAGS -std=c++23', '-CFLAGS -fmodules']
elif is_clang:
    std_cppm = None
    for candidate in ('/usr/share/libc++/v1/std.cppm',
                      *sorted(glob.glob('/usr/lib/llvm-*/share/libc++/v1/std.cppm'))):
        if os.path.exists(candidate):
            std_cppm = candidate
            break
    if std_cppm is None:
        test.skip('Requires libc++ std.cppm')
    test.run_capture('cd ' + test.obj_dir + ' && ' + cxx + ' -std=c++23 -stdlib=libc++'
                     ' --precompile ' + std_cppm + ' -o std.pcm',
                     check=False)
    if not os.path.exists(test.obj_dir + '/std.pcm'):
        test.skip('Requires Clang with libc++')
    flags += [
        '-CFLAGS -std=c++23',
        '-CFLAGS -stdlib=libc++',
        '-CFLAGS -fmodule-file=std=std.pcm',
        '-LDFLAGS -stdlib=libc++',
    ]
else:
    test.skip('Requires GCC or Clang')
test.compile(make_main=False, verilator_flags2=flags, make_flags=make_flags)
test.glob_some(test.obj_dir + '/*__pch.h.fast.gch')
if gcc_match:
    test.file_grep(test.obj_dir + '/vlt_gcc.log', r'-fno-modules')
    test.file_grep(test.obj_dir + '/vlt_gcc.log', r'-fmodules')
else:
    test.file_grep(test.obj_dir + '/vlt_gcc.log', r'-fmodule-file=std=std\.pcm')

os.utime(test.t_dir + '/t_flag_cflags_modules_main.cpp', None)
test.run_capture('cd ' + test.obj_dir + ' && ' + os.environ['MAKE'] + ' -f ' + test.vm_prefix +
                 '.mk VM_PARALLEL_BUILDS=1 OPT_FAST=-O0 OPT_GLOBAL=-O0')
test.execute()
test.passes()
