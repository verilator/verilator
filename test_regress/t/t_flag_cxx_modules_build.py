#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
import os
import re
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
test.glob_some(test.obj_dir + '/gcm.cache/*.gcm')
test.execute()

if re.search(r'\(GCC\)', test.cxx_version):
    cmis = [test.obj_dir + '/gcm.cache/buildmod.gcm']
    generated = cmis + [
        test.obj_dir + '/t_flag_cxx_modules_build.deps.json',
        test.obj_dir + '/t_flag_cxx_modules_build_main.deps.json',
        test.obj_dir + '/' + test.vm_prefix + '__modules.mk',
    ]
    user_cmis = [
        test.obj_dir + '/gcm.cache/std.gcm',
        test.obj_dir + '/std.pcm',
    ]
    for cmi in cmis:
        if not os.path.exists(cmi):
            test.error('No generated CMI at ' + cmi)
    for cmi in user_cmis:
        os.makedirs(os.path.dirname(cmi), exist_ok=True)
        with open(cmi, 'w', encoding='utf8'):
            pass
    test.run_capture('cd ' + test.obj_dir + ' && ' + os.environ['MAKE'] + ' -f ' + test.vm_prefix
                     + '.mk clean')
    for cmi in generated:
        if os.path.exists(cmi):
            test.error('make clean did not remove generated file ' + cmi)
    for cmi in user_cmis:
        if not os.path.exists(cmi):
            test.error('make clean removed user-precompiled module ' + cmi)

test.passes()
