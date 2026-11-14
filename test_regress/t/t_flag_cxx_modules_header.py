#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import glob
import json
import os
import vltest_bootstrap

test.scenarios('vlt')

test.clean_objs()
test.top_filename = test.t_dir + '/t_flag_cxx_modules.v'
if 'clang' in test.cxx_version.lower() or 'microsoft' in test.cxx_version.lower():
    test.skip('Requires GCC for C++ header units')
if not test.have_cxx_module_scan:
    test.skip('Requires a compiler with P1689 C++ module dependency scanning')
flags = [
    '--exe',
    '--cxx-modules',
    test.t_dir + '/t_flag_cxx_modules_header.cpp',
    '-CFLAGS "-std=c++23 -isystem ' + test.t_dir + '/t_flag_cxx_modules_header_isystem"',
]
test.compile(make_main=False, verilator_flags2=flags, make_flags=['VM_PARALLEL_BUILDS=1'])
cmis = glob.glob(test.obj_dir + '/gcm.cache/**/t_flag_cxx_modules_header.h.gcm', recursive=True)
if not cmis:
    test.error('No C++ header unit CMI generated')
sidecars = glob.glob(test.obj_dir + '/*.cmi')
if len(sidecars) != 2:
    test.error('Expected two C++ header unit CMI sidecar files, found ' + str(len(sidecars)))
for sidecar in sidecars:
    with open(sidecar, encoding='utf8') as fh:
        cmi = json.load(fh)['cmi']
    if not os.path.exists(os.path.join(test.obj_dir, cmi)):
        test.error('C++ header unit CMI sidecar refers to missing file: ' + cmi)
# The make rule must rebuild the CMI when the imported header changes.
before = os.stat(cmis[0]).st_mtime_ns
os.utime(test.t_dir + '/t_flag_cxx_modules_header.h', None)
test.run_capture('cd ' + test.obj_dir + ' && ' + os.environ['MAKE'] + ' -f ' + test.vm_prefix +
                 '.mk VM_PARALLEL_BUILDS=1 OPT_FAST=-O0 OPT_GLOBAL=-O0')
if os.stat(cmis[0]).st_mtime_ns == before:
    test.error('C++ header unit CMI was not rebuilt after the header changed')
test.execute()
test.passes()
