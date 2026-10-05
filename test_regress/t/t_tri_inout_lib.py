#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')
test.clean_objs()

for protect in (False, True):
    for split in (False, True):
        lib_dir = test.obj_dir + '/lib_' + str(int(protect)) + str(int(split))
        test.mkdir_ok(lib_dir)
        test.run(logfile=lib_dir + '/vlt_compile.log',
                 cmd=[
                     'perl', os.environ['VERILATOR_ROOT'] + '/bin/verilator', '--cc', '--build',
                     '--top-module', 'secret', '--Mdir', lib_dir,
                     '--protect-lib' if protect else '--lib-create', 'secret',
                     '--pins-inout-enables' if split else '', '-DLIB_CREATE', '--Wno-LITENDIAN',
                     '--dump-tree', '--dump-tree-json', test.top_filename
                 ],
                 verilator_run=True)
        test.file_grep(lib_dir + '/secret.sv',
                       r'input logic.*pad' if split else r'inout logic.*pad')
        if split:
            test.file_grep(lib_dir + '/secret.sv',
                           r'(?s)module secret \([^;]*output logic[^;]*pad__out')
            test.file_grep(lib_dir + '/secret.sv',
                           r'(?s)module secret \([^;]*output logic[^;]*pad__en')
        else:
            test.file_grep_not(lib_dir + '/secret.sv',
                               r'(?s)module secret \([^;]*output logic[^;]*pad__')
        # The DPI call feeds back the resolved bus; this small design may not fill both threads.
        test.compile(verilator_flags2=[
            lib_dir + '/secret.sv', '--Wno-LITENDIAN', '--Wno-UNOPTFLAT', '--Wno-UNOPTTHREADS',
            '-DLIB_SPLIT' if split else '', '-LDFLAGS',
            "'" + os.path.abspath(lib_dir) + "/libsecret.a'"
        ],
                     threads=(2 if test.vltmt else 1))
        test.execute()

test.passes()
