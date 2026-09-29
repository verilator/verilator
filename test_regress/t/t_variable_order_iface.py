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
test.compile(
    verilator_flags2=['--cc', '--stats', '--dumpi-V3VariableOrder 1', '-Wno-UNOPTTHREADS'],
    threads=(2 if test.vltmt else 1))

if test.vltmt:
    dump = test.glob_one(test.obj_dir + '/*_variableorder.txt')
    # Keep the non-emitted companion first, so it would consume alignment without the fix.
    test.file_grep(
        dump, r'  Group \d+ workers=\{\d+\} writers=\{\}\n'
        r'    \S+__DOT__tx__Viftop tasks=\{[^}]+\} writers=\{\} aligned=0\n'
        r'    \S+__DOT__vif tasks=\{[^}]+\} writers=\{[^}]+\} aligned=1')
    test.file_grep(test.stats, r'VariableOrder, MTask aligned group starts\s+(\d+)', 4)
    root_type = test.file_grep(test.obj_dir + '/' + test.vm_prefix + '.h',
                               r'\b(\w+)\* const rootp;')[0]
    root_header = test.obj_dir + '/' + root_type + '.h'
    # Resolve current types from their uses; protected names may change between runs.
    iface_type = test.file_grep(root_header, r'alignas\(VL_CACHE_LINE_BYTES\) (\w+)\* \w+;')[0]
    aligned_var_re = r'^\s+alignas\(VL_CACHE_LINE_BYTES\) '
    test.file_grep_count(root_header, aligned_var_re, 3)
    test.file_grep_count(test.obj_dir + '/' + iface_type + '.h', aligned_var_re, 1)
else:
    test.file_grep_not(test.stats, r'VariableOrder,')

test.passes()
