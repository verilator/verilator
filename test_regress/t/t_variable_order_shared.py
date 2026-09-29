#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

import re

test.scenarios('vlt_all')
test.compile(verilator_flags2=[
    '--cc', '--stats', '--dumpi-V3VariableOrder 1', '--threads-max-mtasks 8', '-Wno-UNOPTTHREADS'
],
             threads=(2 if test.vltmt else 1))

if test.vltmt:
    dump = test.file_contents(test.glob_one(test.obj_dir + '/*_variableorder.txt'))
    task_workers = dict(re.findall(r'^Task (\d+) worker=(\d+)$', dump, re.MULTILINE))
    shared = re.findall(
        r'  Group \d+ workers=\{(\d+(?:,\d+)+)\} writers=\{([^}]+)\}\n'
        r'((?:    .*\n)+)', dump)
    merged_readers = False
    for workers, writers, fields in shared:
        accesses = re.findall(r' tasks=\{([^}]+)\}', fields)
        if any({task_workers[task]
                for task in tasks.split(',')} != set(workers.split(',')) for tasks in accesses):
            test.error('Shared group contains different accessing worker sets')
        if any(field_writers != writers
               for field_writers in re.findall(r' writers=\{([^}]*)\}', fields)):
            test.error('Shared group contains different writing task sets')
        merged_readers |= len(set(accesses)) > 1
    # Different readers on the same workers must not split an otherwise identical group.
    if not merged_readers:
        test.error('Fixture must coalesce shared written fields with different reader task sets')
    test.file_grep(test.stats, r'VariableOrder, MTask affinity groups\s+(\d+)', 7)
    test.file_grep(test.stats, r'VariableOrder, MTask aligned group starts\s+(\d+)', 7)
else:
    test.file_grep_not(test.stats, r'VariableOrder,')

test.passes()
