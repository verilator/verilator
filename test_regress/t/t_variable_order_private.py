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
test.compile(
    verilator_flags2=['--cc', '--stats', '--dumpi-V3VariableOrder 1', '-Wno-UNOPTTHREADS'],
    threads=(2 if test.vltmt else 1))

if test.vltmt:
    dump = test.file_contents(test.glob_one(test.obj_dir + '/*_variableorder.txt'))
    task_workers = dict(re.findall(r'^Task (\d+) worker=(\d+)$', dump, re.MULTILINE))
    private = re.findall(r'  Group \d+ workers=\{(\d+)\} writers=\{\}\n((?:    .*\n)+)', dump)
    # Updating scheduler-dependent goldens must not merge different workers' private state.
    if len({worker for worker, _ in private}) < 2:
        test.error('Fixture must retain private groups on two different workers')
    for worker, fields in private:
        accesses = re.findall(r' tasks=\{([^}]+)\}', fields)
        if any(task_workers[task] != worker for tasks in accesses for task in tasks.split(',')):
            test.error('Private group contains accesses by another worker')
        writers = re.findall(r' writers=\{([^}]+)\}', fields)
        if len(set(writers)) < 2:
            test.error('Each private worker must coalesce distinct writer sets')
    output_workers = [
        worker for worker, fields in private
        if re.search(r'^    o[ab] tasks=', fields, re.MULTILINE)
    ]
    if len(set(output_workers)) != 2:
        test.error('Independent outputs must occupy different private groups')
    test.file_grep(test.stats, r'VariableOrder, MTask affinity groups\s+(\d+)', 3)
    test.file_grep(test.stats, r'VariableOrder, MTask aligned group starts\s+(\d+)', 3)
else:
    test.file_grep_not(test.stats, r'VariableOrder,')

test.passes()
