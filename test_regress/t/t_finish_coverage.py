#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import re

import vltest_bootstrap

test.scenarios('simulator')

coverage_filename = test.obj_dir + '/coverage.dat'
test.compile(verilator_flags2=['--binary', '--coverage-line', '--coverage-expr'])
test.execute(all_run_flags=['+verilator+coverage+file+' + coverage_filename])

source = test.file_contents('t/t_finish_coverage.v')
targets = []
expr_targets = []
line_targets = []
for lineno, line in enumerate(source.splitlines(), 1):
    match = re.search(r'COVER_TARGET:(\w+)', line)
    if match:
        targets.append((lineno, match.group(1)))
    if 'COVER_EXPR_TARGET' in line:
        expr_targets.append(lineno)
    line_match = re.search(r'COVER_LINE_(HIT|MISS)', line)
    if line_match:
        line_targets.append((lineno, line_match.group(1) == 'HIT'))

coverage = test.file_contents(coverage_filename)
for lineno, comment in targets:
    line_marker = f'\x01l\x02{lineno}\x01'
    comment_marker = f'\x01o\x02{comment}\x01'
    matches = [
        line for line in coverage.splitlines()
        if line.startswith('C ') and line_marker in line and comment_marker in line
    ]
    if len(matches) != 1:
        test.error(f'Expected one coverage point at line {lineno} ({comment}), got {len(matches)}')
        continue
    count_match = re.search(r"' (\d+)$", matches[0])
    if not count_match or int(count_match.group(1)) != 1:
        test.error(f'Coverage point at line {lineno} ({comment}) did not execute once')

for lineno in expr_targets:
    line_marker = f'\x01l\x02{lineno}\x01'
    type_marker = '\x01t\x02expr\x01'
    matches = [
        line for line in coverage.splitlines()
        if line.startswith('C ') and line_marker in line and type_marker in line
    ]
    counts = []
    for line in matches:
        count_match = re.search(r"' (\d+)$", line)
        if count_match:
            counts.append(int(count_match.group(1)))
    if not counts or sum(count > 0 for count in counts) != 1 or max(counts) != 1:
        test.error(f'Expression coverage at line {lineno} did not record one evaluated path')

covered_lines = set()
for line in coverage.splitlines():
    if not line.startswith('C ') or '\x01t\x02' not in line:
        continue
    count_match = re.search(r"' (\d+)$", line)
    range_match = re.search(r'\x01S\x02([^\x01]+)\x01', line)
    if not count_match or int(count_match.group(1)) == 0 or not range_match:
        continue
    for item in range_match.group(1).split(','):
        bounds = [int(value) for value in item.split('-', 1)]
        first = bounds[0]
        last = bounds[-1]
        covered_lines.update(range(first, last + 1))

for lineno, expected_hit in line_targets:
    if (lineno in covered_lines) != expected_hit:
        expectation = 'covered' if expected_hit else 'uncovered'
        test.error(f'Expected source line {lineno} to remain {expectation}')

test.passes()
