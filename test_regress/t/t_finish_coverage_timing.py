#!/usr/bin/env python3
# DESCRIPTION: Verilator: Finish-aware coverage timing boundaries
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import re

import vltest_bootstrap

test.scenarios('vlt', 'vltmt')

coverage_filename = test.obj_dir + '/coverage.dat'
test.compile(verilator_flags2=['--binary', '--coverage-line', '--timing'])
test.execute(all_run_flags=['+verilator+coverage+file+' + coverage_filename])

source = test.file_contents('t/t_finish_coverage_timing.v')
target_lines = {
    lineno
    for lineno, line in enumerate(source.splitlines(), 1) if 'COVER_TIMING_LINE' in line
}
coverage_expectations = {}
for lineno, line in enumerate(source.splitlines(), 1):
    match = re.search(r'COVER_TIMING_(HIT|MISS)', line)
    if match:
        coverage_expectations[lineno] = match.group(1) == 'HIT'

matching_points = 0
covered_lines = set()
coverage = test.file_contents(coverage_filename)
for line in coverage.splitlines():
    if not line.startswith('C ') or '\x01t\x02line\x01' not in line:
        continue
    range_match = re.search(r'\x01S\x02([^\x01]+)\x01', line)
    if not range_match:
        continue
    covered = set()
    for item in range_match.group(1).split(','):
        bounds = [int(value) for value in item.split('-', 1)]
        covered.update(range(bounds[0], bounds[-1] + 1))
    if covered & target_lines:
        matching_points += 1
    count_match = re.search(r"' (\d+)$", line)
    if count_match and int(count_match.group(1)) > 0:
        covered_lines.update(covered)

if matching_points != 1:
    test.error(f'Expected one unrelated timing coverage region, got {matching_points}')

for lineno, expected_hit in coverage_expectations.items():
    if (lineno in covered_lines) != expected_hit:
        expectation = 'covered' if expected_hit else 'uncovered'
        test.error(f'Expected source line {lineno} to remain {expectation}')

test.passes()
