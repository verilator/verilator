#!/usr/bin/env python3
# DESCRIPTION: Verilator: Coverage state across finish-capable boundaries
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
test.compile(verilator_flags2=['--binary', '--coverage-line'])
test.execute(all_run_flags=['+verilator+coverage+file+' + coverage_filename])

source = test.file_contents('t/t_finish_coverage_state.v')
targets = []
for lineno, line in enumerate(source.splitlines(), 1):
    match = re.search(r'COVER_LINE_(HIT|MISS|OMIT)', line)
    if match:
        targets.append((lineno, match.group(1)))

tracked_lines = set()
covered_lines = set()
coverage = test.file_contents(coverage_filename)
for line in coverage.splitlines():
    if not line.startswith('C ') or '\x01t\x02' not in line:
        continue
    count_match = re.search(r"' (\d+)$", line)
    range_match = re.search(r'\x01S\x02([^\x01]+)\x01', line)
    if not count_match or not range_match:
        continue
    lines = set()
    for item in range_match.group(1).split(','):
        bounds = [int(value) for value in item.split('-', 1)]
        lines.update(range(bounds[0], bounds[-1] + 1))
    tracked_lines.update(lines)
    if int(count_match.group(1)) > 0:
        covered_lines.update(lines)

for lineno, expectation in targets:
    if expectation == 'HIT' and lineno not in covered_lines:
        test.error(f'Expected source line {lineno} to be covered')
    elif expectation == 'MISS' and lineno in covered_lines:
        test.error(f'Expected source line {lineno} to remain uncovered')
    elif expectation == 'OMIT' and lineno in tracked_lines:
        test.error(f'Expected source line {lineno} to have no coverage point')

test.passes()
