#!/usr/bin/env python3
# DESCRIPTION: Verilator: Expression coverage in sensitivity expressions
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
test.compile(verilator_flags2=['--binary', '--coverage-expr', '--timing'])
test.execute(all_run_flags=['+verilator+coverage+file+' + coverage_filename])

source = test.file_contents('t/t_cover_expr_sensitivity.v')
target_lineno = next(lineno for lineno, line in enumerate(source.splitlines(), 1)
                     if 'COVER_SENSITIVITY_EXPR' in line)
counts = []
for line in test.file_contents(coverage_filename).splitlines():
    if not line.startswith('C ') or '\x01t\x02expr\x01' not in line:
        continue
    if f'\x01l\x02{target_lineno}\x01' not in line:
        continue
    count_match = re.search(r"' (\d+)$", line)
    if count_match:
        counts.append(int(count_match.group(1)))

if not counts or sum(counts) != 1:
    test.error(f'Expected one sensitivity expression evaluation, got {sum(counts)}')

test.passes()
