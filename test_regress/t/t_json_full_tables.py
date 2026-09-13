#!/usr/bin/env python3
# DESCRIPTION: Verilator: Complete JSON array initializer tables
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Verilator Authors
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import json
import re
import vltest_bootstrap

test.scenarios('vlt')

for mode, flags, count in [
    ('default', [], 6),
    ('full', ['--json-full-tables'], 10),
    ('off', ['--json-full-tables', '--no-json-full-tables'], 6),
]:
    filename = test.obj_dir + '/' + mode + '.tree.json'
    test.compile(
        verilator_flags2=['--json-only', '--json-only-output', filename, '--no-json-edit-nums'] +
        flags,
        verilator_make_gmake=False,
        make_top_shell=False,
        make_main=False)

    with open(filename, 'r', encoding='utf8') as fh:
        tree = json.load(fh)

    tables = []

    def visit(node):
        if isinstance(node, dict):
            if node.get('type') == 'INITARRAY':
                tables.append(node)
            for value in node.values():
                visit(value)
        elif isinstance(node, list):
            for value in node:
                visit(value)

    visit(tree)
    if len(tables) != 1:
        test.error('Expected one initializer table in ' + mode)
    for table in tables:
        entries = re.findall(r'\[(\d+)\]=([^ ]+)', table['initList'])
        if [int(index) for index, _ in entries] != list(range(count)):
            test.error('Incorrect initializer indices in ' + mode)
        if ('...' in table['initList']) != (count < 10):
            test.error('Incorrect initializer truncation in ' + mode)
        items = table['initsp']
        if len(items) != 10:
            test.error('Missing initializer values in ' + mode)
        if [addr for _, addr in entries] != [item['addr'] for item in items[:count]]:
            test.error('Incorrect initializer references in ' + mode)

test.passes()
