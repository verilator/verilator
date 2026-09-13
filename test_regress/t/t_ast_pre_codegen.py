#!/usr/bin/env python3
# DESCRIPTION: Verilator: JSON output after optional sampled lowering
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Verilator Authors
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import json
import os
import vltest_bootstrap

test.scenarios('vlt')

for sampled in [False, True]:
    out_dir = test.obj_dir + ('/sampled' if sampled else '/plain')
    os.makedirs(out_dir, exist_ok=True)
    filename = out_dir + '/result.json'
    flags = ['-DWITH_SAMPLED'] if sampled else []
    test.compile(
        verilator_flags2=['--Mdir', out_dir, '--ast-pre-codegen', filename,
                          '--dump-tree-json', '--no-json-edit-nums'] + flags,
        verilator_make_gmake=False,
        make_top_shell=False,
        make_main=False)

    with open(filename, 'r', encoding='utf8') as fh:
        tree = json.load(fh)
    with open(filename + '.meta.json', 'r', encoding='utf8') as fh:
        json.load(fh)

    nodes = []

    def visit(node):
        if isinstance(node, dict):
            if 'type' in node:
                nodes.append(node)
            for value in node.values():
                visit(value)
        elif isinstance(node, list):
            for value in node:
                visit(value)

    visit(tree)
    if any(node['type'] == 'SAMPLED' for node in nodes):
        test.error('Sampled expressions were not lowered')
    sampled_vars = [node for node in nodes if node['type'] == 'VAR' and node.get('sampled')]
    if bool(sampled_vars) != sampled:
        test.error('Unexpected sampled variables')
    if not any(node['type'] == 'ACTIVE' for node in nodes):
        test.error('Expected active blocks before scheduling')
    for node in sampled_vars:
        if not node.get('valuep'):
            test.error('Sampled initialization was consumed by scheduling')
    files = os.listdir(out_dir)
    if any(name.endswith(('.cpp', '.h', '.mk')) for name in files):
        test.error('Unexpected generated C++ or build files')
    if any('sched' in name.lower() for name in files):
        test.error('Unexpected scheduling dump')

test.passes()
