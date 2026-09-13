#!/usr/bin/env python3
# DESCRIPTION: Verilator: Preserved SVA property result signals
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Verilator Authors
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import json
import vltest_bootstrap

test.scenarios('vlt')

test.compile(verilator_flags2=['--dump-tree-json', '--sva-preserve', '--no-json-edit-nums'],
             verilator_make_gmake=False,
             make_top_shell=False,
             make_main=False)

dead_filenames = test.glob_some(test.obj_dir + "/*deadAllScoped.tree.json")
if not dead_filenames:
    test.error("No deadAllScoped JSON tree dumps found")

expected_names = {
    '__Vsva_assert_named_assert__0',
    '__Vsva_assume_named_assume__0',
    '__Vsva_cover_named_cover__0',
    '__Vsva_assert_message_assert__0',
    '__Vsva_assert_multi_assert__0',
}

for filename in dead_filenames:
    with open(filename, 'r', encoding='utf8') as fh:
        tree = json.load(fh)

    sva_vars = {}

    def visit(node):
        if isinstance(node, dict):
            orig_name = node.get('origName', '')
            if node.get('type') == 'VAR' and orig_name.startswith('__Vsva_'):
                sva_vars[orig_name] = node
            for value in node.values():
                visit(value)
        elif isinstance(node, list):
            for value in node:
                visit(value)

    visit(tree)
    if set(sva_vars) != expected_names:
        test.error("Unexpected preserved SVA signals in " + filename + ": " +
                   repr(sorted(sva_vars)))
    for name, node in sva_vars.items():
        if not node.get('isSigPublic'):
            test.error(name + " is not public in " + filename)
        if node.get('dtypeName') != 'bit':
            test.error(name + " is not one bit in " + filename)

    expected_templates = {
        '__Vsva_assert_named_assert__0': ["'assert' failed."],
        '__Vsva_assume_named_assume__0': ["'assert' failed."],
        '__Vsva_assert_message_assert__0': ["grant missing: request=%0b grant=%0b"],
        '__Vsva_assert_multi_assert__0': ["reset active: %0b", "grant missing again: %0b"],
    }
    for name, templates in expected_templates.items():
        tag = sva_vars.get(name, {}).get('tag', '')
        for template in templates:
            if template not in tag:
                test.error(name + " missing diagnostic template: " + template)
    if sva_vars.get('__Vsva_cover_named_cover__0', {}).get('tag'):
        test.error("Cover signal unexpectedly has a failure diagnostic")

    serialized = json.dumps(tree)
    if 'assertCtlGet' in serialized or 'assertOn()' in serialized:
        test.error("Runtime assertion control remains in " + filename)

test.passes()
