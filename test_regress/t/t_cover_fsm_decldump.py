#!/usr/bin/env python3
# DESCRIPTION: Verilator: FSM lowered coverage declaration dump test
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import json
from pathlib import Path

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_cover_fsm_styles.v"

# Dump the post-detect AST so we verify the lowered COVEROTHERDECL nodes carry
# the structured FSM metadata fields directly, not just the human-readable
# annotation strings emitted later by verilator_coverage.
test.lint(v_flags=["--coverage-fsm", "--dump-tree", "--dump-tree-json", "--no-json-edit-nums"])

tree_files = [Path(filename) for filename in test.glob_some(test.obj_dir + "/*.tree")]
json_files = [Path(filename) for filename in test.glob_some(test.obj_dir + "/*.tree.json")]


def walk_json(node):
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from walk_json(value)
    elif isinstance(node, list):
        for value in node:
            yield from walk_json(value)


tree_texts = [filename.read_text(encoding="utf8") for filename in tree_files]
assert any("COVEROTHERDECL" in text and " fv=t.state" in text for text in tree_texts)
assert any(
    "COVEROTHERDECL" in text and " ff=ANY" in text and " ft=S0" in text and " fg=reset" in text
    for text in tree_texts
)
assert any(
    "COVEROTHERDECL" in text and " ff=default" in text and " ft=S0" in text and " fg=default" in text
    for text in tree_texts
)

cover_decls = []
for filename in json_files:
    with filename.open('r', encoding="utf8") as fh:
        cover_decls.extend(
            node for node in walk_json(json.load(fh)) if node.get("type") == "COVEROTHERDECL"
        )

assert any(node.get("fsmVar") == "t.state" and node.get("fsmTo") == "S0" for node in cover_decls)
assert any(
    node.get("fsmVar") == "t.state"
    and node.get("fsmFrom") == "ANY"
    and node.get("fsmTo") == "S0"
    and node.get("fsmTag") == "reset"
    for node in cover_decls
)
assert any(
    node.get("fsmVar") == "t.state"
    and node.get("fsmFrom") == "default"
    and node.get("fsmTo") == "S0"
    and node.get("fsmTag") == "default"
    for node in cover_decls
)

test.passes()
