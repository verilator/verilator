#!/usr/bin/env python3
# DESCRIPTION: Verilator: FSM coverage infers non-enum state space
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

from pathlib import Path

import vltest_bootstrap

test.scenarios('vlt')

test.lint(v_flags=["--coverage-fsm", "--dump-tree"])

tree_files = [Path(filename) for filename in test.glob_some(test.obj_dir + "/*.tree")]
tree_texts = [filename.read_text(encoding="utf8") for filename in tree_files]

assert any("COVEROTHERDECL" in text and " fv=t.literal_state" in text and " ft=2'h0" in text
           for text in tree_texts)
assert any("COVEROTHERDECL" in text and " fv=t.literal_state" in text and " ft=2'h1" in text
           for text in tree_texts)
assert any("COVEROTHERDECL" in text and " fv=t.literal_state" in text and " ft=2'h2" in text
           for text in tree_texts)

assert any("COVEROTHERDECL" in text and " fv=t.param_state" in text and " ft=IDLE" in text
           for text in tree_texts)
assert any("COVEROTHERDECL" in text and " fv=t.param_state" in text and " ft=BUSY" in text
           for text in tree_texts)
assert any("COVEROTHERDECL" in text and " fv=t.param_state" in text and " ft=DONE" in text
           for text in tree_texts)

assert any("COVEROTHERDECL" in text and " fv=t.unbased_state" in text and " ft=1'h0" in text
           for text in tree_texts)
assert any("COVEROTHERDECL" in text and " fv=t.unbased_state" in text and " ft=1'h1" in text
           for text in tree_texts)

assert any("COVEROTHERDECL" in text and " fv=t.body_symbol_state" in text and " ft=BODY_ID" in text
           for text in tree_texts)
assert any("COVEROTHERDECL" in text and " fv=t.body_symbol_state" in text and " ft=BODY$ID" in text
           for text in tree_texts)

assert any("COVEROTHERDECL" in text and " fv=t.multiline_expr_state" in text and " ft=2'h0" in text
           for text in tree_texts)
assert any("COVEROTHERDECL" in text and " fv=t.multiline_expr_state" in text and " ft=2'h1" in text
           for text in tree_texts)

assert any("COVEROTHERDECL" in text and " fv=t.duplicate_expr_state" in text and " ft=IDLE" in text
           for text in tree_texts)
assert any("COVEROTHERDECL" in text and " fv=t.duplicate_expr_state" in text and " ft=BUSY" in text
           for text in tree_texts)

assert any(
    "COVEROTHERDECL" in text and " fv=t.duplicate_same_label_state" in text and " ft=IDLE" in text
    for text in tree_texts)
assert any(
    "COVEROTHERDECL" in text and " fv=t.duplicate_same_label_state" in text and " ft=BUSY" in text
    for text in tree_texts)

assert any(
    "COVEROTHERDECL" in text and " fv=t.duplicate_expr_first_state" in text and " ft=IDLE" in text
    for text in tree_texts)
assert any(
    "COVEROTHERDECL" in text and " fv=t.duplicate_expr_first_state" in text and " ft=BUSY" in text
    for text in tree_texts)

test.passes()
