#!/usr/bin/env python3
# DESCRIPTION: Verilator: generic coverage declaration dump test
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

from pathlib import Path

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_cover_fsm_policy_accept_multi.v"

# Dump generic COVEROTHERDECL nodes so AstCoverOtherDecl::dump() also sees
# coverage declarations with no FSM metadata, exercising the empty-field side
# of the fv/ff/ft/fg formatting.
test.lint(v_flags=["--coverage-line", "--dump-tree"])

tree_files = [Path(filename) for filename in test.glob_some(test.obj_dir + "/*.tree")]
tree_texts = [filename.read_text(encoding="utf8") for filename in tree_files]

generic_lines = []
for text in tree_texts:
    generic_lines.extend(line for line in text.splitlines()
                         if "COVEROTHERDECL" in line and " page=v_line/" in line)

assert generic_lines
assert any(" fv=" not in line and " ff=" not in line and " ft=" not in line and " fg=" not in line
           for line in generic_lines)

test.passes()
