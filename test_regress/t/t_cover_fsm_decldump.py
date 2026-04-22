#!/usr/bin/env python3
# DESCRIPTION: Verilator: FSM lowered coverage declaration dump test
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

from pathlib import Path

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_cover_fsm_styles.v"

# Dump the lowered AST so AstCoverOtherDecl::dump() sees FSM metadata-bearing
# coverage declarations directly. This avoids JSON/schema coupling while still
# covering the dump-side formatting for fv/ff/ft/fg.
test.lint(v_flags=["--coverage-fsm", "--dump-tree"])

tree_files = [Path(filename) for filename in test.glob_some(test.obj_dir + "/*.tree")]
tree_texts = [filename.read_text(encoding="utf8") for filename in tree_files]

assert any("COVEROTHERDECL" in text and " fv=t.state" in text for text in tree_texts)
assert any(
    "COVEROTHERDECL" in text and " ff=ANY" in text and " ft=S0" in text and " fg=reset" in text
    for text in tree_texts)
assert any("COVEROTHERDECL" in text and " ff=default" in text and " ft=S0" in text
           and " fg=default" in text for text in tree_texts)

test.passes()
