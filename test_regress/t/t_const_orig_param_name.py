#!/usr/bin/env python3
# DESCRIPTION: Verilator: AstConst originating parameter name
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

from pathlib import Path

import vltest_bootstrap

test.scenarios('vlt')

test.lint(v_flags=["--dump-tree"])

tree_filenames = test.glob_some(test.obj_dir + "/*.tree")
tree_files = [Path(filename) for filename in tree_filenames]

test.file_grep_any(tree_filenames, r"CONST .*origParamName=S_IDLE")
test.file_grep_any(tree_filenames, r"CONST .*origParamName=S_EXEC")

clean_tree = Path(test.glob_one(test.obj_dir + "/V*_clean.tree"))
clean_text = clean_tree.read_text(encoding="utf8")

assert "origParamName=S_FETCH" not in clean_text

test.passes()
