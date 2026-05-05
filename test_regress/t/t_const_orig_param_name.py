#!/usr/bin/env python3
# DESCRIPTION: Verilator: AstConst originating parameter name
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

from pathlib import Path
import re

import vltest_bootstrap

test.scenarios('vlt')

test.lint(v_flags=["--dump-tree"])

tree_filenames = test.glob_some(test.obj_dir + "/*.tree")
tree_text = "\n".join(Path(filename).read_text(encoding="utf8") for filename in tree_filenames)
orig_param_names = sorted(set(re.findall(r"\bCONST\b.*\borigParamName=([A-Za-z_][A-Za-z0-9_$]*)",
                                         tree_text)))

out_filename = test.obj_dir + "/" + test.name + ".out"
with open(out_filename, "w", encoding="utf8") as fh:
    for name in orig_param_names:
        fh.write(f"origParamName: {name}\n")

test.files_identical(out_filename, test.golden_filename)
test.passes()
