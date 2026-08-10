#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import glob
import json
import vltest_bootstrap

test.scenarios('vlt')

test.lint(v_flags=["--assert --timing --dumpi-tree 3 --dumpi-tree-json 3 --no-json-edit-nums"])

# The JSON dump of an NFA-lowered design must stay parseable
jsons = glob.glob(test.obj_dir + "/V" + test.name + "_*.tree.json")
if not jsons:
    test.error("No .tree.json dumped")
for fn in jsons:
    with open(fn, 'r', encoding="utf8") as fh:
        json.load(fh)

# The tree dump must show the lowered assertion with its [NFA] marker
test.file_grep_any(glob.glob(test.obj_dir + "/V" + test.name + "_*.tree"), r'ASSERT.*\[NFA\]')

test.passes()
