#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('dist')

root = ".."

if not os.path.exists(root + "/.git"):
    test.skip("Not in a git repository")

### Must trim output before and after our file list
warns = {}
summary = None

status = test.run_capture("cd " + root + " && git ls-files -o --exclude-standard")

if test.verbose:
    print("-ST " + status)
for filename in sorted(status.split()):
    if re.search('nodist', filename):
        continue
    warns[filename] = "File not in git or .gitignore: " + filename
    summary = "Files untracked in git or .gitignore:"

if summary:
    # First warning lists everything as that's shown in the driver summary
    test.error(summary + " " + ' '.join(sorted(warns.keys())))
    for filename in sorted(warns.keys()):
        test.error(warns[filename])

test.passes()
