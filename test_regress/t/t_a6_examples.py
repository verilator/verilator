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

test.clean_command = '/bin/rm -rf ../examples/*/build ../examples/*/obj*'

root = ".."

if not os.path.exists(root + "/.git"):
    test.skip("Not in a git repository")

examples = sorted(test.glob_some(root + "/examples/*"))
for example in examples:
    test.run(cmd=[os.environ["MAKE"], "-C", example])

test.passes()
