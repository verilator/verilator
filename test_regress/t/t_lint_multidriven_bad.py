#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('linter')

root = ".."

if not os.path.exists(root + "/.git"):
    test.skip("Not in a git repository")

test.lint(fails=True, expect_filename=test.golden_filename)

test.extract(in_filename=test.top_filename,
             out_filename="../docs/gen/ex_MULTIDRIVEN_faulty.rst",
             lines="31-36")

test.extract(in_filename=test.golden_filename,
             out_filename="../docs/gen/ex_MULTIDRIVEN_msg.rst",
             lines="10,11,14")

test.passes()
