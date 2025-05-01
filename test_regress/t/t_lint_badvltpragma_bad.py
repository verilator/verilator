#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

root = ".."

if not os.path.exists(root + "/.git"):
    test.skip("Not in a git repository")

test.lint(fails=True, expect_filename=test.golden_filename)

test.extract(in_filename=test.top_filename,
             out_filename=root + "/docs/gen/ex_BADVLTPRAGMA_faulty.rst",
             lines="7")

test.extract(in_filename=test.golden_filename,
             out_filename=root + "/docs/gen/ex_BADVLTPRAGMA_msg.rst",
             lines="1-3")

test.passes()
