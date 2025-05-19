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

test.lint(verilator_flags2=["--lint-only"],
          fails=test.vlt_all,
          expect_filename=test.golden_filename)

test.extract(in_filename=test.top_filename,
             out_filename=root + "/docs/gen/ex_WIDTHEXPAND_1_faulty.rst",
             lines="8-10")

test.extract(in_filename=test.golden_filename,
             out_filename=root + "/docs/gen/ex_WIDTHEXPAND_1_msg.rst",
             lineno_adjust=-7,
             regexp=r'Warning-WIDTH')

test.extract(in_filename=test.top_filename,
             out_filename=root + "/docs/gen/ex_WIDTHEXPAND_1_fixed.rst",
             lines="18")

test.passes()
