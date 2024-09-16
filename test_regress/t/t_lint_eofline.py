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
test.top_filename = test.obj_dir + "/t_lint_eofline_bad.v"


def gen(filename):
    with open(filename, 'w', encoding="utf8") as fh:  # pylint: disable=unused-variable
        pass
    # Empty file should not EOFLINE warn


gen(test.top_filename)

test.lint(verilator_flags2=["-E -Wall -Wno-DECLFILENAME"], expect_filename=test.golden_filename)

test.passes()
