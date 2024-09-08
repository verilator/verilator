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


def check_evals():
    got = 0
    for filename in test.glob_some(test.obj_dir + "/*.cpp"):
        wholefile = test.file_contents(filename)
        if re.search(r'__eval_nba__[0-9]+\(.*\)\s*{', wholefile):
            got += 1

    if got < 3:
        test.error("Too few _eval functions found: " + str(got))


test.compile(v_flags2=["--output-split 1 --output-split-cfuncs 20"],
             verilator_make_gmake=False)  # Slow to compile, so skip it)

check_evals()

test.passes()
