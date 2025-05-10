#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')

test.compile()

test.execute(all_run_flags=["+verilator+bad+flag+testing"],
             fails=True,
             expect_filename="t/" + test.name + "__a.out")

test.execute(all_run_flags=["+verilator+rand+reset+-1"],
             fails=True,
             expect_filename="t/" + test.name + "__b.out")

test.execute(all_run_flags=["+verilator+rand+reset+3"],
             fails=True,
             expect_filename="t/" + test.name + "__c.out")

test.execute(all_run_flags=["+verilator+prof+exec+window+0"],
             fails=True,
             expect_filename="t/" + test.name + "__d.out")

test.execute(all_run_flags=["+verilator+prof+exec+window+1000000000000000000000000"],
             fails=True,
             expect_filename="t/" + test.name + "__e.out")

test.passes()
