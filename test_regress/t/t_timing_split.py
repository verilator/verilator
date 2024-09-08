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


def check_splits():
    got1 = False
    gotSyms1 = False
    for filename in test.glob_some(test.obj_dir + "/*.cpp"):
        if re.search(r'Syms__1', filename):
            gotSyms1 = True
        elif re.search(r'__1', filename):
            got1 = True
    if not got1:
        test.error("No __1 split file found")
    if not gotSyms1:
        test.error("No Syms__1 split file found")


test.compile(timing_loop=True,
             verilator_flags2=["--timing --output-split-cfuncs 1 -CFLAGS -Werror"])

test.execute()

if test.have_coroutines:
    check_splits()

test.passes()
