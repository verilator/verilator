#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Multiple Model Test Module
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')
test.pli_filename = "t/t_wrapper_context.cpp"
test.top_filename = "t/t_wrapper_context.v"

test.compile(
    make_top_shell=False,
    make_main=False,
    # link threads library, add custom .cpp code, add tracing & coverage support
    verilator_flags2=["--exe", test.pli_filename, "--trace-fst --coverage -cc"],
    threads=1,
    make_flags=['CPPFLAGS_ADD=-DVL_NO_LEGACY'])

test.execute()

test.passes()
