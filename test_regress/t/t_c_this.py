#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')

test.compile()

if test.vlt_all:
    # The word 'this' (but only the whole word 'this' should have been replaced
    # in the contents.
    has_this = False
    has_xthis = False
    has_thisx = False
    has_xthisx = False
    for filename in test.glob_some(test.obj_dir + "/" + test.vm_prefix +
                                   "___024root__DepSet_*__0.cpp"):
        text = test.file_contents(filename)
        if re.search(r'\bthis->clk\b', text):
            has_this = True
        if re.search(r'\bxthis\b', text):
            has_xthis = True
        if re.search(r'\bthisx\b', text):
            has_thisx = True
        if re.search(r'\bxthisx\b', text):
            has_xthisx = True

    if has_this:
        test.error("Some file has 'this->clk'")
    if not has_xthis:
        test.error("No file has 'xthis'")
    if not has_thisx:
        test.error("No file has 'thisx'")
    if not has_xthisx:
        test.error("No file has 'xthisx'")

test.passes()
