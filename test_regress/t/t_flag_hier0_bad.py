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
test.top_filename = "t/t_hier_block.v"

test.lint(
    fails=True,
    verilator_flags2=[
        '--hierarchical-block',
        'modName,mangledName,param0,"paramValue0",param0,"paramValue1",param1,2,param3',
        '--hierarchical-block', 'modName',
        '--hierarchical-block', 'mod0,mod1,\'"str\\\'',  # end with backslash
        '--hierarchical-block', 'mod2,mod3,\'"str\\a\'',  # unexpected 'a' after backslash
        '--hierarchical-block', 'mod4,mod5,\'"str"abc\',',  # not end with "
        '--hierarchical-block', 'mod6,mod7,\'"str"\',',  # end with ,
        '--hierarchical-block', 'mod8,mod9,\'s"tr"\',',  # unexpected "
        '--hierarchical-block', 'modA,modB,param,',  # end with ,
    ],
    expect_filename=test.golden_filename)  # yapf:disable

test.passes()
