#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);
top_filename("t/t_hier_block.v");

lint(
    fails => 1,
    verilator_flags2 => ['--hierarchical-block',
                         'modName,mangledName,param0,"paramValue0",param0,"paramValue1",param1,2,param3',
                         '--hierarchical-block',
                         'modName',
                         '--hierarchical-block',
                         'mod0,mod1,\'"str\\\'', # end with backslash
                         '--hierarchical-block',
                         'mod2,mod3,\'"str\\a\'', # unexpected 'a' after backslash
                         '--hierarchical-block',
                         'mod4,mod5,\'"str"abc\',', # not end with "
                         '--hierarchical-block',
                         'mod6,mod7,\'"str"\',', # end with ,
                         '--hierarchical-block',
                         'mod8,mod9,\'s"tr"\',', # unexpected "
                         '--hierarchical-block',
                         'modA,modB,param,', # end with ,
                     ],
    expect_filename => $Self->{golden_filename},
    );

ok(1);

1;
