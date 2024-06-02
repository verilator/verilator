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
    verilator_flags2 => ['--hierarchical',
                         '--hierarchical-child 1',
                         'modName',
                     ],
    expect_filename => $Self->{golden_filename},
    );

ok(1);

1;
