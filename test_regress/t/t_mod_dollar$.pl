#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2019 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

# This doesn't use the general compile rule as we want to make sure we form
# prefix properly using post-escaped identifiers
run(cmd => ["../bin/verilator",
            "--cc",
            "--Mdir obj_vlt/t_mod_dollar",
            "--exe --build --main",
            't/t_mod_dollar$.v',
    ],
    verilator_run => 1,
    );

ok(1);
1;
