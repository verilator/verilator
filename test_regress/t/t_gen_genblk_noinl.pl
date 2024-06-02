#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

top_filename("t_gen_genblk.v");
golden_filename("t/t_gen_genblk.out");

scenarios(simulator => 1);

$Self->{sim_time} = 11000;

compile(
    v_flags2 => ["-fno-inline"],
    );

execute(
    expect_filename => $Self->{golden_filename},
    );

ok(1);
1;
