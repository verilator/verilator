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

top_filename("t/t_assert_inside_cond.v");

compile(
    verilator_flags2 => ["-x-assign 0 --assert +define+T_ASSERT_INSIDE_COND_BAD"],
    );

execute(
    fails => 1,
    expect_filename => $Self->{golden_filename},
    );

ok(1);
1;
