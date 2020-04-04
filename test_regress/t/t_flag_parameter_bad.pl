#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2008 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

top_filename("t/t_flag_parameter.v");

lint(
    fails => 1,
    # It is not possible to put them into the options file
    v_flags2 => ['-GPARAM_THAT_DOES_NON_EXIST=1'],
    expect_filename => $Self->{golden_filename},
    );

ok(1);
1;
