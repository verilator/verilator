#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2007 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

top_filename("t/t_unopt_converge_initial.v");

compile(
    v_flags2 => ['+define+ALLOW_UNOPT'],
    );

execute(
    fails => 1,
    expect_filename => $Self->{golden_filename},
    ) if $Self->{vlt_all};

ok(1);
1;
