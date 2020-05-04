#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

top_filename("t/t_assert_synth.v");

compile(
    v_flags2 => ['+define+FAILING_FULL +define+ATTRIBUTES'],
    verilator_flags2 => ['--assert'],
    nc_flags2 => ['+assert'],
    );

execute(
    check_finished => 0,
    fails => $Self->{vlt_all},
    expect_filename => $Self->{golden_filename},
    );

ok(1);
1;
