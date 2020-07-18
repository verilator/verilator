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

top_filename("t/t_clk_latch.v");

my $fail = $Self->{vlt_all};

compile(
    v_flags2 => ['+define+EDGE_DETECT_STYLE'],
    fails => $fail,
    );

execute(
    check_finished => !$fail,
    ) if !$fail;

ok(1);
1;
