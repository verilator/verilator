#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2005 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(linter => 1);

lint(
    fails => 1,
    # Used to be %Error: t/t_order_wireloop.v:\d+: Wire inputs its own output, creating circular logic .wire x=x.
    # However we no longer gate optimize this
    expect_filename => $Self->{golden_filename},
    );

ok(1);
1;
