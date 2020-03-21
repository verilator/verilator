#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

lint(
    fails => 1,
    # Can't use expect_filename here as unstable output
    expect =>
'%Error: Circular logic when ordering code .*
 *t/t_order_loop_bad.v:\d+:\d+: + Example path: ALWAYS
 *t/t_order_loop_bad.v:\d+:\d+: + Example path: t.ready
 *t/t_order_loop_bad.v:\d+:\d+: + Example path: ACTIVE
.*',
    );

ok(1);
1;
