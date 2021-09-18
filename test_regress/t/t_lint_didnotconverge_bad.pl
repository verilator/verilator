#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2008 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

compile(
    verilator_flags2 => ["--prof-cfuncs"],
    );

execute(
    fails => 1,
    expect_filename => $Self->{golden_filename},
    );

extract(
    in => $Self->{top_filename},
    out => "../docs/gen/ex_DIDNOTCONVERGE_faulty.rst",
    lines => "16-17");

extract(
    in => $Self->{golden_filename},
    out => "../docs/gen/ex_DIDNOTCONVERGE_msg.rst",
    lines => "2-5");

ok(1);
1;
