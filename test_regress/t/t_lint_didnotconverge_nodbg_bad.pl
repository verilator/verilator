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

top_filename("t/t_lint_didnotconverge_bad.v");

compile(
    make_flags => 'CPPFLAGS_ADD=-UVL_DEBUG',
    );

execute(
    fails => 1,
    expect_filename => $Self->{golden_filename},
    );

extract(
    in => $Self->{golden_filename},
    out => "../docs/gen/ex_DIDNOTCONVERGE_nodbg_msg.rst",
    lines => "1");

ok(1);
1;
