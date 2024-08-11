#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder and Ethan Sifferman. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

top_filename("t/t_vlt_match_error.v");

lint(
    verilator_flags2 => ["-DT_VLT_MATCH_ERROR_2 --lint-only -Wall t/t_vlt_match_error.v t/t_vlt_match_error.vlt"],
    fails => 1,
    expect_filename => $Self->{golden_filename},
    );

ok(1);
1;
