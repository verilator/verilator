#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

my $waiver_filename = "$Self->{obj_dir}/$Self->{name}_waiver.vlt";

lint(
    verilator_flags2 => ["--lint-only --language 1364-2001 --waiver-output ${waiver_filename}"],
    fails => 1,
    expect_filename => $Self->{golden_filename},
    );

if (-e $waiver_filename) {
    error("Waiver file generated, not expected..");
}

ok(1);
1;
