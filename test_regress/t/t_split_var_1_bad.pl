#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

scenarios(simulator => 1);

compile(
    fails => 1,
    verilator_flags2 => ['--stats '],
    expect_filename => $Self->{golden_filename},
);

file_grep($Self->{stats}, qr/SplitVar,\s+Split packed variables\s+(\d+)/i, 0);
file_grep($Self->{stats}, qr/SplitVar,\s+Split unpacked arrays\s+(\d+)/i, 0);
ok(1);
1;
