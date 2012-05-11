#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
	 verilator_flags2 => ["--stats"],
	 );

if ($Self->{vlt}) {
    file_grep ($Self->{stats}, qr/Optimizations, Lifetime assign deletions\s+(\d+)/i, 4);
    file_grep ($Self->{stats}, qr/Optimizations, Lifetime constant prop\s+(\d+)/i, 2);
}

execute (
	 check_finished=>1,
     );

ok(1);
1;
