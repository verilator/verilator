#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

compile (
    v_flags2 => ["--stats"],
    );

execute (
	 check_finished=>1,
     );

if ($Self->{v3}) {
    #Optimization is disabled
    #file_grep ($Self->{stats}, qr/Optimizations, Gaters inserted\s+3/i);
}

ok(1);
1;
