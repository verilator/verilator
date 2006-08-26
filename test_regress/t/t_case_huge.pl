#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# $Id$
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

compile (
	 v_flags2 => ["--stats --profile-cfuncs"],
	 );

if ($Last_Self->{v3}) {
    file_grep ($Last_Self->{stats}, qr/Optimizations, Tables created\s+10/i);
    file_grep ($Last_Self->{stats}, qr/Optimizations, Combined CFuncs\s+10/i);
}

execute (
	 check_finished=>1,
     );

ok(1);
1;
