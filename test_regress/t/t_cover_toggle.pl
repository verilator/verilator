#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
	 verilator_flags2 => ['--cc --coverage-toggle --stats'],
	 );

execute (
	 check_finished=>1,
	 );

# Read the input .v file and do any CHECK_COVER requests
inline_checks();

file_grep ($Self->{stats}, qr/Coverage, Toggle points joined\s+(\d+)/i, 25)
    if $Self->{vlt};

ok(1);
1;
