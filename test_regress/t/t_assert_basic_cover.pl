#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

top_filename("t/t_assert_basic.v");

compile (
	 verilator_flags2 => ['--assert --cc --coverage-user'],
	 );

execute (
	 check_finished=>1,
	 );

#Needs work
print "-Info:  NOT checking for coverage\n";
#file_grep ($Self->{coverage_filename}, qr/t=>'psl_cover',o=>'cover',c=>2\);/);
#file_grep ($Self->{coverage_filename}, qr/DefaultClock.*,c=>1\);/);
#file_grep ($Self->{coverage_filename}, qr/ToggleLogIf.*,c=>9\);/);

ok(1);
1;
