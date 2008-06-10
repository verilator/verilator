#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2007 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

top_filename("t/t_psl_basic.v");

compile (
	 v_flags2 => [$Last_Self->{v3}?'--psl --sp --coverage-user':''],
	 );

execute (
	 check_finished=>1,
	 );

file_grep ($Last_Self->{coverage_filename}, qr/t=>'psl_cover',o=>'cover',c=>2\);/);
file_grep ($Last_Self->{coverage_filename}, qr/DefaultClock.*,c=>1\);/);
file_grep ($Last_Self->{coverage_filename}, qr/ToggleLogIf.*,c=>9\);/);

ok(1);
1;
