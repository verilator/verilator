#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2008 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

top_filename("t/t_psl_basic.v");

compile (
	 v_flags2 => [$Self->{v3}?'--psl --sp --coverage-user':''],
	 );

execute (
	 check_finished=>1,
	 );

# Allow old Perl format dump, or new binary dump
file_grep ($Self->{coverage_filename}, qr/(,o=>'cover'.*,c=>2\)|o.cover.* 2\n)/);
file_grep ($Self->{coverage_filename}, qr/(DefaultClock.*,c=>1\)|DefaultClock.* 1\n)/);
file_grep ($Self->{coverage_filename}, qr/(ToggleLogIf.*,c=>9\)|ToggleLogIf.* 9\n)/);

ok(1);
1;
