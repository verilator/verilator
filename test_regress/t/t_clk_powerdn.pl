#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2007 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

my $fail = ($Last_Self->{v3} && verilator_version() !~ /\(ord\)/);

compile (
	 );

execute (
	 check_finished => !$fail,
	 fails => $fail,
	 );

ok(1);
1;
