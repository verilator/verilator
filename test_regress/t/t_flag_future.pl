#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2008 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

compile (
	 verilator_flags2 => [qw(-Wfuture-FUTURE1 -Wfuture-FUTURE2)],
	 );

execute (
	 check_finished=>1,
	 );

ok(1);
1;
