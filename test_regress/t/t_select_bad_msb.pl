#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

$Self->{vlt} or $Self->skip("Verilator only test");

compile (
	 fails=>1,
	 expect=>
'%Warning-LITENDIAN: t/t_select_bad_msb.v:\d+: Little bit endian vector: MSB < LSB of bit range: 0:22
.*
%Error: Exiting due to.*',
	 );

ok(1);
1;

