#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
	 );

execute (
	 check_finished=>1,
	 expect=> quotemeta(
'[0] lp %x=0bbccc %x=0bbccc %o=2736314 %b=010111011110011001100 %0d=769228 %d=  769228
[0] ln %x=1bbccc %x=1bbccc %o=6736314 %b=110111011110011001100 %0d=-279348 %d= -279348
[0] qp %x=001bbbbcccc %x=001bbbbcccc %o=00067356746314 %b=00000000110111011101110111100110011001100 %0d=7444614348 %d=    7444614348
[0] qn %x=101bbbbcccc %x=101bbbbcccc %o=20067356746314 %b=10000000110111011101110111100110011001100 %0d=-1092067013428 %d=-1092067013428
[0] wp %x=000bc1234567812345678 %x=000bc1234567812345678 %o=000570110642547402215053170 %b=000000000101111000001001000110100010101100111100000010010001101000101011001111000
[0] wn %x=000bc1234577812345678 %x=000bc1234577812345678 %o=000570110642567402215053170 %b=000000000101111000001001000110100010101110111100000010010001101000101011001111000
'),
     );

ok(1);
1;
