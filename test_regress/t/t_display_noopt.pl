#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

top_filename("t/t_display.v");

compile (
	 verilator_flags2 => ["-O0"],
	 );

execute (
	 check_finished=>1,
	 expect=>quotemeta(dequote(
'[0] In top.v: Hi
[0] In top.v.sub
[0] In top.v.sub.subblock
[0] In top.v.sub2
[0] In top.v.sub2.subblock2
[0] Back \ Quote "
[0] %X=00c %0X=c %0O=14 %B=000001100
[0] %x=00c %0x=c %0o=14 %b=000001100
[0] %D= 12 %d= 12 %01d=12 %06d=000012 %6d=    12
[0] %x=00abbbbcccc %0x=abbbbcccc %o=00527356746314 %b=00000101010111011101110111100110011001100
[0] %x=00abc1234567812345678 %0x=abc1234567812345678 %o=012570110642547402215053170 %b=000001010101111000001001000110100010101100111100000010010001101000101011001111000
[0] %t=                   0 %03t=  0 %0t=0

[0] %s=! %s= what! %s= hmmm!1234
[0] hello, from a very long string. Percent %s are literally substituted in.
[0] Embedded <#013> return
[0] Embedded
multiline
*-* All Finished *-*
')),
     );

ok(1);

# Don't put control chars into our source repository, pre-compress instead
sub dequote { my $s = shift; $s =~ s/<#013>/\r/g; $s; }

1;
