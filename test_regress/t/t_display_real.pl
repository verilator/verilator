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
'[0] e=0.000000e+00 e1=0.000000e+00 e30=0e+00 e32=0.00e+00
[0] f=0.000000 f1=0.000000e+00 f30=0e+00 f32=0.00e+00
[0] g=0 g1=0.000000e+00 g30=0e+00 g32=0.00e+00

[0] e=1.000000e+00 e1=1.000000e+00 e30=1e+00 e32=1.00e+00
[0] f=1.000000 f1=1.000000e+00 f30=1e+00 f32=1.00e+00
[0] g=1 g1=1.000000e+00 g30=1e+00 g32=1.00e+00

[0] e=1.000000e-01 e1=1.000000e-01 e30=1e-01 e32=1.00e-01
[0] f=0.100000 f1=1.000000e-01 f30=1e-01 f32=1.00e-01
[0] g=0.1 g1=1.000000e-01 g30=1e-01 g32=1.00e-01

[0] e=1.234500e-15 e1=1.234500e-15 e30=1e-15 e32=1.23e-15
[0] f=0.000000 f1=1.234500e-15 f30=1e-15 f32=1.23e-15
[0] g=1.2345e-15 g1=1.234500e-15 g30=1e-15 g32=1.23e-15

[0] e=2.579000e+15 e1=2.579000e+15 e30=3e+15 e32=2.58e+15
[0] f=2579000000000000.000000 f1=2.579000e+15 f30=3e+15 f32=2.58e+15
[0] g=2.579e+15 g1=2.579000e+15 g30=3e+15 g32=2.58e+15

r8=  3 n1=1 n2=0.1
n1=1 n2=0.1 r8=  3
'),
     );

ok(1);
1;
