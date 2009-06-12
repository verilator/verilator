#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
	 v_flags2 => ["--lint-only"],
	 fails=>1,
	 expect=>
'%Error: t/t_const_overflow_bad.v:\d+: Too many digits for 94 bit number: 94\'d123456789012345678901234567890
%Error: t/t_const_overflow_bad.v:\d+: Too many digits for 8 bit number: 8\'habc
%Error: t/t_const_overflow_bad.v:\d+: Too many digits for 6 bit number: 6\'o1234
%Error: t/t_const_overflow_bad.v:\d+: Too many digits for 3 bit number: 3\'b1111
%Error: Exiting due to.*',
	 );

ok(1);
1;
