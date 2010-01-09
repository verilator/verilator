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
'%Warning-CASEX: t/t_case_x_bad.v:\d+: Suggest casez \(with \?\'s\) in place of casex \(with X\'s\)
.*%Warning-CASEWITHX: t/t_case_x_bad.v:\d+: Use of x/\? constant in case statement, \(perhaps intended casex/casez\)
.*%Error: Exiting due to.*',
	 );

ok(1);
1;
