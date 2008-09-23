#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2008 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

compile (
	 v_flags2 => ["--lint-only"],
	 fails=>1,
	 expect=>
'%Error: t/t_case_genx_bad.v:\d+: Use of x/\? constant in generate case statement, \(no such thing as \'generate casez\'\)
%Error: Exiting due to.*',
	 );

ok(1);
1;
