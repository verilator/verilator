#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
	 v_flags2 => ["--lint-only"],
	 fails=>$Self->{v3},
	 expect=>
'%Error: t/t_select_bad_range.v:\d+: Selection index out of range: 44:44 outside 43:0
%Error: t/t_select_bad_range.v:\d+: Selection index out of range: 44:41 outside 43:0
%Error: Exiting due to.*',
	 );

ok(1);
1;

