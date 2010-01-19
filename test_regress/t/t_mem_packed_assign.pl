#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2010 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
         v_flags => ["--lint-only"],
	 fails=>1,
	 expect=>
'%Error: t/t_mem_packed_assign.v:\d+: Unsupported: Assignment between packed arrays of different dimensions
%Error: t/t_mem_packed_assign.v:\d+: Unsupported: Assignment between packed arrays of different dimensions
%Error: Exiting due to.*',
	 );

ok(1);
1;
