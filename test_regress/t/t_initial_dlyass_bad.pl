#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

top_filename("t_initial_dlyass.v");

compile (
	 v_flags2 => ["--lint-only"],
	 fails=>1,
	 expect=>
qr{%Warning-INITIALDLY: t/t_initial_dlyass.v:\d+: Delayed assignments .*
%Error: Exiting due to.*},
     );

ok(1);
1;
