#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2007 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

top_filename("t/t_unopt_converge.v");

$Self->{vlt} or $Self->skip("Verilator only test");

compile (
	 fails=>1,
	 expect=> '%Warning-UNOPT: t/t_unopt_converge.v:\d+: Signal unoptimizable: Feedback to public clock or circular logic: x
.*
%Error: Exiting due to '
     );

ok(1);
1;
