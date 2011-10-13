#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

$Self->{vlt} or $Self->skip("Verilator only test");

compile (
	 verilator_flags2 => ["--debug-fatalsrc"],
	 fails=>$Self->{v3},
	 expect=>
'%Error: Internal Error: .*: --debug-fatal-src
%Error: Internal Error: See the manual and http://www.veripool.org/verilator for more assistance.
%Error: Command Failed.*',
	 );

ok(1);
1;
