#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

top_filename("t/t_udp.v");

compile (
	 fails=>$Self->{vlt},
	 expect=>
'%Error: t/t_udp.v:\d+: Unsupported: Verilog 1995 UDP Tables.  Use --bbox-unsup to ignore tables.
%Error: t/t_udp.v:\d+: Unsupported: Verilog 1995 UDP Tables.  Use --bbox-unsup to ignore tables.
%Error: Exiting due to '
	 );

execute (
     ) if !$Self->{vlt};

ok(1);
1;
