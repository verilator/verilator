#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2008 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

top_filename("t/t_flag_topmodule.v");

$Self->{vlt} or $Self->skip("Verilator only test");

compile (
	 fails=>$Self->{v3},
	 nc=>0,  # Need to get it not to give the prompt
	 expect=>
'%Error-MULTITOP: t/t_flag_topmodule.v:\d+: Unsupported: Multiple top level modules: .*
%Error-MULTITOP: t/t_flag_topmodule.v:\d+: Fix, or use --top-module option to select which you want.
%Error: Exiting due to.*',
	 );

ok(1);
1;
