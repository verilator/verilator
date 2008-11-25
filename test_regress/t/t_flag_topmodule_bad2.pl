#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2008 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

top_filename("t/t_flag_topmodule.v");

compile (
	 fails=>$Self->{v3},
	 v_flags2 => ["--top-module notfound"],
	 nc=>0,  # Need to get it not to give the prompt
	 expect=>
'%Error: Specified --top-module \'notfound\' was not found in design.
%Error: Exiting due to.*',
	 ) if $Self->{v3};

ok(1);
1;
