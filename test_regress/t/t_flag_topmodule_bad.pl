#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# $Id$
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2008 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

top_filename("t/t_flag_topmodule.v");

compile (
	 fails=>$Last_Self->{v3},
	 nc=>0,  # Need to get it not to give the prompt
	 expect=>
'%Error-MULTITOP: t/t_flag_topmodule.v:\d+: Unsupported: Multiple top level modules: .*
%Error-MULTITOP: t/t_flag_topmodule.v:\d+: Fix, or use --top-module option to select which you want.
%Error: Exiting due to.*',
	 ) if $Last_Self->{v3};

ok(1);
1;
