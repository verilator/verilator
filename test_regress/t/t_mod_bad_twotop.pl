#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# $Id$
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

compile (
	 fails=>$Last_Self->{v3},
	 nc=>0,  # Need to get it not to give the prompt
	 expect=>
'%Error-MULTITOP: t/t_mod_bad_twotop.v:\d+: Unsupported: Multiple top level modules: t2 and t
%Error: Exiting due to.*',
	 );

ok(1);
1;

