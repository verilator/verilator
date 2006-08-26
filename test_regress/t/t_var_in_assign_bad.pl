#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# $Id:$
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2005 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

compile (
	 fails=>1,
	 expect=>
'%Error: t/t_var_in_assign_bad.v:\d+: Assigning to input variable: value
%Error: t/t_var_in_assign_bad.v:\d+: Assigning to input variable: valueSub
%Error: Exiting due to.*',
	 ) if $Last_Self->{v3};

ok(1);
1;
