#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# $Id:$
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2005 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

compile (
	 fails=>$Last_Self->{v3},
	 expect=>
'%Error: t/t_order_wireloop.v:\d+: Wire inputs its own output, creating circular logic .wire x=x.
',
	 );

ok(1);
1;
