#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# $Id$
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2007 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

compile (
	 fails=>1,
	 expect=>
'%Error: t/t_inst_array_bad.v:19: Port connection __pinNumber2 as part of a module instance array  requires 1 or 8 bits, but connection\'s VARREF generates 9 bits.
%Error: Exiting due to.*',
	 );

ok(1);
1;
