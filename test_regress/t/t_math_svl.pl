#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# $Id:$
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2005 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

compile (
	 ) if $Last_Self->{v3};

execute (
	 check_finished=>1,
	 # Make sure we get the finish statement called
	 expect=>
'\*-\* All Finished \*-\*
Goodbye world, at cycle \d+.*',
     ) if $Last_Self->{v3};

ok(1);
1;
