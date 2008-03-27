#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# $Id: t_delay.pl 965 2007-10-31 20:29:07Z wsnyder $
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

compile (
	 );

execute (
	 check_finished=>1,
	 expect=>quotemeta(
'pre thrupre thrumid thrupost post: "right side"
left side: "right side"
left side : "right side "
left_side : "left_side "
na : "left_side "
prep ( midp1 left_side midp2 ( outp ) ) : "left_side "
na: "nana"
left_side left_side : "left_side left_side "
: ""
left side: "right side"
left side  : "right side  "
twoline: "first   second"
*-* All Finished *-*
'));

ok(1);
1;
