#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
	 );

execute (
	 check_finished=>1,
	 expect=>quotemeta(
qq{pre thrupre thrumid thrupost post: "right side"
left side: "right side"
left side: "right side"
left_side: "right_side"
na: "right_side"
prep ( midp1 left_side midp2 ( outp ) ): "right_side"
na: "nana"
left_side right_side: "left_side right_side"
left side: "right side"
: ""
left side: "right side"
left side: "right side"
standalone
twoline: "first   second"
Line 49 File "t/t_pp_display.v"
*-* All Finished *-*
}));

ok(1);
1;
