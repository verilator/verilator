#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
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
left_side : "right_side "
na : "right_side "
prep ( midp1 left_side midp2 ( outp ) ) : "right_side "
na: "nana"
`ls `rs : "`ls `rs "
: ""
left side: "right side"
left side  : "right side  "
twoline: "first   second"
*-* All Finished *-*
'));

ok(1);
1;
