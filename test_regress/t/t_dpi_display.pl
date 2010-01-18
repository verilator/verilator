#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
	 v_flags2 => ["t/t_dpi_display_c.cpp"],
	 );

execute (
	 check_finished=>1,
	 expect=>quotemeta(
q{dpii_display_call: 
dpii_display_call: c
dpii_display_call: co
dpii_display_call: cons
dpii_display_call: constant
dpii_display_call: constant_value
one10=0000000a 
dpii_display_call: one10=0000000a 
Mod=top.v 16=         10 10=0000000a 
dpii_display_call: Mod=top.v 16=         10 10=0000000a 
*-* All Finished *-*
}),
     );

ok(1);
1;
