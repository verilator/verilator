#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
	 v_flags2 => ["--lint-only"],
	 fails=>$Self->{v3},
	 expect=>
q{%Warning-WIDTH: t/t_func_bad_width.v:\d+: Operator FUNCREF 'MUX' expects 40 bits on the Function Argument, but Function Argument's VARREF 'in' generates 39 bits.
%Warning-WIDTH: Use [^\n]+
%Warning-WIDTH: t/t_func_bad_width.v:\d+: Operator ASSIGN expects 4 bits on the Assign RHS, but Assign RHS.s FUNCREF 'MUX' generates 32 bits.
%Error: Exiting due to},
	 );

ok(1);
1;
