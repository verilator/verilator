#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
	 v_flags2 => ["--lint-only -Wwarn-VARHIDDEN"],
	 fails=>$Self->{v3},
	 expect=>
'%Warning-VARHIDDEN: t/t_var_bad_hide2.v:\d+: Declaration of signal hides declaration in upper scope: t
%Warning-VARHIDDEN: t/t_var_bad_hide2.v:\d+: ... Location of original declaration
.*
%Error: Exiting due to.*',
	 );

ok(1);
1;
