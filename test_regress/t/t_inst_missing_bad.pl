#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
	 v_flags2 => ["--lint-only --Wall -Wno-DECLFILENAME"],
	 fails=>1,
	 expect=>
q{%Warning-PINNOCONNECT: t/t_inst_missing_bad.v:8: Cell pin is not connected: __pinNumber2
%Warning-PINNOCONNECT: Use .*
%Warning-PINCONNECTEMPTY: t/t_inst_missing_bad.v:8: Cell pin connected by name with empty reference: nc
%Warning-PINMISSING: t/t_inst_missing_bad.v:8: Cell has missing pin: missing
%Error: Exiting due to.*},
	 );

ok(1);
1;
