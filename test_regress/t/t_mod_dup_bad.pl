#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2008 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

$Self->skip("Verilator only test") if !$Self->{vlt};

compile (
	 fails=>1,
	 expect=>
'%Error-MODDUP: t/t_mod_dup_bad.v:\d+: Duplicate declaration of module: a
%Error-MODDUP: t/t_mod_dup_bad.v:\d+: ... Location of original declaration
.*
%Error: Exiting due to.*',
	 );

ok(1);
1;
