#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2010 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

$ENV{VERILATOR_TEST_NO_GDB} and $Self->skip("Skipping due to VERILATOR_TEST_NO_GDB");

compile (
	 v_flags2 => ["--lint-only --debug --gdbbt --debug-sigsegv"],
	 fails=>$Self->{v3},
	 expect=>
'.*
Program received signal SIGSEGV, Segmentation fault.
.*in V3Options::.*
.*%Error: Command Failed.*',
	 );

ok(1);
1;
