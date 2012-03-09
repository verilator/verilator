#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

$Self->{vlt} or $Self->skip("Verilator only test");
$ENV{VERILATOR_TEST_NO_GDB} and $Self->skip("Skipping due to VERILATOR_TEST_NO_GDB");

compile (
	 verilator_flags2 => ["--debug-sigsegv"],
	 fails=>$Self->{v3},
	 expect=>
'%Error: Verilator internal fault, sorry.  Consider trying --debug --gdbbt
%Error: Command Failed.*',
	 );

ok(1);
1;
