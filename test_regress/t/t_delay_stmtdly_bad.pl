#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

top_filename("t/t_delay.v");

$Self->{vlt} or $Self->skip("Verilator only test");

compile (
	 verilator_flags2 => ['-Wall -Wno-DECLFILENAME'],
	 fails=>1,
	 expect=>
'%Warning-ASSIGNDLY: t/t_delay.v:\d+: Unsupported: Ignoring delay on this assignment/primitive.
%Warning-ASSIGNDLY: Use .*
%Warning-ASSIGNDLY: t/t_delay.v:\d+: Unsupported: Ignoring delay on this assignment/primitive.
%Warning-ASSIGNDLY: t/t_delay.v:\d+: Unsupported: Ignoring delay on this assignment/primitive.
%Warning-STMTDLY: t/t_delay.v:\d+: Unsupported: Ignoring delay on this delayed statement.
.*%Error: Exiting due to.*',
	 );

ok(1);
1;
