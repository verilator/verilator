#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2008 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

top_filename("t/t_assert_basic.v");

compile (
	 v_flags2 => ['+define+FAILING_ASSERTIONS',
	              $Last_Self->{v3}?'--assert':($Last_Self->{nc}?'+assert':'')],
	 fails => $Last_Self->{nc},
	 );

execute (
	 fails => 1,
	 );

ok(1);
1;
