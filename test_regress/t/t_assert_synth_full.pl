#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2008 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

top_filename("t/t_assert_synth.v");

compile (
	 v_flags2 => [$Last_Self->{v3}?'--assert':($Last_Self->{nc}?'+assert':''),
		      '+define+FAILING_FULL',],
	 );

execute (
	 check_finished=>0,
	 fails=>1,
	 expect=>
'%Error: t_assert_synth.v:\d+: Assertion failed in TOP.v: synthesis full_case'
	 );

ok(1);
1;
