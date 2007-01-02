#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# $Id$
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2007 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

top_filename("t/t_assert_synth.v");

compile (
	 v_flags2 => ['+define+FAILING_FULL',
		      '+define+FAILING_PARALLEL',
		      '+define+FAILING_OH',
		      '+define+FAILING_OC',
		      ],
	 );

execute (
	 check_finished=>1,
	 );

ok(1);
1;
