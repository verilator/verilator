#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# $Id$
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2007 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

top_filename("t/t_clk_latch.v");

my $fail = ($Last_Self->{v3} && verilator_version() !~ /\(ord\)/);

compile (
	 v_flags2 => ['+define+EDGE_DETECT_STYLE'],
	 fails => $fail,
	 );

execute (
	 check_finished => !$fail,
	 ) if !$fail;

ok(1);
1;
