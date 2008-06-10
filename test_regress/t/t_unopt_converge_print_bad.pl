#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2007 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

top_filename("t/t_unopt_converge.v");
#$Last_Self->{verilated_debug} = 1;

compile (
	 v_flags2 => ['+define+ALLOW_UNOPT'],
	 make_flags => 'CPPFLAGS_ADD=-DVL_DEBUG',
	 );

execute (
	 fails=>1,
	 expect=> '%Error: \S+:\d+: Verilated model didn\'t converge',
     ) if $Last_Self->{v3};

ok(1);
1;
