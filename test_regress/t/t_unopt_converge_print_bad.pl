#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2007 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

top_filename("t/t_unopt_converge.v");
#$Self->{verilated_debug} = 1;

compile (
	 v_flags2 => ['+define+ALLOW_UNOPT'],
	 make_flags => 'CPPFLAGS_ADD=-DVL_DEBUG',
	 );

execute (
	 fails=>1,
	 expect=> '%Error: \S+:\d+: Verilated model didn\'t converge',
     ) if $Self->{vlt};

ok(1);
1;
