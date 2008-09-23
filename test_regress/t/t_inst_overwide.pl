#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2004 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

compile (
	 make_top_shell=>0,
	 verilator_flags=> [qw(-sp -Wno-WIDTH)],
	 verilator_make_gcc=>0,
	 );

#No execute ()

ok(1);
1;
