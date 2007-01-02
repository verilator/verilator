#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# $Id$
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2007 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

compile (
	 make_top_shell => 0,
	 make_main => 0,
	 v_flags2 => ["--exe t/$Last_Self->{name}.cpp"],
	 ) if $Last_Self->{v3};

execute (
	 check_finished=>1,
	 ) if $Last_Self->{v3};

ok(1);
1;
