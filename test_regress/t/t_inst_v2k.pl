#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# $Id:$
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

compile (
	 v_flags2 => ['+libext+.vi+.extranoneed'],
	 nc => 0, # Error: Multiple +libext flags found
	 vcs => 0,
	 );

execute (
	 check_finished=>1,
     );

ok(1);
1;
