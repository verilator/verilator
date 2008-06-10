#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

compile (
	 v_flags2 => ["--lint-only"],
	 fails=>1,
	 expect=>
'%Error: t/t_display_bad.v:\d+: Missing arguments for \$display format
%Error: t/t_display_bad.v:\d+: Extra arguments for \$display format
%Error: t/t_display_bad.v:\d+: Unknown \$display format code: %q
%Error: Exiting due to.*',
	 );

ok(1);
1;

