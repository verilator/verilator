#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
	 v_flags2 => ["--lint-only"],
	 fails=>1,
	 expect=>
q{%Warning-WIDTH: t/t_lint_repeat_bad.v:17: Operator ASSIGNW expects 1 bits on the Assign RHS, but Assign RHS's VARREF 'a' generates 2 bits.
%Warning-WIDTH: Use \"\/\* verilator lint_off WIDTH \*\/\" and lint_on around source to disable this message.
%Error: Exiting due to 1 warning}
	 );

ok(1);
1;
