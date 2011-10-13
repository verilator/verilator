#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

$Self->{vlt} or $Self->skip("Verilator only test");

compile (
	 v_flags2 => ["--lint-only"],
	 fails=>1,
	 expect=>
q{.*%Warning-WIDTH: t/t_lint_restore_bad.v:\d+: Operator ASSIGN expects 5 bits on the Assign RHS, but Assign RHS's CONST '64'h1' generates 64 bits.
%Warning-WIDTH: Use .*
%Error: Exiting due to.*},
    );

ok(1);
1;
