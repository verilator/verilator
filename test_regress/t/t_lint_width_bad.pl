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
q{.*%Warning-WIDTH: t/t_lint_width_bad.v:\d+: Operator VAR 'XS' expects 4 bits on the Initial value, but Initial value's CONST '\?32\?bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx' generates 32 bits.
%Warning-WIDTH: Use .*
%Warning-WIDTH: t/t_lint_width_bad.v:\d+: Operator ASSIGNW expects 5 bits on the Assign RHS, but Assign RHS's VARREF 'in' generates 4 bits.
%Warning-WIDTH: t/t_lint_width_bad.v:\d+: Operator SHIFTL expects 5 bits on the LHS, but LHS's CONST '1'h1' generates 1 bits.
%Warning-WIDTH: t/t_lint_width_bad.v:\d+: Operator ASSIGNW expects 6 bits on the Assign RHS, but Assign RHS's SHIFTL generates 7 bits.
%Warning-WIDTH: t/t_lint_width_bad.v:\d+: Operator ADD expects 3 bits on the LHS, but LHS's VARREF 'one' generates 1 bits.
%Warning-WIDTH: t/t_lint_width_bad.v:\d+: Operator ADD expects 3 bits on the RHS, but RHS's VARREF 'one' generates 1 bits.
%Error: Exiting due to.*},
    );

ok(1);
1;
