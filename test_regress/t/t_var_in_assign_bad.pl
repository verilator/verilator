#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2005 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

$Self->{vlt} or $Self->skip("Verilator only test");

compile (
	 v_flags2 => ["--lint-only --Mdir obj_lint_only"],
	 fails=>1,
	 expect=>
'%Error-ASSIGNIN: t/t_var_in_assign_bad.v:\d+: Assigning to input variable: value
%Error-ASSIGNIN: t/t_var_in_assign_bad.v:\d+: Assigning to input variable: valueSub
%Error: Exiting due to.*',
    );

(!-d "obj_lint_only") or $Self->error("%Error: lint-only shouldn't make output directory");
ok(1);
1;
