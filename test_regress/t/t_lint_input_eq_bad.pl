#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2008 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

scenarios(vlt => 1);

lint(
    fails => 1,
    expect =>
'%Error: t/t_lint_input_eq_bad.v:\d+: Unsupported: Default value on module input: i2
%Error: Exiting due to.*',
    );

ok(1);
1;
