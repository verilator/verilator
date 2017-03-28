#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
	fails=>1,
	expect=>
q{%Error: t/t_interface_param_another_bad.v:\d+: Parameter-resolved constants must not use dotted references: dummy
%Error: Exiting due to.*},
    );

ok(1);
1;
