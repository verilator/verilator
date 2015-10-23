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
'%Error: t/t_interface_array_bad.v:\d+: Expecting expression to be constant, but variable isn\'t const: bar
%Error: t/t_interface_array_bad.v:\d+: Could not expand constant selection inside dotted reference: bar
%Error: t/t_interface_array_bad.v:\d+: Can\'t find definition of \'a\' in dotted signal: .a
%Error:      Known scopes under \'a\':.*
%Error: Exiting due to.*',
    );

ok(1);
1;
