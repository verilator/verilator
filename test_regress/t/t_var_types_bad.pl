#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

$Self->{verilated_randReset} = 1;  # allow checking if we initialize vars to zero only when needed

compile (
	 fails=>1,
	 expect=>
'%Error: t/t_var_types_bad.v:\d+: Illegal bit or array select; type does not have a bit range, or bad dimension: type is bit
.*%Error: t/t_var_types_bad.v:\d+: Illegal bit or array select; type does not have a bit range, or bad dimension: type is logic
.*%Error: t/t_var_types_bad.v:\d+: Illegal bit or array select; type does not have a bit range, or bad dimension: type is logic
.*%Error: t/t_var_types_bad.v:\d+: Illegal bit or array select; type does not have a bit range, or bad dimension: type is real
.*%Error: t/t_var_types_bad.v:\d+: Illegal bit or array select; type does not have a bit range, or bad dimension: type is real
.*%Error: Exiting due to.*',
	 );

ok(1);
1;
