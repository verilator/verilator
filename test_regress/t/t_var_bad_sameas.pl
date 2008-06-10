#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

compile (
	 fails=>1,
	 expect=>
'%Error: t/t_var_bad_sameas.v:\d+: Unsupported in C: Cell has same name as variable: varfirst
%Error: t/t_var_bad_sameas.v:\d+: Unsupported in C: Task/function has same name as variable: varfirst
%Error: t/t_var_bad_sameas.v:\d+: Unsupported in C: Variable has same name as cell: cellfirst
%Error: t/t_var_bad_sameas.v:\d+: Unsupported in C: Task/function has same name as cell: cellfirst
%Error: t/t_var_bad_sameas.v:\d+: Unsupported in C: Variable has same name as task: taskfirst
%Error: t/t_var_bad_sameas.v:\d+: Unsupported in C: Cell has same name as task: taskfirst
%Error: Exiting due to.*',
	 );

ok(1);
1;
