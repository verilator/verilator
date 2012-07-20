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
'%Error: t/t_var_bad_sameas.v:\d+: Unsupported in C: Cell has the same name as variable: varfirst
%Error: t/t_var_bad_sameas.v:\d+: ... Location of original declaration
%Error: t/t_var_bad_sameas.v:\d+: Unsupported in C: Task has the same name as (variable|cell): varfirst
%Error: t/t_var_bad_sameas.v:\d+: ... Location of original declaration
%Error: t/t_var_bad_sameas.v:\d+: Unsupported in C: Variable has same name as cell: cellfirst
%Error: t/t_var_bad_sameas.v:\d+: Unsupported in C: Task has the same name as cell: cellfirst
%Error: t/t_var_bad_sameas.v:\d+: ... Location of original declaration
%Error: t/t_var_bad_sameas.v:\d+: Unsupported in C: Variable has same name as task: taskfirst
%Error: t/t_var_bad_sameas.v:\d+: Unsupported in C: Cell has the same name as task: taskfirst
%Error: t/t_var_bad_sameas.v:\d+: ... Location of original declaration
%Error: Exiting due to.*',
	 );

ok(1);
1;
