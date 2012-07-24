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
'%Error: t/t_var_notfound_bad.v:\d+: Can\'t find definition of variable: nf
%Error: t/t_var_notfound_bad.v:\d+: Can\'t find definition of \'subsubz\' in dotted scope/variable: sub.subsubz
%Error:      Known scopes under \'sub\': subsub
%Error: t/t_var_notfound_bad.v:\d+: Can\'t find definition of task/function: nofunc
%Error: t/t_var_notfound_bad.v:\d+: Can\'t find definition of task/function: notask
%Error: t/t_var_notfound_bad.v:\d+: Found definition of \'a_var\' as a VAR but expected a task/function
%Error: Exiting due to.*',
	 );

ok(1);
1;
