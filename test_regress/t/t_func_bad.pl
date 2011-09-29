#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
	 v_flags2 => ["--lint-only"],
	 fails=>1,
	 expect=>
q{%Error: t/t_func_bad.v:\d+: Too few arguments in function call to FUNC 'add'
%Error: t/t_func_bad.v:\d+: Too few arguments in function call to FUNC 'add'
%Error: t/t_func_bad.v:\d+: Too few arguments in function call to FUNC 'add'
%Error: t/t_func_bad.v:\d+: Too many arguments in function call to FUNC 'add'
%Error: t/t_func_bad.v:\d+: Too few arguments in function call to TASK 'x'
%Error: t/t_func_bad.v:\d+: Too few arguments in function call to TASK 'x'
%Error: t/t_func_bad.v:\d+: Too few arguments in function call to TASK 'x'
%Error: Exiting due to},
	 );

ok(1);
1;

