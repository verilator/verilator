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
q{%Error: t/t_func_bad.v:\d+: Missing argument on non-defaulted argument 'from2' in function call to FUNC 'add'
%Error: t/t_func_bad.v:\d+: Too many arguments in function call to FUNC 'add'
%Error: t/t_func_bad.v:\d+: Missing argument on non-defaulted argument 'y' in function call to TASK 'x'
%Error: t/t_func_bad.v:\d+: Unsupported: Function output argument 'y' requires 1 bits, but connection's CONST '.*' generates 32 bits.
%Error: t/t_func_bad.v:\d+: No such argument 'no_such' in function call to FUNC 'f'
%Error: t/t_func_bad.v:\d+: Duplicate argument 'dup' in function call to FUNC 'f'
%Error: t/t_func_bad.v:\d+: Too many arguments in function call to FUNC 'f'
%Error: Exiting due to},
	 );

ok(1);
1;

