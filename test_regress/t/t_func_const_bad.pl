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
q{%Error: t/t_func_const_bad.v:\d+: Expecting expression to be constant, but can't determine constant for FUNCREF 'f_bad_output'
%Error: t/t_func_const_bad.v:\d+: ... Location of non-constant VAR 'o': Language violation: Outputs not allowed in constant functions
%Error: t/t_func_const_bad.v:\d+: Expecting expression to be constant, but can't determine constant for FUNCREF 'f_bad_dotted'
%Error: t/t_func_const_bad.v:\d+: ... Location of non-constant VARXREF 'EIGHT': Language violation: Dotted hierarchical references not allowed in constant functions
%Error: t/t_func_const_bad.v:\d+: Expecting expression to be constant, but can't determine constant for FUNCREF 'f_bad_nonparam'
%Error: t/t_func_const_bad.v:\d+: ... Location of non-constant VARREF 'modvar': Language violation: reference to non-function-local variable
%Error: t/t_func_const_bad.v:\d+: Expecting expression to be constant, but can't determine constant for FUNCREF 'f_bad_infinite'
%Error: t/t_func_const_bad.v:\d+: ... Location of non-constant WHILE: Loop unrolling took too long; probably this is an infinite loop, or set --unroll-count above 1024
%Error: t/t_func_const_bad.v:\d+: Expecting expression to be constant, but can't determine constant for FUNCREF 'f_bad_stop'
%Error: t/t_func_const_bad.v:\d+: ... Location of non-constant STOP: .stop executed during function constification; maybe indicates assertion firing
%Error: Exiting due to.*},
	 );

ok(1);
1;
