#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2017 by Todd Strader. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
#
compile (
	 v_flags2 => ["--lint-only"],
	 fails=>1,
	 expect=>
q{%Warning-USERFATAL: f_add = 15
%Warning-USERFATAL: Use "/* verilator lint_off USERFATAL */" and lint_on around source to disable this message.
%Error: t/t_func_const_packed_array_bad.v:11: Expecting expression to be constant, but can't determine constant for FUNCREF 'f_add2'
%Error: t/t_func_const_packed_array_bad.v:22: ... Location of non-constant STOP: $stop executed during function constification; maybe indicates assertion firing
Called from:
t/t_func_const_packed_array_bad.v:30:  f_add() with parameters:
    params = [0 = 32'h7, 1 = 32'h8]
Called from:
t/t_func_const_packed_array_bad.v:11:  f_add2() with parameters:
    a = ?32?sh7
    b = ?32?sh8
    c = ?32?sh9
},
	 );

ok(1);
1;
