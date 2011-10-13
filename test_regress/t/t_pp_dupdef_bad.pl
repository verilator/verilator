#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2008 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

top_filename("t/t_pp_dupdef.v");

$Self->{vlt} or $Self->skip("Verilator only test");

compile (
	 v_flags2 => ["--lint-only"],
	 fails=>1,
	 expect=>
'%Warning-REDEFMACRO: t/t_pp_dupdef.v:\d+: Redefining existing define: DUP, with different value: barney 
%Warning-REDEFMACRO: Use .* to disable this message.
%Warning-REDEFMACRO: t/t_pp_dupdef.v:\d+: Previous definition is here, with value: fred 
%Warning-REDEFMACRO: t/t_pp_dupdef.v:\d+: Redefining existing define: DUPP, with different value: .*
%Warning-REDEFMACRO: t/t_pp_dupdef.v:\d+: Previous definition is here, with value: .*
%Error: Exiting due to.*',
    );

ok(1);
1;

