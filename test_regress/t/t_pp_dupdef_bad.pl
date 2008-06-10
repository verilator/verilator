#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("./driver.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2008 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

top_filename("t/t_pp_dupdef.v");

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
	 ) if $Last_Self->{v3};

ok(1);
1;

