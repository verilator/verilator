#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

top_filename("t/t_unopt_combo.v");

compile (
	 fails=>$Self->{v3},
	 expect=>
'%Warning-UNOPTFLAT: t/t_unopt_combo.v:\d+: Signal unoptimizable: Feedback to clock or circular logic: TOP->v.c
%Warning-UNOPTFLAT: Use "/\* verilator lint_off UNOPTFLAT \*/" and lint_on around source to disable this message.
%Warning-UNOPTFLAT:      Example path: t/t_unopt_combo.v:\d+:  TOP->v.c
%Warning-UNOPTFLAT:      Example path: t/t_unopt_combo.v:\d+:  ALWAYS
%Warning-UNOPTFLAT:      Example path: t/t_unopt_combo.v:\d+:  TOP->v.b
%Warning-UNOPTFLAT:      Example path: t/t_unopt_combo.v:\d+:  ALWAYS
%Warning-UNOPTFLAT:      Example path: t/t_unopt_combo.v:\d+:  TOP->v.c
%Error: Exiting due to '
	 );

execute (
     ) if !$Self->{v3};

ok(1);
1;
