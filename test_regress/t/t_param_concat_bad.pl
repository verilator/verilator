#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

top_filename("t/t_param_concat.v");

compile (
	 fails=>1,
	 expect=>
'%Warning-WIDTHCONCAT: t/t_param_concat.v:\d+: Unsized numbers/parameters not allowed in concatenations.
%Warning-WIDTHCONCAT: Use "/\* verilator lint_off WIDTHCONCAT \*/" and lint_on around source to disable this message.
%Warning-WIDTHCONCAT: t/t_param_concat.v:\d+: Unsized numbers/parameters not allowed in replications.
.*%Error: Exiting due to.*',
	 );

ok(1);
1;
