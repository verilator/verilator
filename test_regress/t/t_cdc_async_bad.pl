#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2009 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
	 v_flags => ['--cdc'],
	 verilator_make_gcc => 0,
	 fails => 1,
	 expect=>
'%Warning-CDCRSTLOGIC: t/t_cdc_async_bad.v:\d+: Logic in path that feeds async reset, via signal: v.rst2_bad_n
%Warning-CDCRSTLOGIC: Use "/\* verilator lint_off CDCRSTLOGIC \*/" and lint_on around source to disable this message.
%Warning-CDCRSTLOGIC:      See details in obj_dir/t_cdc_async_bad/Vt_cdc_async_bad__cdc.txt
%Warning-CDCRSTLOGIC: t/t_cdc_async_bad.v:\d+: Logic in path that feeds async reset, via signal: v.rst6a_bad_n
%Warning-CDCRSTLOGIC: t/t_cdc_async_bad.v:\d+: Logic in path that feeds async reset, via signal: v.rst6b_bad_n
%Error: Exiting due to.*',
	 );

file_grep ("$Self->{obj_dir}/V$Self->{name}__cdc.txt", qr/CDC Report/);

ok(1);
1;
