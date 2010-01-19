#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
	 fails=>$Self->{v3},
	 nc=>0,  # Need to get it not to give the prompt
	 expect=>
q{%Error: t/t_mem_multi_ref_bad.v:\d+: Illegal bit or array select; variable already selected, or bad dimension: dimn
.*%Error: t/t_mem_multi_ref_bad.v:\d+: Illegal range select; variable already selected, or bad dimension
.*%Error: t/t_mem_multi_ref_bad.v:\d+: Illegal bit or array select; variable already selected, or bad dimension: dim0
.*%Error: t/t_mem_multi_ref_bad.v:\d+: Illegal bit or array select; variable already selected, or bad dimension
.*%Error: t/t_mem_multi_ref_bad.v:\d+: Illegal bit or array select; variable already selected, or bad dimension: dim1
.*%Error: t/t_mem_multi_ref_bad.v:\d+: Illegal bit or array select; variable already selected, or bad dimension
.*%Error: t/t_mem_multi_ref_bad.v:\d+: Illegal \+: or -: select; variable already selected, or bad dimension
.*%Error: t/t_mem_multi_ref_bad.v:\d+: Illegal bit or array select; variable already selected, or bad dimension: dim0nv
.*%Error: t/t_mem_multi_ref_bad.v:\d+: Illegal bit or array select; variable already selected, or bad dimension
.*%Error: Exiting due to.*},
	 );

ok(1);
1;
