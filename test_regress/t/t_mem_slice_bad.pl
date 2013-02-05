#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2010 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

$Self->{vlt} or $Self->skip("Verilator only test");

compile (
	 v_flags2 => ["--lint-only"],
	 fails=>1,
	 expect=>
'%Error: t/t_mem_slice_bad.v:\d+: Slices of arrays in assignments must have the same unpacked dimensions
%Error: t/t_mem_slice_bad.v:\d+: Slices of arrays in assignments must have the same unpacked dimensions
%Error: t/t_mem_slice_bad.v:\d+: Unsupported: Slices in a non-delayed assignment with the same Var on both sides
%Error: t/t_mem_slice_bad.v:\d+: Slices of arrays in assignments must have the same unpacked dimensions
%Error: t/t_mem_slice_bad.v:\d+: Slices of arrays in assignments must have the same unpacked dimensions
%Error: Exiting due to.*',
    );

ok(1);
1;
