#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

top_filename("t/t_gen_missing.v");

$Self->{vlt} or $Self->skip("Verilator only test");
compile (
    v_flags2 => ['+define+T_GEN_MISSING_BAD'],
    fails => 1,
    expect=>
'%Error: t/t_gen_missing.v:\d+: Cannot find file containing module: foo_not_needed
%Error: t/t_gen_missing.v:\d+: Looked in:
%Error: t/t_gen_missing.v:\d+:       t/foo_not_needed
%Error: t/t_gen_missing.v:\d+:       t/foo_not_needed.v
%Error: t/t_gen_missing.v:\d+:       t/foo_not_needed.sv
.*%Error: Exiting due to.*',
    );

ok(1);
1;
