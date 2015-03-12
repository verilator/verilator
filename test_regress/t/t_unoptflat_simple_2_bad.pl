#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

top_filename("t/t_unoptflat_simple_2.v");

# Compile only
compile (
    verilator_flags3 => [],
    verilator_flags2 => ["--report-unoptflat"],
    fails => 1,
    expect=>
'.*%Warning-UNOPTFLAT:      Widest candidate vars to split:
%Warning-UNOPTFLAT:           t/t_unoptflat_simple_2.v:\d+:  v.x, width 3, fanout \d+
.*%Error: Exiting due to ',
    );


ok(1);
1;
