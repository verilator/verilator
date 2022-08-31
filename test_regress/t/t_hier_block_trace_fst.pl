#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

scenarios(vlt_all => 1);

top_filename("t/t_hier_block.v");

# CI environment offers 2 VCPUs, 2 thread setting causes the following warning.
# %Warning-UNOPTTHREADS: Thread scheduler is unable to provide requested parallelism; consider asking for fewer threads.
# So use 6 threads here though it's not optimal in performace wise, but ok.

compile(
    v_flags2 => ['t/t_hier_block.cpp'],
    verilator_flags2 => ['--hierarchical',
                         '--Wno-TIMESCALEMOD',
                         '--trace-fst',
                         '--no-trace-underscore',  # To avoid handle mismatches
    ],
    threads => $Self->{vltmt} ? 6 : 0
    );

execute(
    check_finished => 1,
    );

fst_identical($Self->trace_filename, $Self->{golden_filename});

ok(1);
1;
