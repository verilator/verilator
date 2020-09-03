#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

top_filename("t/t_bench_mux4k.v");

compile(
    v_flags2 => ["--stats",
                 $Self->wno_unopthreads_for_few_cores()]
    );

if (`numactl --show` !~ /cpu/) {
    skip("No numactl available");
} else {
    execute(
        run_env => 'numactl -m 0 -C 0,0,0,0,0,0,0,0',
        check_finished => 1,
        );
    ok(1);
}

1;
