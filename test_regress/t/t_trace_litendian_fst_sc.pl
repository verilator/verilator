#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2020 by Geza Lore. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

if (!$Self->have_sc) {
    skip("No SystemC installed");
}
else {
    top_filename("t/t_trace_litendian.v");

    # CI environment offers 2 VCPUs, 2 thread setting causes the following warning.
    # %Warning-UNOPTTHREADS: Thread scheduler is unable to provide requested parallelism; consider asking for fewer threads.
    # Strangely, asking for more threads makes it go away.
    compile(
        verilator_flags2 => ['--sc --trace-fst --trace-params -Wno-LITENDIAN'],
        threads => $Self->{vltmt} ? 6 : 0
        );

    execute(
        check_finished => 1,
        );

    fst_identical("$Self->{obj_dir}/simx.fst", $Self->{golden_filename});
}

ok(1);
1;
