#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

# Travis environment offers 2 VCPUs, 2 thread setting causes the following warning.
# %Warning-UNOPTTHREADS: Thread scheduler is unable to provide requested parallelism; consider asking for fewer threads.
# So use 6 threads here though it's not optimal in performace wise, but ok.
compile(
    verilator_flags2 => ['--stats' . ($Self->{vltmt} ? ' --threads 6' : '')],
    );

execute(
    check_finished => 1,
    );

file_grep($Self->{stats}, qr/SplitVar,\s+Split packed variables\s+(\d+)/i, 13);
file_grep($Self->{stats}, qr/SplitVar,\s+Split unpacked arrays\s+(\d+)/i, 23);
ok(1);
1;
