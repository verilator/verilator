#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

# stats will be deleted but generation will be skipped if libs of hierarchy blocks exist.
clean_objs();

top_filename("t/t_hier_block.v");

# Travis environment offers 2 VCPUs, 2 thread setting causes the following warning.
# %Warning-UNOPTTHREADS: Thread scheduler is unable to provide requested parallelism; consider asking for fewer threads.
# So use 6 threads here though it's not optimal in performace wise, but ok.
scenarios(simulator => 1);

compile(
    verilator_flags2 => ['--sc', '--stats', '--hierarchical', ($Self->{vltmt} ? ' --threads 6' : '')],
    );

execute(
    check_finished => 1,
    );

file_grep($Self->{obj_dir} . "/Vsub0/sub0.sv", /^module\s+(\S+)\s+/, "sub0");
file_grep($Self->{obj_dir} . "/Vsub1/sub1.sv", /^module\s+(\S+)\s+/, "sub1");
file_grep($Self->{obj_dir} . "/Vsub2/sub2.sv", /^module\s+(\S+)\s+/, "sub2");
file_grep($Self->{stats}, qr/HierBlock,\s+Hierarchy blocks\s+(\d+)/i, 7);

ok(1);
1;
