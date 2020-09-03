#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

# If a test fails, broken .cmake may distrub the next run
clean_objs();

scenarios(simulator => 1);
top_filename("t/t_hier_block.v");

# Travis environment offers 2 VCPUs, 2 thread setting causes the following warning.
# %Warning-UNOPTTHREADS: Thread scheduler is unable to provide requested parallelism; consider asking for fewer threads.
# So use 6 threads here though it's not optimal in performace wise, but ok.
compile(
    verilator_make_gmake => 0,
    verilator_make_cmake => 1,
    v_flags2 => ['t/t_hier_block.cpp'],
    verilator_flags2 => ['--stats',
                         '--hierarchical',
                         '--CFLAGS', "'-pipe -DCPP_MACRO=cplusplus '",
                         '--make cmake',
                         ($Self->{vltmt} ? ' --threads 6' : '')],
    );

if (!$Self->have_cmake) {
    skip("cmake is not installed");
} else {
    my $cmakecache = $Self->{obj_dir}."/CMakeCache.txt";
    if (! -e $cmakecache) {
        error("$cmakecache does not exist.")
    }

    execute(
        check_finished => 1,
        );

file_grep($Self->{obj_dir} . "/Vsub0/sub0.sv", /^module\s+(\S+)\s+/, "sub0");
file_grep($Self->{obj_dir} . "/Vsub1/sub1.sv", /^module\s+(\S+)\s+/, "sub1");
file_grep($Self->{obj_dir} . "/Vsub2/sub2.sv", /^module\s+(\S+)\s+/, "sub2");
file_grep($Self->{obj_dir} . '/Vt_hier_block_cmake__stats.txt', qr/HierBlock,\s+Hierarchical blocks\s+(\d+)/i, 10);
file_grep($Self->{run_log_filename}, qr/MACRO:(\S+) is defined/i, "cplusplus");

}

ok(1);
1;
