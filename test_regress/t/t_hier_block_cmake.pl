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

if (!$Self->have_cmake) {
    $Self->skip("Test requires CMake; ignore error since not available or version too old\n");
} else {
    run(logfile => "$Self->{obj_dir}/cmake.log",
        cmd => ['cd "' . $Self->{obj_dir} . '" && cmake ' . $Self->{t_dir} . '/t_hier_block_cmake',
            "-DCMAKE_PREFIX_PATH=$ENV{VERILATOR_ROOT}",
            ($Self->{vltmt} ? '-DTEST_THREADS=6' : '')
        ]);

    run(logfile => "$Self->{obj_dir}/build.log",
        cmd => ['cd "' . $Self->{obj_dir} . '" && cmake --build', '.']
    );

    run(logfile => "$Self->{obj_dir}/run.log",
        cmd => ['cd "' . $Self->{obj_dir} . '" && ./t_hier_block_cmake', '.']
    );
    my $target_dir = $Self->{obj_dir} . '/CMakeFiles/t_hier_block_cmake.dir/Vt_hier_block.dir/';
    file_grep($target_dir . 'Vsub0/sub0.sv', /^module\s+(\S+)\s+/, "sub0");
    file_grep($target_dir . 'Vsub1/sub1.sv', /^module\s+(\S+)\s+/, "sub1");
    file_grep($target_dir . 'Vsub2/sub2.sv', /^module\s+(\S+)\s+/, "sub2");
    file_grep($target_dir . 'Vt_hier_block__stats.txt', qr/HierBlock,\s+Hierarchical blocks\s+(\d+)/i, 13);
    file_grep($Self->{obj_dir} . '/run.log', qr/MACRO:(\S+) is defined/i, "cplusplus");
}

ok(1);
1;
