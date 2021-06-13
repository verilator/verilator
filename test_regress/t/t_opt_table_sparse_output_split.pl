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

top_filename("t/t_opt_table_sparse.v");
golden_filename("t/t_opt_table_sparse.out");

compile(
    verilator_flags2 => ["--stats", "--output-split 1"],
    );

if ($Self->{vlt_all}) {
    file_grep($Self->{stats}, qr/Optimizations, Tables created\s+(\d+)/i, 1);
    file_grep($Self->{stats}, qr/ConstPool, Tables emitted\s+(\d+)/i, 2);
}

# Splitting should set VM_PARALLEL_BUILDS to 1 by default
file_grep("$Self->{obj_dir}/$Self->{VM_PREFIX}_classes.mk", qr/VM_PARALLEL_BUILDS\s*=\s*1/);

check_splits(2);

execute(
    check_finished => 1,
    expect_filename => $Self->{golden_filename},
    );

ok(1);
1;

sub check_splits {
    my $expected = shift;
    my $n;
    foreach my $file (glob("$Self->{obj_dir}/*.cpp")) {
        if ($file =~ /__ConstPool_/) {
            $n += 1;
        }
    }
    $n == $expected or error("__ConstPool*.cpp not split: $n");
}
