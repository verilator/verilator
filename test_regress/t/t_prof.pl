#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt_all => 1);

# TODO below might no longer be requried as configure checks for -pg
if ($ENV{VERILATOR_TEST_NO_GPROF}) {
    skip("Skipping due to VERILATOR_TEST_NO_GPROF");
} else {
    dotest();
}

ok(1);

sub dotest {
    compile(
        verilator_flags2 => ["--stats --prof-cfuncs"],
        );

    unlink $_ foreach (glob "$Self->{obj_dir}/gmon.out.*");
    setenv('GMON_OUT_PREFIX', "$Self->{obj_dir}/gmon.out");

    execute(
        check_finished => 1,
        );

    my $gmon_path;
    $gmon_path = $_ foreach (glob "$Self->{obj_dir}/gmon.out.*");
    $gmon_path or error("Profiler did not create a gmon.out");
    (my $gmon_base = $gmon_path) =~ s!.*[/\\]!!;

    run(cmd => ["cd $Self->{obj_dir} && gprof $Self->{VM_PREFIX} $gmon_base > gprof.out"],
        check_finished => 0);

    run(cmd => ["cd $Self->{obj_dir} && $ENV{VERILATOR_ROOT}/bin/verilator_profcfunc gprof.out > cfuncs.out"],
        check_finished => 0);

    file_grep("$Self->{obj_dir}/cfuncs.out", qr/Overall summary by/);
    file_grep("$Self->{obj_dir}/cfuncs.out", qr/VLib + VL_POWSS_QQQ/);
    file_grep("$Self->{obj_dir}/cfuncs.out", qr/VBlock + t_prof:/);
}

1;
