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

top_filename("t/t_prof.v");

# TODO below might no longer be required as configure checks for -pg
if ($ENV{VERILATOR_TEST_NO_GPROF}) {
    skip("Skipping due to VERILATOR_TEST_NO_GPROF");
} elsif (!$Self->have_coroutines) {
    skip("No coroutine support");
} else {
    dotest();
}

ok(1);

sub dotest {
    compile(
        verilator_flags2 => ["--stats --prof-cfuncs --binary"],
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

    run(cmd => ["cd $Self->{obj_dir} && gprof $Self->{vm_prefix} $gmon_base > gprof.log"],
        check_finished => 0);

    run(cmd => ["cd $Self->{obj_dir} && $ENV{VERILATOR_ROOT}/bin/verilator_profcfunc gprof.log > profcfuncs.log"],
        check_finished => 0);

    file_grep("$Self->{obj_dir}/profcfuncs.log", qr/Overall summary by/);
#   Appears that GCC 11.4 has a bug whereby it doesn't trace function calls
#   within coroutines; CLang seems to work correctly.
#   file_grep("$Self->{obj_dir}/profcfuncs.log", qr/VLib + VL_POWSS_QQQ/);
    file_grep("$Self->{obj_dir}/profcfuncs.log", qr/VLib + VL_WRITEF/);
    file_grep("$Self->{obj_dir}/profcfuncs.log", qr/VBlock + t_prof:/);
}

1;
