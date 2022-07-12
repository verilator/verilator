#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

# Test for bin/verilator_gantt,

scenarios(vlt_all => 1);

# It doesn't really matter what test
# we use, so long as it runs several cycles,
# enough for the profiling to happen:
top_filename("t/t_gen_alw.v");

compile(
    make_top_shell => 0,
    make_main => 0,
    v_flags2 => ["--prof-exec --exe $Self->{t_dir}/$Self->{name}.cpp"],
    # Checks below care about thread count, so use 2 (minimum reasonable)
    threads => $Self->{vltmt} ? 2 : 0,
    make_flags => 'CPPFLAGS_ADD=-DVL_NO_LEGACY',
    );

execute(
    all_run_flags => ["+verilator+prof+exec+start+4",
                      " +verilator+prof+exec+window+4",
                      " +verilator+prof+exec+file+$Self->{obj_dir}/profile_exec.dat",
                      " +verilator+prof+vlt+file+$Self->{obj_dir}/profile.vlt",
                      ],
    check_finished => 1,
    );

# For now, verilator_gantt still reads from STDIN
#  (probably it should take a file, gantt.dat like verilator_profcfunc)
# The profiling data still goes direct to the runtime's STDOUT
#  (maybe that should go to a separate file - gantt.dat?)
run(cmd => ["$ENV{VERILATOR_ROOT}/bin/verilator_gantt",
            "$Self->{obj_dir}/profile_exec.dat",
            "--vcd $Self->{obj_dir}/profile_exec.vcd",
            "| tee $Self->{obj_dir}/gantt.log"],
    );

if ($Self->{vltmt}) {
    file_grep("$Self->{obj_dir}/gantt.log", qr/Total threads += 2/i);
    file_grep("$Self->{obj_dir}/gantt.log", qr/Total mtasks += 7/i);
} else {
    file_grep("$Self->{obj_dir}/gantt.log", qr/Total threads += 1/i);
    file_grep("$Self->{obj_dir}/gantt.log", qr/Total mtasks += 0/i);
}
file_grep("$Self->{obj_dir}/gantt.log", qr/Total evals += 4/i);

# Diff to itself, just to check parsing
vcd_identical("$Self->{obj_dir}/profile_exec.vcd", "$Self->{obj_dir}/profile_exec.vcd");

ok(1);
1;
