#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

use IO::File;

# Test for bin/verilator_gantt,
#
# Only needed in multithreaded regression.
scenarios(vltmt => 1);

# It doesn't really matter what test
# we use, so long as it runs several cycles,
# enough for the profiling to happen:
top_filename("t/t_gen_alw.v");

compile(
    # Checks below care about thread count, so use 2 (minimum reasonable)
    v_flags2 => ["--prof-threads --threads 2"]
    );

execute(
    all_run_flags => ["+verilator+prof+threads+start+2",
                      " +verilator+prof+threads+window+2",
                      " +verilator+prof+threads+file+$Self->{obj_dir}/profile_threads.dat",
                      ],
    check_finished => 1,
    );

# For now, verilator_gantt still reads from STDIN
#  (probably it should take a file, gantt.dat like verilator_profcfunc)
# The profiling data still goes direct to the runtime's STDOUT
#  (maybe that should go to a separate file - gantt.dat?)
run(cmd => ["$ENV{VERILATOR_ROOT}/bin/verilator_gantt",
            "$Self->{obj_dir}/profile_threads.dat",
            "--vcd $Self->{obj_dir}/profile_threads.vcd",
            "> $Self->{obj_dir}/gantt.log"]);

# We should have three lines of gantt chart, each with
# an even number of mtask-bars (eg "[123--]")
my $gantt_line_ct = 0;
my $global_mtask_ct = 0;
{
    my $fh = IO::File->new("<$Self->{obj_dir}/gantt.log")
        or error("$! $Self->{obj_dir}/gantt.log");
    while (my $line = ($fh && $fh->getline)) {
        if ($line !~ m/^  t:/) { next; }
        $gantt_line_ct++;
        my $this_thread_mtask_ct = 0;
        my @mtasks = split(/\[/, $line);
        shift @mtasks;  # throw the '>>  ' away
        foreach my $mtask (@mtasks) {
            # Format of each mtask is "[123--]" where the hyphens
            # number or ] may or may not appear; it depends on exact timing.
            $this_thread_mtask_ct++;
            $global_mtask_ct++;
        }
        if ($this_thread_mtask_ct % 2 != 0) { error("odd number of mtasks found"); }
    }
}
if ($gantt_line_ct != 2) { error("wrong number of gantt lines"); }
if ($global_mtask_ct == 0) { error("wrong number of mtasks, should be > 0"); }
print "Found $gantt_line_ct lines of gantt data with $global_mtask_ct mtasks\n"
    if $Self->{verbose};

# Diff to itself, just to check parsing
vcd_identical("$Self->{obj_dir}/profile_threads.vcd", "$Self->{obj_dir}/profile_threads.vcd");

ok(1);
1;
