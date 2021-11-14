#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2021 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

if (!$Self->cfg_with_ccache) {
    skip("Requires configuring with ccache");
}

top_filename("t_a1_first_cc.v");

# This test requires rebuilding the object files to check the ccache log
foreach my $filename (glob("$Self->{obj_dir}/*.o")) {
    print "rm $filename\n" if $Self->{verbose};
    unlink $filename;
}

compile(
    verilator_flags2 => ['--trace'],
    make_flags => "ccache-report"
    );

my $report = "$Self->{obj_dir}/$Self->{VM_PREFIX}__ccache_report.txt";

# We do not actually want to make this test depend on whether the file was
# cached or not, so trim the report to ignore actual caching behaviour
run(cmd => ["sed", "-i", "-e", "'s/ : .*/ : IGNORED/; /|/s/.*/IGNORED/;'", $report]);
files_identical($report, "t/$Self->{name}__ccache_report_initial.out");

# Now rebuild again (should be all up to date)
run(
    logfile => "$Self->{obj_dir}/rebuild.log",
    cmd => ["make", "-C", $Self->{obj_dir},
                    "-f", "$Self->{VM_PREFIX}.mk",
                    $Self->{VM_PREFIX}, "ccache-report"]
    );

files_identical($report, "t/$Self->{name}__ccache_report_rebuild.out");

ok(1);
1;
