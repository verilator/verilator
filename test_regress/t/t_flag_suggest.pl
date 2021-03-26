#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2008 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

my @opts;
# Typo
push @opts, "-ccc";
# Typo of an option that starts with "--"
push @opts, "--ccc";
# Typo of an option that starts with "-no-"
push @opts, "-no-asserT";
# Typo of an option that starts with "-no"
push @opts, "-noasserT";
# Typo of an option that allows "-no"
push @opts, "-asserT";
# Typo of an option that starts with '+'
push @opts, "+definE+A=B";
# Typo that takes arg
push @opts, "-CFLAGs -ggdb";
# Typo of an undocumented option
push @opts, "-debug-aborT";
# Typo of "-Wno" for partial match
push @opts, "-Won-SPLITVAR";
# Typo after -Wno- for partial match
push @opts, "-Wno-SPLITVER";
# Typo of -language
push @opts, "-language 1364-1997";

my $cmd = "";

foreach my $var (@opts) {
    $cmd = $cmd . $ENV{VERILATOR_ROOT} . "/bin/verilator ${var}; ";
}

run(cmd => [$cmd],
    verilator_run => 1,
    logfile => "$Self->{obj_dir}/sim.log",
    fails => 1,
    expect_filename => $Self->{golden_filename},
);

ok(1);
1;
