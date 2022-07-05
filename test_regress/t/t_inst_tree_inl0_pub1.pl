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

top_filename("t/t_inst_tree.v");

my $default_vltmt_threads = $Self->get_default_vltmt_threads();
compile(
    verilator_flags2 => ['--stats', "$Self->{t_dir}/$Self->{name}.vlt"],
    # Force 3 threads even if we have fewer cores
    threads => $Self->{vltmt} ? $default_vltmt_threads : 0
    );

sub checkRelativeRefs {
    my ($mod, $expect_relative) = @_;
    my $found_relative = 0;

    foreach my $file (glob_all("$Self->{obj_dir}/V$Self->{name}_${mod}*.cpp")) {
        my $text = file_contents($file);

        if ($text =~ m/this->/ || $text =~ m/vlSelf->/) {
            $found_relative = 1;
        }

        if ($found_relative != $expect_relative) {
            error("$file "
                  . ($found_relative ? "has" : "does not have")
                  . " relative variable references.");
        }
    }
}

if ($Self->{vlt_all}) {
    # We expect to combine sequent functions across multiple instances of
    # l2, l3, l4, l5. If this number drops, please confirm this has not broken.
    file_grep($Self->{stats}, qr/Optimizations, Combined CFuncs\s+(\d+)/i,
              ($Self->{vltmt} ? 84 : 52));

    # Everything should use relative references
    checkRelativeRefs("t", 1);
    checkRelativeRefs("l1", 1);
    checkRelativeRefs("l2", 1);
    checkRelativeRefs("l3", 1);
    checkRelativeRefs("l4", 1);
    checkRelativeRefs("l5__P1", 1);
    checkRelativeRefs("l5__P2", 1);
}

execute(
    check_finished => 1,
    expect =>
'\] (%m|.*t\.ps): Clocked
',
    );

ok(1);
1;
