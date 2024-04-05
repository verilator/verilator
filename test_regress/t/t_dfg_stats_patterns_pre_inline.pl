#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

top_filename("t/t_dfg_stats_patterns.v");

compile(
    verilator_flags2 => ["--stats --no-skip-identical -fno-dfg-post-inline"],
    );

my $f = glob_one("$Self->{obj_dir}/$Self->{vm_prefix}__stats_dfg_patterns*");
files_identical($f, $Self->{golden_filename});

ok(1);
1;
