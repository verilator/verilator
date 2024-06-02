#!/usr/bin/env perl
if (!$::Driver) { use strict; use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Multiple Model Test Module
#
# Copyright 2020-2021 by Andreas Kuster. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

compile(
    make_top_shell => 0,
    make_main => 0,
    verilator_flags2 => ["--exe $Self->{t_dir}/$Self->{name}.cpp"],
    );

execute(
    fails => 1,
    expect_filename => $Self->{golden_filename},
    );

ok(1);
1;
