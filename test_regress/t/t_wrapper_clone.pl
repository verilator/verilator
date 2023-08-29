#!/usr/bin/env perl
if (!$::Driver) { use strict; use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Multiple Model Test Module
#
# This file ONLY is placed into the Public Domain, for any use,
# without warranty, 2023 by Yinan Xu.
# SPDX-License-Identifier: CC0-1.0

scenarios(vlt_all => 1);

compile(
    make_top_shell => 0,
    make_main => 0,
    # link threads library, add custom .cpp code, add tracing & coverage support
    verilator_flags2 => ["--exe $Self->{t_dir}/$Self->{name}.cpp",
                         "-cc"],
    threads => 1,
    );

execute(
    check_finished => 1,
    expect_filename => $Self->{golden_filename},
    );

ok(1);
1;
