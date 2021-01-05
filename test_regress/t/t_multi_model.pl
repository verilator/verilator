#!/usr/bin/env perl
if (!$::Driver) {
    use strict;
    use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
#
# DESCRIPTION: Verilator: Verilog Multiple Model Test Module
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2020 by Andreas Kuster.
# SPDX-License-Identifier: CC0-1.0
#

scenarios(vlt_all => 1);

compile(
    make_top_shell => 0,
    make_main => 0,
    verilator_flags2 => ["-threads 1 --exe $Self->{t_dir}/$Self->{name}.cpp --trace --coverage -cc"] # link threads library, add custom .cpp code, add tracing & coverage support
);

execute(
    check_finished => 1,
);

ok(1);
1;
