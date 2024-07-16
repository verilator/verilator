#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);
top_filename("t/t_compiler_include.v");

compile(
    make_top_shell => 0,
    make_main => 0,
    verilator_flags2 => ["--exe", "$Self->{t_dir}/t_compiler_include.cpp", "--compiler-include $Self->{t_dir}/t_compiler_include.h", "--output-split 1"],
    );

execute(
    check_finished => 1,
    );

ok(1);
1;
