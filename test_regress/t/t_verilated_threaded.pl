#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vltmt => 1);

top_filename("t/t_verilated_all.v");

my $root = "..";

compile(
    # Can't use --coverage and --savable together, so cheat and compile inline
    verilator_flags2 => ["--cc --coverage-toggle --coverage-line --coverage-user --trace --vpi $root/include/verilated_save.cpp"],
    threads => 1
    );

execute(
    check_finished => 1,
    );

ok(1);
1;
