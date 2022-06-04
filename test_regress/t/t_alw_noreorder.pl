#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt_all => 1);

top_filename("t/t_alw_reorder.v");
compile(
    verilator_flags2 => ["--stats -fno-reorder"],
    );

file_grep($Self->{stats}, qr/Optimizations, Split always\s+(\d+)/i, 0);
# Here we should see some dly vars since reorder is disabled.
# (Whereas our twin test, t_alw_reorder, should see no dly vars
#  since it enables the reorder step.)
my @files = glob_all("$Self->{obj_dir}/$Self->{VM_PREFIX}___024root*.cpp");
file_grep_any(\@files, qr/dly__t__DOT__v1/i);
file_grep_any(\@files, qr/dly__t__DOT__v2/i);

execute(
    check_finished => 1,
    );

ok(1);
1;
