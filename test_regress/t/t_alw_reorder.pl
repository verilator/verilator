#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt_all => 1);

compile(
    verilator_flags2 => ["--stats"],
    );

file_grep($Self->{stats}, qr/Optimizations, Split always\s+(\d+)/i, 0);
# Important: if reorder succeeded, we should see no dly vars.
# Equally important: twin test t_alw_noreorder should see dly vars,
#  is identical to this test except for disabling the reorder step.
foreach my $file ("$Self->{obj_dir}/$Self->{VM_PREFIX}.cpp",
                  "$Self->{obj_dir}/$Self->{VM_PREFIX}.h") {
    file_grep_not($file, qr/dly__t__DOT__v1/i);
    file_grep_not($file, qr/dly__t__DOT__v2/i);
    file_grep_not($file, qr/dly__t__DOT__v3/i);
}

execute(
    check_finished=>1,
    );

ok(1);
1;
