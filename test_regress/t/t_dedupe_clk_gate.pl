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

my $out_filename = "$Self->{obj_dir}/V$Self->{name}.tree.json";

compile(
    verilator_flags2 => ["--no-json-edit-nums", "--stats"],
    );

if ($Self->{vlt_all}) {
    files_identical($out_filename, $Self->{golden_filename});
    file_grep($Self->{stats}, qr/Optimizations, Gate sigs deduped\s+(\d+)/i, 4);
}

ok(1);
1;
