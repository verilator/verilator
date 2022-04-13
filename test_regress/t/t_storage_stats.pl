#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

my $out_filename = "$Self->{obj_dir}/$Self->{VM_PREFIX}__stats.txt";

compile(
    verilator_flags2 => ["--stats"],
    );

file_grep("$out_filename", qr/RAMs, count \s+ 2/);
file_grep("$out_filename", qr/RAMs, total bits \s+ 72192/);
file_grep("$out_filename", qr/Registers, count \s+ 8/);
file_grep("$out_filename", qr/Registers, total bits \s+ 144440/);

ok(1);
1;
