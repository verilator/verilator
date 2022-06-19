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

compile(
    verilator_flags2 => ['--assert']
    );

execute(
    check_finished => 1,
    );

# We expect all loops should be unrolled by verilator,
# none of the loop variables should exist in the output:
for my $file (glob_all("$Self->{obj_dir}/$Self->{VM_PREFIX}*.cpp")) {
    file_grep_not($file, qr/index_/);
}

# Further, we expect that all logic within the loop should
# have been evaluated inside the compiler. So there should be
# no references to 'sum' in the .cpp.
for my $file (glob_all("$Self->{obj_dir}/$Self->{VM_PREFIX}*.cpp")) {
    file_grep_not($file, qr/[^a-zA-Z]sum[^a-zA-Z]/);
}

ok(1);
1;
