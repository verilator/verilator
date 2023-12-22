#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2019 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

top_filename("t/t_assigndly_task.v");

compile(
    verilator_flags2 => ["--timing"],
    );

foreach my $file (
      glob_all("$Self->{obj_dir}/$Self->{vm_prefix}*.h"),
      glob_all("$Self->{obj_dir}/$Self->{vm_prefix}*.cpp")
    ) {
    file_grep_not($file, qr/__Vfork_/i);
}

ok(1);
1;
