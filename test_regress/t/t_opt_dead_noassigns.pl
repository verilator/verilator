#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2020 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

compile(
    verilator_flags2 => ['--fno-dead-assigns'],
    );

execute(
    check_finished => 1,
    );

my @files = glob_all("$Self->{obj_dir}/$Self->{vm_prefix}_*.cpp");
file_grep_any(\@files, qr/keptdead/ix);

ok(1);
1;
