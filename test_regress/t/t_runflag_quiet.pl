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

compile(
    verilator_flags2 => ["--binary --quiet"],
    );

execute(
    all_run_flags => ["+verilator+quiet"],
    logfile => "$Self->{obj_dir}/sim__quiet.log",
    );

file_grep_not("$Self->{obj_dir}/sim__quiet.log", qr/S i m u l a t/i,);

#---

execute(
    all_run_flags => [""],
    logfile => "$Self->{obj_dir}/sim__noquiet.log",
    );

file_grep("$Self->{obj_dir}/sim__noquiet.log", qr/S i m u l a t/i,);

ok(1);

1;
