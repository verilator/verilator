#!/usr/bin/perl
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
    v_flags2 => ["--savable"],
    save_time => 500,
    );

execute(
    check_finished => 0,
    all_run_flags => ['+save_time=500'],
    );

-r "$Self->{obj_dir}/saved.vltsv" or error("Saved.vltsv not created\n");

execute(
    all_run_flags => ['+save_restore=1'],
    check_finished => 1,
    );

ok(1);
1;
