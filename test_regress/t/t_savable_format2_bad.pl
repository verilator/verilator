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

top_filename("t/t_savable.v");

compile(
    v_flags2 => ["--savable"],
    save_time => 500,
    );

execute(
    check_finished => 0,
    all_run_flags => ['+save_time=500'],
    );

-r "$Self->{obj_dir}/saved.vltsv" or error("Saved.vltsv not created\n");

# Break the header
file_sed("$Self->{obj_dir}/saved.vltsv",
         "$Self->{obj_dir}/saved.vltsv",
         sub { s/verilatorsave/verilatorsavBAD/g; });

execute(
    all_run_flags => ['+save_restore=1'],
    fails => 1,
    expect_filename => $Self->{golden_filename},
    );

ok(1);
1;
