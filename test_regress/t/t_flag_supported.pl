#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2008 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

if ($Self->have_coroutines) {
    run(
        cmd => ["$ENV{VERILATOR_ROOT}/bin/verilator --get-supported COROUTINES"],
        expect => '1
',
        logfile => "$Self->{obj_dir}/vlt_coroutines.log",
        verilator_run => 1,
        );
}

if ($Self->have_sc) {
    run(
        cmd => ["$ENV{VERILATOR_ROOT}/bin/verilator --get-supported SYSTEMC"],
        expect => '1
',
        logfile => "$Self->{obj_dir}/vlt_systemc.log",
        verilator_run => 1,
        );
}

run(
    cmd => ["$ENV{VERILATOR_ROOT}/bin/verilator --get-supported DOES_NOT_EXIST"],
    expect => '',
    logfile => "$Self->{obj_dir}/vlt_does_not_exist.log",
    verilator_run => 1,
    );


ok(1);
1;
