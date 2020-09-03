#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

# This test runs the very first time we've executed Verilator --sc
# after building so we make sure to run with --gdbbt, so if it dumps we'll
# get a trace.

scenarios(simulator => 1);

top_filename("t/t_a1_first_cc.v");

$DEBUG_QUIET = "--debug --debugi 0 --gdbbt --no-dump-tree";

compile(
    verilator_flags2 => [$DEBUG_QUIET, "-sc --trace"],
    );

execute(
    check_finished => 1,
    );

ok(1);
1;
