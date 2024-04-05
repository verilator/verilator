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

compile(
    verilator_flags2 => ['--quiet-stats'],
    verilator_make_gcc => 0,
    logfile => $Self->{run_log_filename},
    );

file_grep_not($Self->{obj_dir}.'/vlt_compile.log', qr/V e r i l a t/i,);

ok(1);
1;
