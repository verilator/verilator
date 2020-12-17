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

compile(
    v_flags2 => ["t/$Self->{name}_c.cpp"],
    verilator_flags2 => ['--vpi'],
    );

execute(
    fails => 1,
    );

file_grep($Self->{run_log_filename}, qr/vpi_release_handle.*called on same object twice/i);

ok(1);

1;
