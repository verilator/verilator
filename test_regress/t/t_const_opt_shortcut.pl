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
    v_flags2 => ["t/$Self->{name}.cpp"],
    verilator_flags2 => ["-Wno-UNOPTTHREADS", "--stats"],
    );

execute(
    # Shortcut is not properly implemented yet as in https://github.com/verilator/verilator/issues/487
    # When the issue is fixed, change the following two lines.
    check_finished => 0,
    fails => $Self->{vlt_all},
    );

ok(1);
1;
