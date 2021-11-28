#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2010 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);
if ($ENV{VERILATOR_TEST_NO_GDB}) {
    skip("Skipping due to VERILATOR_TEST_NO_GDB");
} elsif (system("gdb --version")) {
    skip("No gdb installed");
} else {
    lint(
        verilator_flags2 => ["--lint-only --debug --gdbbt --debug-sigsegv"],
        sanitize => 0,
        fails => $Self->{vlt_all},
        expect =>
'.*
Program received signal SIGSEGV, Segmentation fault.
.*in V3Options::.*
.*%Error: Command Failed.*',
        );

    ok(1);
}
1;
