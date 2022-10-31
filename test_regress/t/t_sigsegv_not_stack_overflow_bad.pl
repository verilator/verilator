#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2022 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

if ($^O eq "linux") {
    lint(
        v_flags => ["--debug-sigsegv"],
        fails => 1,
        sanitize => 0,
        expect => '\A(?!.*?Segmentation fault due to stack overflow.*?)' .
                  '.*' .
                  '%Error: Verilator internal fault, sorry. Suggest trying --debug --gdbbt\n' .
                  '%Error: Command Failed.*'
        );

    ok(1);
} else {
    skip("Linux only test");
}
