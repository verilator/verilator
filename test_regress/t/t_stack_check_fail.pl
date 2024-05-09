#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

top_filename("t/t_stack_check.v");

scenarios(vlt => 1);

compile(
    verilator_flags2 => ['--binary --debug-stack-check', '--CFLAGS', '"-D_VL_TEST_RLIMIT_FAIL"'],
    );

execute();

file_grep($Self->{run_log_filename}, qr/.*%Warning: System has stack size/);
ok(1);
1;
