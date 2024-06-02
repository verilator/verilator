#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vltmt => 1);

compile(
    verilator_flags2 => ['--cc'],
    threads => 4,
    context_threads => 2
    );

execute(
    fails => 1
    );

file_grep($Self->{run_log_filename}, qr/%Error: .*\/verilated\.cpp:\d+: VerilatedContext has 2 threads but model 'Vt_threads_crazy' \(instantiated as 'top'\) was Verilated with --threads 4\./);
ok(1);
1;
