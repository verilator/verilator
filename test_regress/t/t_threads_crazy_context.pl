#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt_all => 1);

if ($Self->cfg_with_m32) {
    skip("Does not work with -m32 (resource unavailable)");
}

top_filename("t/t_threads_crazy.v");

compile(
    verilator_flags2 => ['--cc'],
    threads => $Self->{vltmt} ? 2 : 0,
    context_threads => 1024
    );

execute(
    check_finished => 1,
    );

if ($Self->{vltmt}) {
    file_grep($Self->{run_log_filename}, qr/System has \d+ hardware threads but simulation thread count set to 1024\. This will likely cause significant slowdown\./);
} else {
    file_grep($Self->{run_log_filename}, qr/Verilator run-time library built without VL_THREADS\. Ignoring call to 'VerilatedContext::threads' with argument 1024\./);
}

ok(1);
1;
