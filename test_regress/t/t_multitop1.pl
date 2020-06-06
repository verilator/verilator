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

compile(
    );

execute(
    check_finished => 0,
    );

# Order of lines is unspecified, so don't use a golden file
file_grep($Self->{run_log_filename}, qr!In 'top.t'!);
file_grep($Self->{run_log_filename}, qr!In 'top.t.s'!);
file_grep_not($Self->{run_log_filename}, qr!in_subfile!);

ok(1);
1;
