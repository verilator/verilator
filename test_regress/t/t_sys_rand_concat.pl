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
    );

execute(
    check_finished => 1,
    );

file_grep_not(glob_one("$Self->{obj_dir}/Vt_sys_rand_concat___024root__DepSet_*__0__Slow.cpp"), qr/(<<|>>)/x);

ok(1);
1;
