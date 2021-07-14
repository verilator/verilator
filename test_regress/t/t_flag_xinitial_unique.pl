#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt_all => 1);

compile(
    verilator_flags2 => ["--x-initial unique"],
    );

execute(
    check_finished => 1,
    );

file_grep(glob_one("$Self->{obj_dir}/$Self->{VM_PREFIX}___024root__DepSet_*__0__Slow.cpp"), qr/VL_RAND_RESET/);

ok(1);
1;
