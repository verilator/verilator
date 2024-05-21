#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

compile(
    verilator_flags2 => ["--x-initial unique"],
    );

execute(
    all_run_flags => ["+verilator+rand+reset+1"],
    check_finished => 1,
    );

files_identical("$Self->{obj_dir}/t_sys_readmem_4state_b.mem", "t/t_sys_readmem_4state_b.out");
files_identical("$Self->{obj_dir}/t_sys_readmem_4state_h.mem", "t/t_sys_readmem_4state_h.out");

ok(1);
1;
