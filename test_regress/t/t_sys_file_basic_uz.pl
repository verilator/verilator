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

unlink("$Self->{obj_dir}/t_sys_file_basic_uz_test.log");

compile();

execute(
    check_finished => 1,
    );

files_identical("$Self->{obj_dir}/t_sys_file_basic_uz_test.log", $Self->{golden_filename});

files_identical("$Self->{obj_dir}/t_sys_file_basic_uz_test.bin",
                "$Self->{t_dir}/t_sys_file_basic_uz.dat");

ok(1);
1;
