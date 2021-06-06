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

unlink("$Self->{obj_dir}/t_sys_file_basic_mcd.log");

compile();
execute(
    check_finished => 1,
    expect_filename => $Self->{golden_filename},
    );

files_identical("$Self->{obj_dir}/t_sys_file_basic_mcd_test2_0.dat",
                "$Self->{t_dir}/t_sys_file_basic_mcd_test2_0.dat");
files_identical("$Self->{obj_dir}/t_sys_file_basic_mcd_test2_1.dat",
                "$Self->{t_dir}/t_sys_file_basic_mcd_test2_1.dat");
files_identical("$Self->{obj_dir}/t_sys_file_basic_mcd_test2_2.dat",
                "$Self->{t_dir}/t_sys_file_basic_mcd_test2_2.dat");
files_identical("$Self->{obj_dir}/t_sys_file_basic_mcd_test5.dat",
                "$Self->{t_dir}/t_sys_file_basic_mcd_test5.dat");

ok(1);
1;
