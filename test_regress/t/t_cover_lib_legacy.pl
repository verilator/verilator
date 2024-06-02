#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

top_filename("t/t_cover_lib.v");

compile(
    v_flags2 => ["--coverage t/t_cover_lib_c.cpp"],
    verilator_flags2 => ["--exe -Wall -Wno-DECLFILENAME"],
    make_flags => 'CPPFLAGS_ADD=-DTEST_OBJ_DIR="' . $Self->{obj_dir} . '"',
    make_top_shell => 0,
    make_main => 0,
    );

execute(
    check_finished => 1,
    );

files_identical_sorted("$Self->{obj_dir}/coverage1.dat", "t/t_cover_lib_1.out");
files_identical_sorted("$Self->{obj_dir}/coverage2.dat", "t/t_cover_lib_2.out");
files_identical_sorted("$Self->{obj_dir}/coverage3.dat", "t/t_cover_lib_3.out");
files_identical_sorted("$Self->{obj_dir}/coverage4.dat", "t/t_cover_lib_4.out");

ok(1);
1;
