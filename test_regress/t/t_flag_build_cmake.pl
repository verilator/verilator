#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2008 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0


scenarios(simulator => 1);
top_filename("t/t_flag_make_cmake.v");

compile(  # Don't call cmake nor gmake from driver.pl
    verilator_make_cmake => 0,
    verilator_make_gmake => 0,
    verilator_flags2 => ['--exe --cc --build -j 2 --make cmake',
        '../' . $Self->{main_filename},
        ' -MAKEFLAGS "-DTEST_NAME=' . $Self->{name} . '"',
        ' -MAKEFLAGS "-DTEST_CSOURCES=' . $Self->{main_filename} . '"',
        ' -MAKEFLAGS "-DTEST_OPT_FAST=-Os"',
        ' -MAKEFLAGS "-DTEST_VERILATOR_ROOT=' . $ENV{VERILATOR_ROOT} . '"',
        ' -MAKEFLAGS "-DTEST_VERILATOR_ARGS=\"--prefix ' . $Self->{VM_PREFIX} . ' --cc \""',
        ' -MAKEFLAGS "-DTEST_VERILATOR_SOURCES=./t/t_flag_make_cmake.v"',
        ' -MAKEFLAGS "-DTEST_SYSTEMC=0"',
        ' -MAKEFLAGS "-DTEST_VERBOSE=0"',
        ' -MAKEFLAGS "-DTEST_VERILATION=1"'
        ],
    );

execute(
    check_finished => 1,
    );

ok(1);
1;
