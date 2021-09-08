#!/usr/bin/env perl
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
    verilator_flags2 => ['--exe --cc --build -j 2',
                         '../' . $Self->{main_filename},
                         '-MAKEFLAGS -p --trace'],
    );

execute(
    check_finished => 1,
    );

# If '-MAKEFLAGS --trace' is not properly processed,
# the log will not contain 'CMAKE_BUILD_TYPE:STRING=Debug'.
file_grep($Self->{obj_dir} . '/vlt_compile.log', /^Vt_flag_build_make.mk:\d+: update target \'(\w+)\' due to:/, 'Vt_flag_build');

ok(1);
1;
