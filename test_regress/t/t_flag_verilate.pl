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

# We expect below that Vt_flag_verilate.mk and others are not in the build
# tree already when doing --no-verilate, so we must remove them when
# re-running the test.
clean_objs();

compile(  # Don't call cmake nor gmake from driver.pl. Nothing should be done here.
    verilator_make_cmake => 0,
    verilator_make_gmake => 0,
    verilator_flags2 => ['--exe --cc --no-verilate',
                         '../' . $Self->{main_filename}]
    );

# --no-verilate should skip verilation
if ( -e $Self->{obj_dir} . '/Vt_flag_verilate.mk' ) {
    $Self->error('Vt_flag_verilate.mk is unexpectedly created');
}

# --verilate this time
compile(  # Don't call cmake nor gmake from driver.pl. Just verilate here.
    verilator_make_cmake => 0,
    verilator_make_gmake => 0,
    verilator_flags2 => ['--exe --cc --verilate',
                         '../' . $Self->{main_filename}]
    );

# must be verilated this time
if ( ! -e $Self->{obj_dir} . '/Vt_flag_verilate.mk' ) {
    $Self->error('Vt_flag_verilate.mk does not exist');
}

# Just build, no verilation. .tree must not be saved even with --dump-tree option.
compile(  # Don't call cmake nor gmake from driver.pl. Just build here
    verilator_make_cmake => 0,
    verilator_make_gmake => 0,
    verilator_flags2 => ['--exe --cc --build --no-verilate',
                         '../' . $Self->{main_filename},
                         '--debugi 1 --dump-tree --dump-tree-addrids'],
    );

# The previous run must not verilated, only build is expected.
if (-e $Self->{obj_dir} . '/Vt_flag_verilate_990_final.tree') {
    $Self->error('Unexpectedly verilated.');
}

execute(
    check_finished => 1,
    );

ok(1);
1;
