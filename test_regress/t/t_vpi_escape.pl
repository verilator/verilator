#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2023 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

pli_filename("t_vpi_escape.cpp");
compile(
    make_top_shell => 0,
    make_main => 0,
    make_pli => 1,
    sim_time => 100,
    iv_flags2 => ["-g2005-sv -D USE_VPI_NOT_DPI -DWAVES"],
    v_flags2 => ["+define+USE_VPI_NOT_DPI"],
    verilator_flags2 => ["--exe --vpi --no-l2name --public-flat-rw $Self->{t_dir}/$Self->{name}.cpp"],
    );

execute(
    # run_env => "VPI_TRACE=" . Cwd::getcwd() . "/$Self->{obj_dir}/$Self->{name}_vpi.log",
    # run_env => "VPI_TRACE=/tmp/$Self->{name}_vpi.log",
    use_libvpi => 1,
    check_finished => 1,
    );

ok(1);
1;
