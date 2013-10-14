#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2010 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
    make_top_shell => 0,
    make_main => 0,
    verilator_flags2 => ["-CFLAGS '-DVL_DEBUG -ggdb' --exe --no-l2name $Self->{t_dir}/t_vpi_get.cpp"],
    make_pli => 1,
    iv_flags2 => ["-g2005-sv -D USE_VPI_NOT_DPI"],
    v_flags2 => ["+define+USE_VPI_NOT_DPI"],
);

execute (
    iv_pli => 1,
    check_finished=>1
);

ok(1);
1;
