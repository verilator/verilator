#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2009 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

top_filename("t/t_cdc_async_bad.v");

compile(
    # --debug so we get code coverage of Cdc
    v_flags => ['--cdc --debug'],
    verilator_make_gmake => 0,
    make_top_shell => 0,
    make_main => 0,
    fails => 1,
    );

files_identical("$Self->{obj_dir}/V$Self->{name}__cdc_edges.txt", $Self->{golden_filename});

ok(1);
1;
