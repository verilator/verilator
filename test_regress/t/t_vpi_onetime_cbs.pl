#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2020 by Wilson Snyder and Marlon James. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

$Self->{sanitize} = 0;  # Test neads cleanup to reclaim all callbacks

compile(
    make_top_shell => 0,
    make_main => 0,
    make_pli => 1,
    verilator_flags2 => ["--exe --vpi $Self->{t_dir}/$Self->{name}.cpp"],
    iv_flags2 => ["-g2005-sv -D USE_VPI_NOT_DPI -DIVERILOG"],
    v_flags2 => ["+define+USE_VPI_NOT_DPI"],
    );

execute(
    check_finished => 1,
    use_libvpi => 1,
    );

ok(1);
1;
