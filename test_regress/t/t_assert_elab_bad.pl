#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

top_filename("t/t_assert_elab.v");
unlink("$Self->{obj_dir}/t_assert_elab_bad.log");


compile(
    v_flags2 => ['+define+FAILING_ASSERTIONS',
    $Self->{vlt_all} ? '--assert' : ($Self->{nc} ? '+assert':'')],
    fails => 1,
);

execute(
    fails => $Self->{vlt_all},
);

file_grep("$Self->{obj_dir}/vlt_compile.log",
qr/%Warning-USERFATAL: "Parameter   5 is invalid...string and constant both work"/);

ok(1);
1;
