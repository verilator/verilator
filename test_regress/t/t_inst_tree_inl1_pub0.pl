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

top_filename("t/t_inst_tree.v");
my $out_filename = "$Self->{obj_dir}/V$Self->{name}.tree.json";

compile(
    v_flags2 => ["--no-json-edit-nums", "-fno-dfg-post-inline", "$Self->{t_dir}/t_inst_tree_inl1_pub0.vlt"],
    );

if ($Self->{vlt_all}) {
    file_grep("$out_filename", qr/{"type":"VAR","name":"t.u.u0.u0.z1",.*"loc":"f,70:[^"]*",.*"origName":"z1",.*"dtypeName":"logic"/);
    file_grep("$out_filename", qr/{"type":"VAR","name":"t.u.u0.u1.z1",.*"loc":"f,70:[^"]*",.*"origName":"z1",.*"dtypeName":"logic"/);
    file_grep("$out_filename", qr/{"type":"VAR","name":"t.u.u1.u0.z0",.*"loc":"f,70:[^"]*",.*"origName":"z0",.*"dtypeName":"logic"/);
}

execute(
    check_finished => 1,
    expect =>
'\] (%m|.*t\.ps): Clocked
',
    );

ok(1);
1;
