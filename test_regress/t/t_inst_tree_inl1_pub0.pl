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
my $out_filename = "$Self->{obj_dir}/V$Self->{name}.xml";

compile(
    v_flags2 => ["$Self->{t_dir}/t_inst_tree_inl1_pub0.vlt"],
    );

if ($Self->{vlt_all}) {
    file_grep("$out_filename", qr/\<var loc="e,70,.*?" name="t.u.u0.u0.z1" dtype_id="\d+" vartype="logic" origName="z1"\/\>/i);
    file_grep("$out_filename", qr/\<var loc="e,70,.*?" name="t.u.u0.u1.z1" dtype_id="\d+" vartype="logic" origName="z1"\/\>/i);
    file_grep("$out_filename", qr/\<var loc="e,70,.*?" name="t.u.u1.u0.z0" dtype_id="\d+" vartype="logic" origName="z0"\/\>/i);
}

execute(
    check_finished => 1,
    expect =>
'\] (%m|.*t\.ps): Clocked
',
    );

ok(1);
1;
