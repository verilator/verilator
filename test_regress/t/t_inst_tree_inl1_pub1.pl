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
    v_flags2 => ["t/$Self->{name}.vlt",
                 $Self->wno_unopthreads_for_few_cores()]
    );

if ($Self->{vlt_all}) {
    file_grep("$out_filename", qr/\<var loc="e,70,.*?" name="u.u0.u0.z0" dtype_id="\d+" vartype="logic" origName="z0" public="true" public_flat_rd="true" public_flat_rw="true"\/\>/i);
    file_grep("$out_filename", qr/\<var loc="e,85,.*?" name="u.u0.u0.u0.u0.z1" dtype_id="\d+" vartype="logic" origName="z1" public="true" public_flat_rd="true" public_flat_rw="true"\/\>/i);
    file_grep("$out_filename", qr/\<var loc="e,83,.*?" name="u.u0.u1.u0.u0.z" dtype_id="\d+" vartype="logic" origName="z" public="true" public_flat_rd="true" public_flat_rw="true"\/\>/i);
}

execute(
    check_finished => 1,
    expect =>
'\] (%m|.*t\.ps): Clocked
',
    );

ok(1);
1;
