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

top_filename("t/t_dpi_var.v");
my $out_filename = "$Self->{obj_dir}/V$Self->{name}.xml";

compile(
    make_top_shell => 0,
    make_main => 0,
    verilator_flags2 => ["--exe --no-l2name $Self->{t_dir}/t_dpi_var.vlt $Self->{t_dir}/t_dpi_var.cpp"],
    );

if ($Self->{vlt_all}) {
    file_grep("$out_filename", qr/\<var loc="e,58,.*?" name="formatted" dtype_id="\d+" dir="input" vartype="string" origName="formatted" sformat="true"\/\>/i);
    file_grep("$out_filename", qr/\<var loc="e,81,.*?" name="t.sub.in" dtype_id="\d+" vartype="int" origName="in" public="true" public_flat_rd="true"\/\>/i);
    file_grep("$out_filename", qr/\<var loc="e,82,.*?" name="t.sub.fr_a" dtype_id="\d+" vartype="int" origName="fr_a" public="true" public_flat_rd="true" public_flat_rw="true"\/\>/i);
    file_grep("$out_filename", qr/\<var loc="e,83,.*?" name="t.sub.fr_b" dtype_id="\d+" vartype="int" origName="fr_b" public="true" public_flat_rd="true" public_flat_rw="true"\/\>/i);
}

execute(
    check_finished => 1,
    );

ok(1);
1;
