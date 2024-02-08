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
my $out_filename = "$Self->{obj_dir}/V$Self->{name}.tree.json";

compile(
    make_top_shell => 0,
    make_main => 0,
    verilator_flags2 => ["--no-json-edit-nums", "-DATTRIBUTES --exe --no-l2name $Self->{t_dir}/t_dpi_var.cpp"],
    );

if ($Self->{vlt_all}) {
    file_grep("$out_filename", qr/{"type":"VAR","name":"formatted",.*"loc":"e,56:[^"]*",.*"origName":"formatted",.*"direction":"INPUT",.*"dtypeName":"string",.*"attrSFormat":true/);
    file_grep("$out_filename", qr/{"type":"VAR","name":"t.sub.in",.*"loc":"e,77:[^"]*",.*"origName":"in",.*"dtypeName":"int",.*"isSigUserRdPublic":true/);
    file_grep("$out_filename", qr/{"type":"VAR","name":"t.sub.fr_a",.*"loc":"e,78:[^"]*",.*"origName":"fr_a",.*"dtypeName":"int",.*"isSigUserRdPublic":true,.*"isSigUserRWPublic":true/);
    file_grep("$out_filename", qr/{"type":"VAR","name":"t.sub.fr_b",.*"loc":"e,79:[^"]*",.*"origName":"fr_b",.*"dtypeName":"int",.*"isSigUserRdPublic":true,.*"isSigUserRWPublic":true/);
}

execute(
    check_finished => 1,
    );

ok(1);
1;
