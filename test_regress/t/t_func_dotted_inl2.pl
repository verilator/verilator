#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

top_filename("t/t_func_dotted.v");
my $out_filename = "$Self->{obj_dir}/V$Self->{name}.tree.json";

compile(
    v_flags2 => ["--no-json-edit-nums", '+define+ATTRIBUTES', '+define+USE_INLINE_MID',],
    );

if ($Self->{vlt_all}) {
    my $modp = (file_grep("$out_filename", qr/{"type":"MODULE","name":"mb","addr":"([^"]*)","loc":"e,99:[^"]*",.*"origName":"mb"/))[0];
    file_grep("$out_filename", qr/{"type":"CELL","name":"t.ma0.mb0","addr":"[^"]*","loc":"e,87:[^"]*",.*"origName":"mb0",.*"modp":"([^"]*)"/, $modp);
}

execute(
    check_finished => 1,
    );

ok(1);
1;
