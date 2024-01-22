#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2019 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

top_filename("t/t_func_dotted.v");
my $out_filename = "$Self->{obj_dir}/V$Self->{name}.tree.json";

compile(
    v_flags2 => ["--no-json-edit-nums", "t/t_func_dotted_inl2.vlt",],
    );

if ($Self->{vlt_all}) {
    file_grep("$out_filename", qr/{"type":"CELL","name":"t.ma0.mb0","addr":"[^"]*","loc":"f,87:[^"]*","origName":"mb0","recursive":false,"modp":"[^"]*","pinsp": \[\],"paramsp": \[\],"rangep": \[\],"intfRefsp": \[\]/);
    file_grep("$out_filename", qr/{"type":"MODULE","name":"mb","addr":"[^"]*","loc":"f,99:[^"]*","origName":"mb","level":4,"modPublic":false,"inLibrary":false,"dead":false,"recursiveClone":false,"recursive":false,"timeunit":"1ps","inlinesp": \[\],/);
}

execute(
    check_finished => 1,
    );

ok(1);
1;
