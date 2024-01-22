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
    v_flags2 => ["--no-json-edit-nums", "$Self->{t_dir}/t_func_dotted_inl0.vlt"],
    );

if ($Self->{vlt_all}) {
    file_grep("$out_filename", qr/{"type":"MODULE","name":"ma","addr":"[^"]*","loc":"f,84:[^"]*","origName":"ma","level":3,"modPublic":true,"inLibrary":false,"dead":false,"recursiveClone":false,"recursive":false,"timeunit":"1ps","inlinesp": \[\],/);
    file_grep("$out_filename", qr/{"type":"MODULE","name":"mb","addr":"[^"]*","loc":"f,99:[^"]*","origName":"mb","level":4,"modPublic":true,"inLibrary":false,"dead":false,"recursiveClone":false,"recursive":false,"timeunit":"1ps","inlinesp": \[\],/);
    file_grep("$out_filename", qr/{"type":"MODULE","name":"mc","addr":"[^"]*","loc":"f,127:[^"]*","origName":"mc","level":5,"modPublic":true,"inLibrary":false,"dead":false,"recursiveClone":false,"recursive":false,"timeunit":"1ps","inlinesp": \[\],/);
    file_grep("$out_filename", qr/{"type":"MODULE","name":"mc__PB1","addr":"[^"]*","loc":"f,127:[^"]*","origName":"mc","level":5,"modPublic":true,"inLibrary":false,"dead":false,"recursiveClone":false,"recursive":false,"timeunit":"1ps","inlinesp": \[\],/);
}

execute(
    check_finished => 1,
    );

ok(1);
1;
