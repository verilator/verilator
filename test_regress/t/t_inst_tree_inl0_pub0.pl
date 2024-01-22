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
    v_flags2 => ["--no-json-edit-nums", "$Self->{t_dir}/$Self->{name}.vlt"],
);

if ($Self->{vlt_all}) {
    file_grep("$out_filename", qr/{"type":"MODULE","name":"l1","addr":"[^"]*","loc":"f,56:[^"]*","origName":"l1","level":3,"modPublic":false,"inLibrary":false,"dead":false,"recursiveClone":false,"recursive":false,"timeunit":"1ps","inlinesp": \[\],/);
    file_grep("$out_filename", qr/{"type":"MODULE","name":"l2","addr":"[^"]*","loc":"f,62:[^"]*","origName":"l2","level":4,"modPublic":false,"inLibrary":false,"dead":false,"recursiveClone":false,"recursive":false,"timeunit":"1ps","inlinesp": \[\],/);
    file_grep("$out_filename", qr/{"type":"MODULE","name":"l3","addr":"[^"]*","loc":"f,69:[^"]*","origName":"l3","level":5,"modPublic":false,"inLibrary":false,"dead":false,"recursiveClone":false,"recursive":false,"timeunit":"1ps","inlinesp": \[\],/);
    file_grep("$out_filename", qr/{"type":"MODULE","name":"l4","addr":"[^"]*","loc":"f,76:[^"]*","origName":"l4","level":6,"modPublic":false,"inLibrary":false,"dead":false,"recursiveClone":false,"recursive":false,"timeunit":"1ps","inlinesp": \[\],/);
    file_grep("$out_filename", qr/{"type":"MODULE","name":"l5__P1","addr":"[^"]*","loc":"f,83:[^"]*","origName":"l5","level":7,"modPublic":false,"inLibrary":false,"dead":false,"recursiveClone":false,"recursive":false,"timeunit":"1ps","inlinesp": \[\],/);
    file_grep("$out_filename", qr/{"type":"MODULE","name":"l5__P2","addr":"[^"]*","loc":"f,83:[^"]*","origName":"l5","level":7,"modPublic":false,"inLibrary":false,"dead":false,"recursiveClone":false,"recursive":false,"timeunit":"1ps","inlinesp": \[\],/);
}

execute(
    check_finished => 1,
    expect =>
'\] (%m|.*t\.ps): Clocked
',
    );

ok(1);
1;
