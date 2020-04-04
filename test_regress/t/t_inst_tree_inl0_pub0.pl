#!/usr/bin/perl
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
    v_flags2 => ["$Self->{t_dir}/$Self->{name}.vlt"],
);

if ($Self->{vlt_all}) {
    file_grep("$out_filename", qr/\<module fl="e56" loc=".*?" name="l1" origName="l1"\>/i);
    file_grep("$out_filename", qr/\<module fl="e62" loc=".*?" name="l2" origName="l2"\>/i);
    file_grep("$out_filename", qr/\<module fl="e69" loc=".*?" name="l3" origName="l3"\>/i);
    file_grep("$out_filename", qr/\<module fl="e76" loc=".*?" name="l4" origName="l4"\>/i);
    file_grep("$out_filename", qr/\<module fl="e83" loc=".*?" name="l5__P2" origName="l5"\>/i);
    file_grep("$out_filename", qr/\<module fl="e83" loc=".*?" name="l5__P1" origName="l5"\>/i);
}

execute(
    check_finished => 1,
    expect =>
'\] (%m|.*t\.ps): Clocked
',
    );

ok(1);
1;
