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
my $out_filename = "$Self->{obj_dir}/V$Self->{name}.xml";

compile(
    v_flags2 => ["$Self->{t_dir}/t_func_dotted_inl0.vlt"],
    );

if ($Self->{vlt_all}) {
    file_grep("$out_filename", qr/\<module loc="e,84,.*?" name="ma" origName="ma" public="true"\>/i);
    file_grep("$out_filename", qr/\<module loc="e,99,.*?" name="mb" origName="mb" public="true"\>/i);
    file_grep("$out_filename", qr/\<module loc="e,127,.*?" name="mc" origName="mc" public="true"\>/i);
    file_grep("$out_filename", qr/\<module loc="e,127,.*?" name="mc__PB1" origName="mc" public="true"\>/i);
}

execute(
    check_finished => 1,
    );

ok(1);
1;
