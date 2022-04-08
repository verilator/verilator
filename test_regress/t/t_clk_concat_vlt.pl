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

top_filename("t/t_clk_concat.v");
my $out_filename = "$Self->{obj_dir}/V$Self->{name}.xml";

compile(
    verilator_flags2 => ["t/t_clk_concat.vlt"],
    );

if ($Self->{vlt_all}) {
    file_grep("$out_filename", qr/\<var loc="e,78,.*?" name="clk0" .*dir="input" .*vartype="logic" origName="clk0" clocker="true" public="true"\/\>/i);
    file_grep("$out_filename", qr/\<var loc="e,79,.*?" name="clk1" .*dir="input" .*vartype="logic" origName="clk1" clocker="true" public="true"\/\>/i);
    file_grep("$out_filename", qr/\<var loc="e,80,.*?" name="clk2" .*dir="input" .*vartype="logic" origName="clk2" clocker="true" public="true"\/\>/i);
    file_grep("$out_filename", qr/\<var loc="e,82,.*?" name="data_in" .*dir="input" .*vartype="logic" origName="data_in" clocker="false" public="true"\/\>/i);
}

execute(
    check_finished => 1,
    );

ok(1);
1;
