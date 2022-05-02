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

my $out_filename = "$Self->{obj_dir}/V$Self->{name}.xml";

compile(
    verilator_flags2 => ["--stats"],
    );

if ($Self->{vlt_all}) {
    file_grep("$out_filename", qr/\<var loc="\w+,44,.*?" name="t.f0.clock_gate.clken_latched" dtype_id="\d+" vartype="logic" origName="clken_latched" latched="true"\/\>/i);
    file_grep($Self->{stats}, qr/Optimizations, Gate sigs deduped\s+(\d+)/i, 4);
}

ok(1);
1;
