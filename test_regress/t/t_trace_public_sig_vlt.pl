#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt_all => 1);

top_filename("t/t_trace_public.v");
golden_filename("t/t_trace_public.out");

my $out_filename = "$Self->{obj_dir}/V$Self->{name}.xml";

compile(
    make_top_shell => 0,
    make_main => 0,
    v_flags2 => ["--trace --exe $Self->{t_dir}/t_trace_public_sig.cpp $Self->{t_dir}/t_trace_public_sig.vlt"],
    );

if ($Self->{vlt_all}) {
    file_grep("$out_filename", qr/\<var loc="e,47,.*?" name="GSR" dtype_id="1" vartype="logic" origName="GSR" public="true" public_flat_rd="true" public_flat_rw="true"\/\>/i);
}

execute(
    check_finished => 1,
    );

vcd_identical("$Self->{obj_dir}/simx.vcd", $Self->{golden_filename});

# vcd_identical doesn't detect "$var a.b;" vs "$scope module a; $var b;"
file_grep("$Self->{obj_dir}/simx.vcd", qr/module glbl/i);

ok(1);
1;
