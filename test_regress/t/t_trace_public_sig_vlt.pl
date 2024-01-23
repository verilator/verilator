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

my $out_filename = "$Self->{obj_dir}/V$Self->{name}.tree.json";

compile(
    make_top_shell => 0,
    make_main => 0,
    v_flags2 => ["--trace --exe $Self->{t_dir}/t_trace_public_sig.cpp $Self->{t_dir}/t_trace_public_sig.vlt --no-json-edit-nums"],
    );

if ($Self->{vlt_all}) {
    golden_filename("t/t_trace_public_sig_vlt.out");
    files_identical($out_filename, $Self->{golden_filename});
}

execute(
    check_finished => 1,
    );

golden_filename("t/t_trace_public.out");
vcd_identical("$Self->{obj_dir}/simx.vcd", $Self->{golden_filename});

# vcd_identical doesn't detect "$var a.b;" vs "$scope module a; $var b;"
file_grep("$Self->{obj_dir}/simx.vcd", qr/module glbl/i);

ok(1);
1;
