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

top_filename("t/t_unopt_combo.v");
my $out_filename = "$Self->{obj_dir}/V$Self->{name}.tree.json";

compile(
    verilator_flags2 => ["--no-json-edit-nums +define+ISOLATE --stats"],
    );

if ($Self->{vlt_all}) {
    file_grep($Self->{stats}, qr/Optimizations, isolate_assignments blocks\s+3/i);
    file_grep("$out_filename", qr/{"type":"VAR","name":"t.b",.*"loc":"e,23:[^"]*",.*"origName":"b",.*"attrIsolateAssign":true,.*"dtypeName":"logic"/);
    file_grep("$out_filename", qr/{"type":"VAR","name":"__Vfunc_t.file.get_31_16__0__Vfuncout",.*"loc":"e,99:[^"]*",.*"origName":"__Vfunc_t__DOT__file__DOT__get_31_16__0__Vfuncout",.*"attrIsolateAssign":true,.*"dtypeName":"logic"/);
    file_grep("$out_filename", qr/{"type":"VAR","name":"__Vfunc_t.file.get_31_16__0__t_crc",.*"loc":"e,100:[^"]*",.*"origName":"__Vfunc_t__DOT__file__DOT__get_31_16__0__t_crc",.*"attrIsolateAssign":true,.*"dtypeName":"logic"/);
    file_grep("$out_filename", qr/{"type":"VAR","name":"__Vtask_t.file.set_b_d__1__t_crc",.*"loc":"e,112:[^"]*",.*"origName":"__Vtask_t__DOT__file__DOT__set_b_d__1__t_crc",.*"attrIsolateAssign":true,.*"dtypeName":"logic"/);
    file_grep("$out_filename", qr/{"type":"VAR","name":"__Vtask_t.file.set_b_d__1__t_c",.*"loc":"e,113:[^"]*",.*"origName":"__Vtask_t__DOT__file__DOT__set_b_d__1__t_c",.*"attrIsolateAssign":true,.*"dtypeName":"logic"/);
}

execute(
    );

ok(1);
1;
