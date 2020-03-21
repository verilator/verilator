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

top_filename("t/t_unopt_combo.v");
my $out_filename = "$Self->{obj_dir}/V$Self->{name}.xml";

compile(
    verilator_flags2 => ["--stats $Self->{t_dir}/t_unopt_combo_isolate.vlt"],
    );

if ($Self->{vlt_all}) {
    file_grep($Self->{stats}, qr/Optimizations, isolate_assignments blocks\s+5/i);
    file_grep("$out_filename", qr/\<var fl="e23" loc=".*?" name="t.b" dtype_id="4" vartype="logic" origName="b" isolate_assignments="true"\/\>/i);
    file_grep("$out_filename", qr/\<var fl="e104" loc=".*?" name="__Vfunc_t.file.get_31_16__0__Vfuncout" dtype_id="5" vartype="logic" origName="__Vfunc_t__DOT__file__DOT__get_31_16__0__Vfuncout" isolate_assignments="true"\/\>/i);
    file_grep("$out_filename", qr/\<var fl="e105" loc=".*?" name="__Vfunc_t.file.get_31_16__0__t_crc" dtype_id="4" vartype="logic" origName="__Vfunc_t__DOT__file__DOT__get_31_16__0__t_crc" isolate_assignments="true"\/\>/i);
    file_grep("$out_filename", qr/\<var fl="e115" loc=".*?" name="__Vtask_t.file.set_b_d__1__t_crc" dtype_id="4" vartype="logic" origName="__Vtask_t__DOT__file__DOT__set_b_d__1__t_crc" isolate_assignments="true"\/\>/i);
    file_grep("$out_filename", qr/\<var fl="e116" loc=".*?" name="__Vtask_t.file.set_b_d__1__t_c" dtype_id="4" vartype="logic" origName="__Vtask_t__DOT__file__DOT__set_b_d__1__t_c" isolate_assignments="true"\/\>/i);
}

execute(
    );

ok(1);
1;
