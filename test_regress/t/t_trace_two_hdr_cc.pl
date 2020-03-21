#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2020 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

# Test tracing with two models instanced
scenarios(vlt_all => 1);

top_filename("t_trace_two_a.v");

compile(
    make_main => 0,
    verilator_make_gmake => 0,
    top_filename => 't_trace_two_b.v',
    VM_PREFIX => 'Vt_trace_two_b',
    verilator_flags2 => ['-trace'],
    );

compile(
    make_main => 0,
    top_filename => 't_trace_two_a.v',
    make_flags => 'CPPFLAGS_ADD=-DTEST_HDR_TRACE=1',
    verilator_flags2 => ['-exe', '-trace', "$Self->{t_dir}/t_trace_two_cc.cpp"],
    );

execute(
    check_finished => 1,
    );

if ($Self->{vlt_all}) {
    file_grep("$Self->{obj_dir}/simx.vcd", qr/\$enddefinitions/x);
    vcd_identical("$Self->{obj_dir}/simx.vcd", $Self->{golden_filename});
}

ok(1);
1;
