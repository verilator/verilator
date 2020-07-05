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

top_filename("t/t_sys_readmem.v");

# Use random reset to ensure we're fully initializing arrays before
# $writememh, to avoid miscompares with X's on 4-state simulators.
$Self->{verilated_randReset} = 2;  # 2 == truly random

compile(v_flags2 => [
            "+define+WRITEMEM_READ_BACK=1",
            "+define+WRITEMEM_BIN=1",
            "+define+OUT_TMP1=\\\"$Self->{obj_dir}/tmp1.mem\\\"",
            "+define+OUT_TMP2=\\\"$Self->{obj_dir}/tmp2.mem\\\"",
            "+define+OUT_TMP3=\\\"$Self->{obj_dir}/tmp3.mem\\\"",
            "+define+OUT_TMP4=\\\"$Self->{obj_dir}/tmp4.mem\\\"",
            "+define+OUT_TMP5=\\\"$Self->{obj_dir}/tmp5.mem\\\"",
        ]);

execute(
    check_finished => 1,
    );

for (my $i = 1; $i <= 5; $i++) {
    my $gold = "$Self->{t_dir}/t_sys_writemem_b.gold${i}.mem";
    my $out = "$Self->{obj_dir}/tmp${i}.mem";
    files_identical($out, $gold);
}

ok(1);
1;
