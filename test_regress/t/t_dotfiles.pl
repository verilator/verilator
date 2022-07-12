#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2021 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vltmt => 1);

# Use a top file which we are sure to be parallelizable
top_filename("t/t_gen_alw.v");

compile(
    v_flags2 => ["--debug --debugi 5"],
    threads => 2
    );

foreach my $dotname ("linkcells", "task_call", "gate_simp", "gate_opt",
        "acyc_simp", "orderg_pre", "orderg_acyc", "orderg_order", "orderg_domain",
        "ordermv_initial", "ordermv_hazards", "ordermv_contraction",
        "ordermv_transitive1", "orderg_done", "ordermv_transitive2", "schedule") {
    # Some files with identical prefix are generated multiple times during
    # verilation. Ensure that at least one of each $dotname-prefixed file is generated.
    @dotFiles = glob("$Self->{obj_dir}/*$dotname.dot");
    if (scalar @dotFiles == 0) {
        error("Found no dotfiles with pattern *$dotname.dot");
    }
    foreach my $dotFilename (@dotFiles) {
        file_grep($dotFilename, qr/digraph v3graph/);
    }
}

ok(1);
1;
