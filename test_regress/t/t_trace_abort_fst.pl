#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2020 by Geza Lore. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt_all => 1);

top_filename("t/t_trace_abort.v");

compile(
    verilator_flags2 => ['--cc --trace-fst'],
    );

execute(
    fails => 1,
    );

fst_identical("$Self->{obj_dir}/simx.fst", $Self->{golden_filename});

ok(1);
1;
