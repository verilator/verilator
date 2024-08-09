#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

lint(
    fails => $Self->{vlt_all},
    verilator_flags2 => ['-DTEST1'],
    expect_filename => ($Self->{golden_filename} =~ s/\.out$/_1.out/r),
    );

lint(
    fails => $Self->{vlt_all},
    verilator_flags2 => ['-DTEST2'],
    expect_filename => ($Self->{golden_filename} =~ s/\.out$/_2.out/r),
    );

ok(1);
1;
