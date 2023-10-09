#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2008 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt => 1);

lint(
    # See also t/t_lint_warn_incfile1_bad
    # See also t/t_lint_warn_incfile2_bad
    verilator_flags2 => ["--no-std t/t_vlt_warn_file_bad.vlt"],
    fails => 1,
    expect_filename => $Self->{golden_filename},
    );

ok(1);
1;
