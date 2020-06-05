#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(linter => 1);

lint(
    fails => 1,
    verilator_flags2 => ['--stats'],
    # When issue-2407 resolved, decomment and update golden file
    #expect_filename => $Self->{golden_filename},
);

# When issue-2407 resolved, remove
files_identical_sorted("$Self->{obj_dir}/vlt_compile.log", $Self->{golden_filename}, 1);

ok(1);
1;
