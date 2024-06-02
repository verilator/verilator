#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(vlt_all => 1);

compile(
    );

execute(
    all_run_flags => ["+verilator+bad+flag+testing"],
    fails => 1,
    expect_filename => "t/" . $Self->{name} . "_a.out",
    );

execute(
    all_run_flags => ["+verilator+rand+reset+-1"],
    fails => 1,
    expect_filename => "t/" . $Self->{name} . "_b.out",
    );

execute(
    all_run_flags => ["+verilator+rand+reset+3"],
    fails => 1,
    expect_filename => "t/" . $Self->{name} . "_c.out",
    );

execute(
    all_run_flags => ["+verilator+prof+exec+window+0"],
    fails => 1,
    expect_filename => "t/" . $Self->{name} . "_d.out",
    );

execute(
    all_run_flags => ["+verilator+prof+exec+window+1000000000000000000000000"],
    fails => 1,
    expect_filename => "t/" . $Self->{name} . "_e.out",
    );

ok(1);

1;
