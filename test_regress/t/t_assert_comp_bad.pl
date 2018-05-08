#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

scenarios(simulator => 1);

compile(
    verilator_flags2 => ['--assert'],
    nc_flags2 => ['+assert'],
    );

execute(
    check_finished => 0,
    fails => 1,
    expect =>
'.*%Warning: t_assert_comp_bad.v:\d+: Assertion failed in top.t.genblk1: User compile-time warning
.*%Error: t_assert_comp_bad.v:\d+: Assertion failed in top.t.genblk1: User compile-time error'

    );

ok(1);
1;
