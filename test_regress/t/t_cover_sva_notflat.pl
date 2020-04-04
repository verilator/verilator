#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

compile(
    verilator_flags2 => ['--assert --cc --coverage-user'],
    );

execute(
    check_finished => 1,
    );

#if ($Self->{nc}) ... # See t_assert_cover.pl for NC version

# Allow old Perl format dump, or new binary dump
# Check that the hierarchy doesn't include __PVT__
# Otherwise our coverage reports would look really ugly
if ($Self->{vlt_all}) {
    file_grep($Self->{coverage_filename}, qr/(top\.t\.sub.*.cyc_eq_5)/)
}

ok(1);
1;
