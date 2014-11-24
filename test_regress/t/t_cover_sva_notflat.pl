#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

compile (
	 verilator_flags2 => ['--assert --cc --coverage-user'],
	 );

execute (
	 check_finished=>1,
	 );

#if ($Self->{nc}) ... # See t_assert_cover.pl for NC version

# Allow old Perl format dump, or new binary dump
# Check that the hierarchy doesn't include __PVT__
# Otherwise our coverage reports would look really ugly
file_grep ($Self->{coverage_filename}, qr/(top\.v\.sub.*.cyc_eq_5)/)
    if $Self->{vlt};

ok(1);
1;
