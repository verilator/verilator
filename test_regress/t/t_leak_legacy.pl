#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

if ($Self->{vltmt} && exists $ENV{TRAVIS_DIST} &&
    $ENV{TRAVIS_DIST} eq "trusty")
{
    skip("Multithreaded test does not work under CI w/ Ubuntu Trusty");
}

scenarios(vlt_all => 1);

top_filename("t/t_leak.v");

compile(
    make_top_shell => 0,
    make_main => 0,
    verilator_flags2 => ["--exe $Self->{t_dir}/t_leak.cpp"],
    make_flags => 'CPPFLAGS_ADD=-UVL_NO_LEGACY',
    );

execute(
    check_finished => 1,
    );

ok(1);
1;
